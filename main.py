from __future__ import annotations
from z3 import *
from capstone import *
from typing import Callable, Optional, Tuple, List
from dataclasses import dataclass
from minidump.minidumpfile import MinidumpFile
from minidump.minidumpreader import MinidumpFileReader
from IPython import embed
from collections import defaultdict
import pypcode
import itertools
import enum
import time

BITS_PER_BYTE = 8
DUMP_FILE_PATH = '/home/sho/Documents/freelance/getcode/GetCode.DMP'
VIRT_ENTRY_POINT_ADDR = 0x00d6bd08
X86_MAX_INSN_LEN = 15
EXAMPLE_PUSHED_MAGIC = 0x6bfd0737
MEM_VAR_NAME_PREFIX = 'orig_mem'
EMPTY_SOLVER = Solver()

DUMP_FILE = MinidumpFile.parse(DUMP_FILE_PATH)
DUMP_READER = DUMP_FILE.get_reader()

@dataclass(frozen=True)
class VarnodeAddr:
    space_name: str
    off: int

@dataclass(frozen=True)
class MemAccess:
    addr: BitVecRef
    size_in_bytes: int

def bits_to_bytes_safe(bits_amount: int) -> int:
    assert bits_amount % BITS_PER_BYTE == 0
    return bits_amount // BITS_PER_BYTE

class UnreachableError:
    pass

def unreachable():
    raise UnreachableError()

@dataclass
class Successor:
    state: State
    next_insn_addr: BitVecRef
    is_branch: bool
    is_return: bool
    is_indirect_branch: bool

@dataclass
class StateDiff:
    varnode_addrs: List[VarnodeAddr]
    mem_addrs: List[BitVecRef]
    constraints: List[BoolRef]

class ResolvedCondition(enum.Enum):
    FALSE = 0
    TRUE = 1
    UNKNOWN = 2

@dataclass
class TrackedMemWrite:
    addr: BitVecRef
    value: BitVecRef

class TrackedMemWriteAggregator:
    def __init__(self):
        self.addr = None
        self.single_byte_values = []

    def track_write(self, addr: BitVecRef, value: BitVecRef):
        if self.addr is None:
            self.addr = addr
            self.single_byte_values.append(value)
            return
        expected_addr = self.addr + len(self.single_byte_values)
        assert are_concretely_equal(EMPTY_SOLVER, addr, expected_addr)
        self.single_byte_values = [value] + self.single_byte_values

    @property
    def size_in_bytes(self) -> int:
        return len(self.single_byte_values)

    @property
    def value(self) -> Optional[BitVecRef]:
        if self.addr is None:
            return None
        single_byte_values = simplify_concat_extract(EMPTY_SOLVER, self.single_byte_values)

        if len(single_byte_values) == 1:
            return simplify(single_byte_values[0])
        else:
            return simplify(Concat(single_byte_values))

    def __repr__(self) -> str:
        return 'TrackedMemWriteAggregator(addr={}, value={})'.format(self.addr, self.value)

    def __str__(self) -> str:
        return repr(self)

def get_insn_disassembly(address: int) -> str:
    insn_bytes = DUMP_READER.read(address, X86_MAX_INSN_LEN)
    cs = Cs(CS_ARCH_X86, CS_MODE_64)
    insn_addr, insn_size, insn_mnemonic, insn_op_str = next(cs.disasm_lite(insn_bytes, address))
    return '{} {} {}'.format(hex(address), insn_mnemonic, insn_op_str)

def is_extract(expr: BitVecRef) -> bool:
    return is_app_of(expr, Z3_OP_EXTRACT)

def copy_solver(solver: Solver) -> Solver:
    return solver.translate(solver.ctx)

def are_concretely_equal(solver: Solver, a: BitVecRef, b: BitVecRef) -> bool:
    if a.size() != b.size():
        return False
    return solver.check(a != b) == unsat

def is_concretely_unsigned_lower_or_eq_to(solver: Solver, a: BitVecRef, b: BitVecRef) -> bool:
    return solver.check(UGT(a, b)) == unsat

def are_constraints_concretely_equal(solver: Solver, a: BoolRef, b: BoolRef) -> bool:
    return solver.check(a != b) == unsat

def simplify_concat_extract(solver: Solver, single_byte_values: List[BitVecRef]) -> List[BitVecRef]:
    if len(single_byte_values) == 1:
        return single_byte_values
    for i in range(len(single_byte_values) - 1):
        [byte_val_a, byte_val_b] = single_byte_values[i:i+2]
        if not is_extract(byte_val_a) or not is_extract(byte_val_b):
            continue
        [a_high, a_low] = byte_val_a.params()
        [b_high, b_low] = byte_val_b.params()
        if b_high + 1 != a_low:
            # not consequtive
            continue
        if not are_concretely_equal(solver, byte_val_a.arg(0), byte_val_b.arg(0)):
            # not equal, can't merge
            continue
        combined = Extract(a_high, b_low, byte_val_a.arg(0))
        new_values =single_byte_values[:i] + [combined] + single_byte_values[i+2:]
        return simplify_concat_extract(solver, new_values)
    return single_byte_values

def try_extract_cond_from_int_cond(int_cond: BitVecRef) -> Optional[BoolRef]:
    concrete_int_cond = try_expr_to_concrete(int_cond)
    if concrete_int_cond != None:
        if concrete_int_cond != 0:
            return BoolVal(True)
        else:
            return BoolVal(False)
    if int_cond.decl().name().lower() != 'if':
        return None
    if int_cond.num_args() != 3:
        return None

    if (
        are_concretely_equal(
            EMPTY_SOLVER, int_cond.arg(1), BitVecVal(1, 8)
        ) and are_concretely_equal(
            EMPTY_SOLVER, int_cond.arg(2), BitVecVal(0, 8)
        )
    ):
        # the condition is not negated
        cond = int_cond.arg(0)
        assert isinstance(cond, BoolRef)
        return cond

    elif (
        are_concretely_equal(
            EMPTY_SOLVER, int_cond.arg(1), BitVecVal(0, 8)
        ) and are_concretely_equal(
            EMPTY_SOLVER, int_cond.arg(2), BitVecVal(1, 8)
        )
    ):
        # the condition is negated
        cond = int_cond.arg(0)
        assert isinstance(cond, BoolRef)
        return Not(cond)
    return None

def build_int_cond_from_cond(cond: BoolRef) -> BitVecRef:
    cond = simplify(cond)
    return If(cond, BitVecVal(1, 8), BitVecVal(0, 8))

class State:
    def __init__(self):
        self.ctx = pypcode.Context("x86:LE:64:default")
        self.varnode_values = {}
        self.mem_values = {}
        self.mem_var_addresses = []
        self.constraints = []
        self.solver = Solver()
        self.read_mem_single_byte_fallback = None
        self.mem_writes = None

    def copy(self):
        new_state = State()
        new_state.varnode_values = self.varnode_values.copy()
        new_state.mem_values = self.mem_values.copy()
        new_state.mem_var_addresses = self.mem_var_addresses.copy()
        new_state.constraints = self.constraints.copy()
        new_state.solver = copy_solver(self.solver)
        new_state.read_mem_single_byte_fallback = self.read_mem_single_byte_fallback
        if self.mem_writes != None:
            new_state.mem_writes = self.mem_writes.copy()
        return new_state

    def enable_mem_write_tracking(self):
        if self.mem_writes == None:
            self.reset_mem_write_tracking()

    def reset_mem_write_tracking(self):
        self.mem_writes = defaultdict(TrackedMemWriteAggregator)

    def has_constraint(self, constraint: BoolRef) -> bool:
        for cur_constraint in self.constraints:
            if are_constraints_concretely_equal(EMPTY_SOLVER, constraint, cur_constraint):
                return True
        return False

    def shared_constraints_with(self, other: State) -> List[BoolRef]:
        res = []
        for self_constraint in self.constraints:
            if other.has_constraint(self_constraint):
                res.append(self_constraint)
        return res

    def diff(self, other: State) -> StateDiff:
        diff_varnode_addrs = []
        diff_mem_addrs = []
        diff_constraints = []
        for k in self.varnode_values.keys():
            if k not in other.varnode_values or not are_concretely_equal(EMPTY_SOLVER, self.varnode_values[k], other.varnode_values[k]):
                diff_varnode_addrs.append(k)
        for k in other.varnode_values.keys():
            if k in self.varnode_values:
                # already considered this key, because we considered all keys in `self.varnode_values`.
                continue
            diff_varnode_addrs.append(k)

        for k in self.mem_values.keys():
            if k not in other.mem_values or not are_concretely_equal(EMPTY_SOLVER, self.mem_values[k], other.mem_values[k]):
                diff_mem_addrs.append(k)
        for k in other.mem_values.keys():
            if k in self.mem_values:
                # already considered this key, because we considered all keys in `self.mem_values`.
                continue
            diff_mem_addrs.append(k)
        for c in self.constraints:
            if not other.has_constraint(c):
                diff_constraints.append(c)
        for c in other.constraints:
            if not self.has_constraint(c):
                diff_constraints.append(c)
        return StateDiff(diff_varnode_addrs, diff_mem_addrs, diff_constraints)

    def is_same_as(self, other: State) -> bool:
        """
        checks if this state is the same as the given other state.
        this means that all varnode and memory values are the same.
        the states are considered the same even if they differ in their constraints.
        """
        if not self.varnode_values.keys() == other.varnode_values.keys():
            return False

        for k in self.varnode_values.keys():
            if not are_concretely_equal(EMPTY_SOLVER, self.varnode_values[k], other.varnode_values[k]):
                return False

        if len(self.mem_var_addresses) != len(other.mem_var_addresses):
            return False
        for self_addr, other_addr in zip(self.mem_var_addresses, other.mem_var_addresses):
            if not are_concretely_equal(EMPTY_SOLVER, self_addr, other_addr):
                return False

        if len(self.mem_values) != len(other.mem_values):
            return False

        for mem_value_addr in self.mem_values.keys():
            if mem_value_addr not in other.mem_values:
                return False
            if not are_concretely_equal(EMPTY_SOLVER, self.mem_values[mem_value_addr], other.mem_values[mem_value_addr]):
                return False

        for mem_value_addr in other.mem_values.keys():
            if mem_value_addr not in self.mem_values:
                return False
            if not are_concretely_equal(EMPTY_SOLVER, self.mem_values[mem_value_addr], other.mem_values[mem_value_addr]):
                return False
        return True
            

    def set_read_mem_single_byte_fallback(self, fn: Callable[[int], Optional[int]]):
        self.read_mem_single_byte_fallback = fn

    def get_reg_name_containting_addr(self, addr: VarnodeAddr) -> Optional[str]:
        for reg_name, reg_varnode in self.ctx.registers.items():
            if reg_varnode.space.name != addr.space_name:
                continue
            reg_start_off = reg_varnode.offset
            reg_end_off = reg_start_off + reg_varnode.size
            if addr.off >= reg_start_off and addr.off < reg_end_off:
                return reg_name

    def symbolize_register(self, reg_name: str):
        reg_varnode = self.ctx.registers[reg_name]
        var_name = 'orig_{}'.format(reg_name.lower())
        var = BitVec(var_name, reg_varnode.size * BITS_PER_BYTE)
        self.write_varnode(reg_varnode, var)

    def read_varnode_single_byte(self, addr: VarnodeAddr) -> BitVecRef:
        # this is important since simplification makes the expression deterministic.
        if addr in self.varnode_values:
            return self.varnode_values[addr]
        else:
            # value is uninitialized, need to initialize it with a variable
            reg_name = self.get_reg_name_containting_addr(addr)
            if reg_name != None:
                # value is a register, initialize the register and then read the specific byte
                self.symbolize_register(reg_name)
                return self.varnode_values[addr]
            else:
                # value is not a register, create a variable for this specific byte
                var_name = 'orig_{}_{}'.format(addr.space.name, addr.off)
                var = BitVec(var_name, 8)
                self.write_varnode_single_byte(addr, var)
                return var

    def read_non_const_multibyte_varnode(self, varnode: pypcode.Varnode) -> BitVecRef:
        single_byte_values = []
        for rel_byte_off in range(varnode.size):
            addr = VarnodeAddr(varnode.space.name, varnode.offset + rel_byte_off)
            single_byte_values.append(self.read_varnode_single_byte(addr))
        single_byte_values.reverse()
        single_byte_values = simplify_concat_extract(self.solver, single_byte_values)
        if len(single_byte_values) == 1:
            return single_byte_values[0]
        else:
            return Concat(single_byte_values)

    def read_non_const_varnode(self, varnode: pypcode.Varnode) -> BitVecRef:
        if varnode.size == 1:
            # single byte
            addr = VarnodeAddr(varnode.space.name, varnode.offset)
            return self.read_varnode_single_byte(addr)
        else:
            # multi byte
            return self.read_non_const_multibyte_varnode(varnode)

    def read_varnode(self, varnode: pypcode.Varnode) -> BitVecRef:
        if varnode.space.name == 'const':
            return BitVecVal(varnode.offset, varnode.size * BITS_PER_BYTE)
        else:
            return simplify(self.read_non_const_varnode(varnode))

    def read_mem_single_byte_uninit(self, addr: BitVecRef) -> BitVecRef:
        # if the address is concrete, try using the fallback function
        concrete_addr = try_expr_to_concrete(addr)
        if concrete_addr != None and self.read_mem_single_byte_fallback != None:
            value = (self.read_mem_single_byte_fallback)(concrete_addr)
            if value != None:
                return BitVecVal(value, 8)

        # value is uninitialized, need to initialize it with a variable
        mem_var_id = len(self.mem_var_addresses)
        var_name = '{}_{}'.format(MEM_VAR_NAME_PREFIX, mem_var_id)
        self.mem_var_addresses.append(addr)
        return BitVec(var_name, 8)

    def read_mem_single_byte(self, addr: BitVecRef) -> BitVecRef:
        # simplify the address before trying to access the dictionary.
        # this is important since simplification makes the expression deterministic.
        addr = simplify(addr)
        if addr in self.mem_values:
            return self.mem_values[addr]
        else:
            value = self.read_mem_single_byte_uninit(addr)
            self.write_mem_single_byte(addr, value, None)
            return value

    def read_multibyte_mem(self, access: MemAccess) -> BitVecRef:
        single_byte_values = []
        for rel_byte_off in range(access.size_in_bytes):
            addr = access.addr + rel_byte_off
            single_byte_values.append(self.read_mem_single_byte(addr))
        single_byte_values.reverse()
        single_byte_values = simplify_concat_extract(self.solver, single_byte_values)
        if len(single_byte_values) == 1:
            return single_byte_values[0]
        else:
            return Concat(single_byte_values)

    def read_mem(self, access: MemAccess) -> BitVecRef:
        if access.size_in_bytes == 1:
            # single byte
            return self.read_mem_single_byte(access.addr)
        else:
            # multi byte
            return simplify(self.read_multibyte_mem(access))

    def was_entire_mem_written_to(self, access: MemAccess) -> BitVecRef:
        single_byte_values = []
        for rel_byte_off in range(access.size_in_bytes):
            addr = access.addr + rel_byte_off
            # simplify the address before trying to access the dictionary.
            # this is important since simplification makes the expression deterministic.
            addr = simplify(addr)
            if addr not in self.mem_values:
                return False
        return True

    def write_varnode_single_byte(self, addr: VarnodeAddr, value: BitVecRef):
        assert value.size() == 8
        self.varnode_values[addr] = value
        
    def write_varnode(self, varnode: pypcode.Varnode, value: BitVecRef):
        assert value.size() == varnode.size * BITS_PER_BYTE
        value = simplify(value)
        for rel_byte_off in range(varnode.size):
            addr = VarnodeAddr(varnode.space.name, varnode.offset + rel_byte_off)
            start_bit_offset = rel_byte_off * BITS_PER_BYTE
            extracted_byte = Extract(start_bit_offset + 7, start_bit_offset, value)
            self.write_varnode_single_byte(addr, extracted_byte)

    def write_mem_single_byte(self, addr: BitVecRef, value: BitVecRef, track_insn_addr: Optional[int]):
        assert value.size() == 8

        # simplify the address before trying to access the dictionary.
        # this is important since simplification makes the expression deterministic.
        addr = simplify(addr)

        self.mem_values[addr] = value

        if track_insn_addr != None and self.mem_writes != None:
            self.mem_writes[track_insn_addr].track_write(addr, value)
        
    def write_mem(self, access: MemAccess, value: BitVecRef, track_insn_addr: Optional[int]):
        assert value.size() == access.size_in_bytes * BITS_PER_BYTE
        value = simplify(value)
        for rel_byte_off in range(access.size_in_bytes):
            addr = access.addr + rel_byte_off
            start_bit_offset = rel_byte_off * BITS_PER_BYTE
            extracted_byte = Extract(start_bit_offset + 7, start_bit_offset, value)
            self.write_mem_single_byte(addr, extracted_byte, track_insn_addr)

    def exec_binop(self, op: pypcode.PcodeOp, binary_operation: Callable[[BitVecRef, BitVecRef], BitVecRef]):
        assert len(op.inputs) == 2
        input_a = self.read_varnode(op.inputs[0])
        input_b = self.read_varnode(op.inputs[1])
        result = binary_operation(input_a, input_b)
        self.write_varnode(op.output, result)

    def exec_bool_binop(self,
        op: pypcode.PcodeOp,
        binary_operation: Callable[[BoolRef, BoolRef], BoolRef],
        int_binary_operation: Callable[[BitVecRef, BitVecRef], BitVecRef]
    ):
        assert len(op.inputs) == 2
        input_a = self.read_varnode(op.inputs[0])
        input_b = self.read_varnode(op.inputs[1])
        cond_a = try_extract_cond_from_int_cond(input_a)
        cond_b = try_extract_cond_from_int_cond(input_b)
        if cond_a != None and cond_b != None:
            result_cond = binary_operation(cond_a, cond_b)
            self.write_varnode(op.output, build_int_cond_from_cond(result_cond))
        else:
            self.write_varnode(op.output, int_binary_operation(input_a, input_b))

    def exec_comparison(self, op: pypcode.PcodeOp, comparison_operation: Callable[[BitVecRef, BitVecRef], BoolRef]):
        assert len(op.inputs) == 2
        input_a = self.read_varnode(op.inputs[0])
        input_b = self.read_varnode(op.inputs[1])
        cond = comparison_operation(input_a, input_b)
        self.write_varnode(op.output, build_int_cond_from_cond(cond))

    @staticmethod
    def shift_right(a: BitVecRef, b: BitVecRef) -> BitVecRef:
        if b.size() > a.size():
            b = Extract(a.size() - 1, 0, b)
        if b.size() < a.size():
            b = ZeroExt(a.size() - b.size(), b)
        return LShR(a, b)

    @staticmethod
    def signed_shift_right(a: BitVecRef, b: BitVecRef) -> BitVecRef:
        if b.size() > a.size():
            b = Extract(a.size() - 1, 0, b)
        if b.size() < a.size():
            b = ZeroExt(a.size() - b.size(), b)
        return a >> b

    @staticmethod
    def shift_left(a: BitVecRef, b: BitVecRef) -> BitVecRef:
        if b.size() > a.size():
            b = Extract(a.size() - 1, 0, b)
        if b.size() < a.size():
            b = ZeroExt(a.size() - b.size(), b)
        return a << b

    def exec_pcode_op(self, op: pypcode.PcodeOp, insn_addr: int):
        binops = {
            pypcode.OpCode.INT_XOR: lambda a,b: a ^ b,
            pypcode.OpCode.INT_AND: lambda a,b: a & b,
            pypcode.OpCode.INT_ADD: lambda a,b: a + b,
            pypcode.OpCode.INT_SUB: lambda a,b: a - b,
            pypcode.OpCode.INT_MULT: lambda a,b: a * b,
            pypcode.OpCode.INT_REM: lambda a,b: URem(a,b),
            pypcode.OpCode.INT_OR: lambda a,b: a | b,
            pypcode.OpCode.INT_RIGHT: State.shift_right,
            pypcode.OpCode.INT_SRIGHT: State.signed_shift_right,
            pypcode.OpCode.INT_LEFT: State.shift_left,
        }
        bool_binops = {
            pypcode.OpCode.BOOL_OR: (Or, lambda a,b: a|b),
            pypcode.OpCode.BOOL_XOR: (Xor, lambda a,b: a^b),
            pypcode.OpCode.BOOL_AND: (And, lambda a,b: a&b),
        }
        comparisons = {
            pypcode.OpCode.INT_SLESS: lambda a,b: a < b,
            pypcode.OpCode.INT_LESS: lambda a,b: ULT(a, b),
            pypcode.OpCode.INT_EQUAL: lambda a,b: a == b,
            pypcode.OpCode.INT_NOTEQUAL: lambda a,b: a != b,
            pypcode.OpCode.INT_SCARRY: lambda a,b: Not(BVAddNoOverflow(a, b, True)),
            pypcode.OpCode.INT_CARRY: lambda a,b: Not(BVAddNoOverflow(a, b, False)),
            pypcode.OpCode.INT_SBORROW: lambda a,b: Or(Not(BVSubNoUnderflow(a, b, True)), Not(BVSubNoOverflow(a, b))),
        }
        if op.opcode == pypcode.OpCode.COPY:
            input = self.read_varnode(op.inputs[0])
            self.write_varnode(op.output, input)
        elif op.opcode == pypcode.OpCode.LOAD:
            assert len(op.inputs) == 2
            space_id_input = op.inputs[0]
            assert space_id_input.space.name == 'const'
            space_id = space_id_input.offset
            addr = self.read_varnode(op.inputs[1])
            mem_access = MemAccess(addr, op.output.size)
            result = self.read_mem(mem_access)
            self.write_varnode(op.output, result)
        elif op.opcode == pypcode.OpCode.STORE:
            assert len(op.inputs) == 3
            space_id_input = op.inputs[0]
            assert space_id_input.space.name == 'const'
            space_id = space_id_input.offset
            addr = self.read_varnode(op.inputs[1])
            mem_access = MemAccess(addr, op.inputs[2].size)
            result = self.read_varnode(op.inputs[2])
            self.write_mem(mem_access, result, insn_addr)
        elif op.opcode == pypcode.OpCode.SUBPIECE:
            assert len(op.inputs) == 2
            shit_amount_varnode = op.inputs[1]
            assert shit_amount_varnode.space.name == 'const'
            shift_amount = shit_amount_varnode.offset
            value = self.read_varnode(op.inputs[0])
            result = value >> shift_amount
            output_size_in_bits = op.output.size * BITS_PER_BYTE
            if result.size() > output_size_in_bits:
                result = Extract(output_size_in_bits - 1, 0, result)
            self.write_varnode(op.output, result)
        elif op.opcode == pypcode.OpCode.POPCOUNT:
            input = self.read_varnode(op.inputs[0])
            desired_size = op.output.size * BITS_PER_BYTE
            bits = (Extract(i, i, input) for i in range(input.size()))
            expanded_bits = (Concat(BitVecVal(0, desired_size - 1), bit) for bit in bits)
            result = Sum(*expanded_bits)
            self.write_varnode(op.output, result)
        elif op.opcode == pypcode.OpCode.INT_ZEXT:
            assert len(op.inputs) == 1
            assert op.output.size > op.inputs[0].size
            value = self.read_varnode(op.inputs[0])
            expand_by_bytes_amount = op.output.size - op.inputs[0].size
            result = ZeroExt(expand_by_bytes_amount * BITS_PER_BYTE, value)
            self.write_varnode(op.output, result)
        elif op.opcode == pypcode.OpCode.INT_SEXT:
            assert len(op.inputs) == 1
            assert op.output.size > op.inputs[0].size
            value = self.read_varnode(op.inputs[0])
            expand_by_bytes_amount = op.output.size - op.inputs[0].size
            result = SignExt(expand_by_bytes_amount * BITS_PER_BYTE, value)
            self.write_varnode(op.output, result)
        elif op.opcode == pypcode.OpCode.INT_2COMP:
            assert len(op.inputs) == 1
            value = self.read_varnode(op.inputs[0])
            self.write_varnode(op.output, -value)
        elif op.opcode == pypcode.OpCode.INT_NEGATE:
            assert len(op.inputs) == 1
            value = self.read_varnode(op.inputs[0])
            self.write_varnode(op.output, ~value)
        elif op.opcode == pypcode.OpCode.BOOL_NEGATE:
            assert len(op.inputs) == 1
            value = self.read_varnode(op.inputs[0])
            cond = try_extract_cond_from_int_cond(value)
            if cond != None:
                self.write_varnode(op.output, build_int_cond_from_cond(Not(cond)))
            else:
                self.write_varnode(op.output, build_int_cond_from_cond(value == 0))
        elif op.opcode == pypcode.OpCode.CALLOTHER:
            assert len(op.inputs) >= 1
            assert op.inputs[0].space.name == 'const'
            index = op.inputs[0].offset
            if index == 74:
                # rdtsc
                assert len(op.inputs) == 1
                self.write_varnode(op.output, BitVec('rdtsc_{}'.format(time.time()), 64))
            else:
                raise Exception('unknown CALLOTHER index {}'.format(index))
        elif op.opcode in binops:
            binop = binops[op.opcode]
            self.exec_binop(op, binop)
        elif op.opcode in bool_binops:
            (bool_binop, int_binop)  = bool_binops[op.opcode]
            self.exec_bool_binop(op, bool_binop, int_binop)
        elif op.opcode in comparisons:
            comparison = comparisons[op.opcode]
            self.exec_comparison(op, comparison)
        else:
            raise Exception('no handler for opcode {}'.format(op.opcode))

    def substitute(self, expr: BitVecRef, read_single_mem_byte: Callable[[int], int], *substitutions):
        expr = substitute(expr, *substitutions)
        while True:
            did_anything = False
            cur_vars = z3util.get_vars(expr)
            for var in cur_vars:
                prefix = MEM_VAR_NAME_PREFIX + '_'
                var_name = var.decl().name()
                if not var_name.startswith(prefix):
                    continue
                var_id = int(var_name[len(prefix):])
                mem_addr_expr = self.mem_var_addresses[var_id]
                mem_addr_expr = simplify(substitute(mem_addr_expr, *substitutions))
                mem_addr = try_expr_to_concrete(mem_addr_expr)
                if mem_addr != None:
                    assert var.size() == 8
                    mem_byte_value = read_single_mem_byte(mem_addr)
                    expr = substitute(expr, (var, BitVecVal(mem_byte_value, 8)))
                    did_anything = True
            if not did_anything:
                break

        expr = simplify(expr)
        return expr

    def cleanup_unique_varnodes(self):
        addrs_to_delete = []
        for addr in self.varnode_values.keys():
            if addr.space_name == 'unique':
                addrs_to_delete.append(addr)
        for addr in addrs_to_delete:
            del self.varnode_values[addr]

    def exec_single_insn(self, code: bytes, code_addr: int) -> List[Successor]:
        tx = self.ctx.translate(code,base_address=code_addr)
        branched_to = None
        assert len(tx.ops) > 0
        imark_op = tx.ops[0]
        assert imark_op.opcode == pypcode.OpCode.IMARK
        assert imark_op.inputs[0].offset == code_addr
        next_insn_addr = code_addr + imark_op.inputs[0].size
        successors = self.exec_pcode_ops(tx.ops, 1, code_addr, next_insn_addr)
        for successor in successors:
            successor.state.cleanup_unique_varnodes()
        return successors

    def add_constraint(self, constraint: BoolRef):
        self.constraints.append(constraint)
        self.solver.add(constraint)

    def resolve_condition(self, cond_value_expr: ExprRef) -> ResolvedCondition:
        # check if the condition is certainly false
        cond_true_solve_result = self.solver.check(cond_value_expr != 0)
        if cond_true_solve_result == unsat:
            # if the condition being true is unsatisfied, the condition is known to be false.
            return ResolvedCondition.FALSE

        # here, the condition being true is satisfiable, so it **might** be true, but we don't know if it is true or unconstrained.
        # so, we must perform some other check to determine if it is certainly true.

        cond_false_solve_result = self.solver.check(cond_value_expr == 0)
        if cond_false_solve_result == unsat:
            # if the condition being false is unsatisfied, the condition is known to be true.
            return ResolvedCondition.TRUE

        # here, we know that the condition is unknown - may be true and may be false.
        print('UNKNOWN CONDITION {}'.format(cond_value_expr))
        return ResolvedCondition.UNKNOWN

    def exec_pcode_ops(self, ops: List[pypcode.Instruction], first_op_index: int, insn_addr: int, next_insn_addr: int) -> List[Successor]:
        for i, op in itertools.islice(enumerate(ops), first_op_index, None):
            if op.opcode == pypcode.OpCode.IMARK:
                if i == 0:
                    # this is the imark of the current instruction, ignore it
                    continue
                else:
                    # reached a second IMARK, so this is no longer the first instruction. stop executing.
                    break
            elif op.opcode == pypcode.OpCode.BRANCH:
                assert len(op.inputs) == 1
                addr_varnode = op.inputs[0]
                if addr_varnode.space.name == 'ram':
                    addr = addr_varnode.offset
                    return [Successor(self, BitVecVal(addr, 64), True, False, False)]
                else:
                    assert addr_varnode.space.name == 'const'
                    return self.exec_pcode_ops(ops, i + addr_varnode.offset, insn_addr, next_insn_addr)
            elif op.opcode == pypcode.OpCode.BRANCHIND:
                assert len(op.inputs) == 1
                addr = self.read_varnode(op.inputs[0])
                return [Successor(self, addr, True, False, True)]
            elif op.opcode == pypcode.OpCode.CBRANCH:
                assert len(op.inputs) == 2
                addr_varnode = op.inputs[0]
                cond_value_expr = self.read_varnode(op.inputs[1])
                resolved_condition = self.resolve_condition(cond_value_expr)

                if addr_varnode.space.name == 'ram':
                    addr = addr_varnode.offset
                    if resolved_condition == ResolvedCondition.FALSE:
                        # the branch is not taken, so continue to the next pcode insn.
                        continue
                    elif resolved_condition == ResolvedCondition.TRUE:
                        # the branch is taken.
                        return [Successor(self, BitVecVal(addr, 64), True, False, False)]
                    elif resolved_condition == ResolvedCondition.UNKNOWN:
                        # here, we know that the condition is unknown - may be true and may be false, so take both branches.
                        print('UNKNOWN COND:')
                        print('***')
                        print('R8 = {}'.format(self.regs.r8))
                        print(try_extract_cond_from_int_cond(cond_value_expr))
                        print('***')

                        # generate the successor for the case where the branch is taken.
                        branch_taken_state = self.copy()
                        branch_taken_state.add_constraint(cond_value_expr != 0)
                        branch_taken_successor = Successor(branch_taken_state, BitVecVal(addr, 64), True, False, False)

                        # generate the successors for the case where the branch is **not** taken.
                        self.add_constraint(cond_value_expr == 0)
                        branch_not_taken_successors = self.exec_pcode_ops(ops, i + 1, insn_addr, next_insn_addr)
                        return branch_not_taken_successors + [branch_taken_successor]
                    else:
                        unreachable()
                else:
                    # handle a pcode relative branch
                    assert addr_varnode.space.name == 'const'
                    if resolved_condition == ResolvedCondition.FALSE:
                        # the branch is not taken, so continue to the next pcode insn.
                        continue
                    elif resolved_condition == ResolvedCondition.TRUE:
                        # the branch is taken.
                        return self.exec_pcode_ops(ops, i + addr_varnode.offset, insn_addr, next_insn_addr)
                    elif resolved_condition == ResolvedCondition.UNKNOWN:
                        # here, we know that the condition is unknown - may be true and may be false, so take both branches.

                        # generate the successors for the case where the branch is taken.
                        branch_taken_state = self.copy()
                        branch_taken_state.add_constraint(cond_value_expr != 0)
                        branch_taken_successors = branch_taken_state.exec_pcode_ops(ops, i + addr_varnode.offset, insn_addr, next_insn_addr)

                        # generate the successors for the case where the branch is **not** taken.
                        self.add_constraint(cond_value_expr == 0)
                        branch_not_taken_successors = self.exec_pcode_ops(ops, i + 1, insn_addr, next_insn_addr)
                        return branch_not_taken_successors + branch_taken_successors
                    else:
                        unreachable()

            elif op.opcode == pypcode.OpCode.RETURN:
                assert len(op.inputs) == 1
                addr = self.read_varnode(op.inputs[0])
                return [Successor(self, addr, True, True, True)]
                
            self.exec_pcode_op(op, insn_addr)
        return [Successor(self, BitVecVal(next_insn_addr, 64), False, False, False)]

    def read_single_byte_from_mem_or_dump_file(self, dumpfile_reader: MinidumpFileReader, address: int) -> int:
        addr_bitvec = BitVecVal(address, 64)
        if addr_bitvec in self.mem_values:
            raise Exception('self modifying code')
            # expr = self.read_mem(self.mem_values[addr_bitvec])
            # return expr_to_concrete(expr)
        else:
            return dumpfile_reader.read(address, 1)[0]

    def exec_single_insn_from_dump_file(self, dumpfile_reader: MinidumpFileReader, address: int) -> List[Successor]:
        insn_single_bytes = []
        for cur_addr in range(address, address + X86_MAX_INSN_LEN):
            insn_single_bytes.append(self.read_single_byte_from_mem_or_dump_file(dumpfile_reader, cur_addr))
        insn_bytes = bytes(insn_single_bytes)

        # debug
        cs = Cs(CS_ARCH_X86, CS_MODE_64)
        insn_addr, insn_size, insn_mnemonic, insn_op_str = next(cs.disasm_lite(insn_bytes, address))
        print('executing insn {} {} {}'.format(hex(address), insn_mnemonic, insn_op_str))
        # debug

        return self.exec_single_insn(insn_bytes, address)

    @property
    def regs(self) -> StateRegs:
        return StateRegs(self)
            
@dataclass
class StateRegs:
    state: State
    def __getattr__(self, name):
        if name in self.__dict__:
            return self.__dict__[name]
        for reg_name, reg_varnode in self.state.ctx.registers.items():
            if reg_name.lower() == name:
                return self.state.read_varnode(reg_varnode)
        raise Exception('no register named {}'.format(name))

    def __setattr__(self, name, value):
        if 'state' not in self.__dict__:
            self.__dict__[name] = value
            return
        for reg_name, reg_varnode in self.state.ctx.registers.items():
            if reg_name.lower() == name:
                self.state.write_varnode(reg_varnode, value)
                return
        raise Exception('no register named {}'.format(name))
    

def expr_to_concrete(expr: BitVecRef) -> int:
    assert isinstance(expr, BitVecNumRef), 'expression {} is not a concrete value, its type is {}'.format(expr, type(expr))
    return expr.as_long()

def try_expr_to_concrete(expr: BitVecRef) -> Optional[int]:
    if not isinstance(expr, BitVecNumRef):
        return None
    return expr.as_long()


@dataclass
class ActiveState:
    state: State
    next_insn_addr: int

    def is_same_as(self, other: ActiveState) -> bool:
        """
        checks if this state is the same as the given other state.
        this means that all varnode and memory values are the same, and the next instruction to be executed is also the same.
        the states are considered the same even if they differ in their constraints.
        """
        return self.next_insn_addr == other.next_insn_addr and self.state.is_same_as(other.state)

@dataclass
class UnconstrainedState:
    state: State
    next_insn_addr: BitVecRef

@dataclass
class StepOptions:
    allow_indirect_branches: bool

class ActiveStatesSet:
    def __init__(self):
        self.states = []

    def append_state(self, new_active_state: ActiveState):
        for cur_state_index in range(len(self.states)):
            cur_active_state = self.states[cur_state_index]
            if not new_active_state.is_same_as(cur_active_state):
                continue

            # the two states are the same, but may have different constraints. keep only the shared constraints
            # and combine them into a single state.
            shared_constraints = new_active_state.state.shared_constraints_with(cur_active_state.state)
            shared_constraints_solver = Solver()
            for constraint in shared_constraints:
                shared_constraints_solver.add(constraint)
            combined_state = new_active_state.state.copy()
            combined_state.constraints = shared_constraints
            combined_state.solver = shared_constraints_solver
            self.states[cur_state_index] = ActiveState(combined_state, new_active_state.next_insn_addr)

            # we combined the states, so we are done adding the new state
            return
        self.states.append(new_active_state)

class SimManager:
    def __init__(self, dumpfile_reader: MinidumpFileReader, initial_state: State, first_insn_addr: int):
        self.dumpfile_reader = dumpfile_reader
        self.active = [ActiveState(initial_state, first_insn_addr)]
        self.unconstrained = []
        self.stopped = []

    def run(self, opts: StepOptions):
        while not self.finished():
            self.step(opts)

    def finished(self):
        return len(self.active) == 0

    def step(self, opts: StepOptions):
        new_active = ActiveStatesSet()
        for state_index, active_state in enumerate(self.active):
            # print('STEPPING STATE {}'.format(state_index))
            successors = active_state.state.exec_single_insn_from_dump_file(
                self.dumpfile_reader,
                active_state.next_insn_addr
            )
            for i, successor in enumerate(successors):
                new_state = active_state.state
                if i > 0:
                    # all successors should copy the state, except for the first one which uses the original state
                    # to avoid excess copying.
                    new_state = new_state.copy()

                next_insn_addr_concrete = try_expr_to_concrete(successor.next_insn_addr)
                if next_insn_addr_concrete == None:
                    # next address is unconstrained, or this successor is an indirect branch and indirect branches are not allowed
                    self.unconstrained.append(UnconstrainedState(new_state, successor.next_insn_addr))
                else:
                    # next address is concrete
                    new_active_state = ActiveState(new_state, next_insn_addr_concrete)
                    if successor.is_indirect_branch and not opts.allow_indirect_branches:
                        self.stopped.append(new_active_state)
                    else:
                        new_active.append_state(new_active_state)
        self.active = new_active.states

class VmSimManager:
    def __init__(self, pushed_magic: int):
        self.pushed_magic = pushed_magic
        self.pushed_magic_value_bitvec = BitVecVal(pushed_magic, 64)
        self.pushed_magic_var = BitVec('pushed_magic', 64)

        initial_state = State()
        initial_state.set_read_mem_single_byte_fallback(read_dump_byte)
        initial_state.write_mem(MemAccess(initial_state.regs.rsp + 8, 8), self.pushed_magic_value_bitvec, None)

        initial_state.regs.eflags = BitVecVal(0x200246, 32)

        # some conditions can have weird results if `rsp` is close to one of the ends of the address space,
        # so make sure that it isn't.
        rsp_distance_from_ends_of_address_space = 0x16000
        min_rsp = rsp_distance_from_ends_of_address_space
        max_rsp = 2**64 - rsp_distance_from_ends_of_address_space
        initial_state.add_constraint(UGE(initial_state.regs.rsp, BitVecVal(min_rsp, 64)))
        initial_state.add_constraint(ULT(initial_state.regs.rsp, BitVecVal(max_rsp, 64)))

        self.simgr = SimManager(DUMP_READER, initial_state, VIRT_ENTRY_POINT_ADDR)

    def exec_single_vm_handler(self):
        for i, active_state in enumerate(self.simgr.active):
            active_state.state.reset_mem_write_tracking()
            # print('ABOUT TO STEP STATE {} STARTING AT ADDR {}'.format(i, hex(active_state.next_insn_addr)))
        self.simgr.run(StepOptions(allow_indirect_branches=False))
        assert len(self.simgr.unconstrained) == 0
        assert len(self.simgr.stopped) > 0

        # for i, stopped_state in enumerate(self.simgr.stopped):
        #     print('MEM WRITES FOR STATE {}'.format(i))
        #     print('===========')
        #     for insn_addr, tracked_write in stopped_state.state.mem_writes.items():
        #         print('INSN {}'.format(get_insn_disassembly(insn_addr)))
        #         print('ADDR = {}'.format(tracked_write.addr))
        #         print('VALUE = {}'.format(tracked_write.value))
        #         print()
        #     print('===========')

        # print()
        # print()

        # re-activate the stopped states
        self.simgr.active = self.simgr.stopped
        self.simgr.stopped = []

def read_dump_byte(addr: int) -> int:
    return DUMP_READER.read(addr, 1)[0]

def try_read_dump_byte(addr: int) -> Optional[int]:
    try:
        return DUMP_READER.read(addr, 1)[0]
    except Exception as e:
        if 'Address not in memory range' in str(e):
            return None
        else:
            raise
    
def get_vm_entrypoint_final_state(pushed_magic: BitVec) -> UnconstrainedState:
    initial_state = State()
    initial_state.write_mem(MemAccess(initial_state.regs.rsp + 8, 8), pushed_magic, None)
    simgr = SimManager(DUMP_READER, initial_state, VIRT_ENTRY_POINT_ADDR)
    simgr.run(StepOptions(True))
    assert len(simgr.unconstrained) == 1
    return simgr.unconstrained[0]

def calculate_vm_state_structure():
    pushed_magic = BitVec('pushed_magic', 64)
    vm_ep_state = get_vm_entrypoint_final_state(try_read_dump_byte)

    # r8 points to the VM state, which is constructed on the stack.
    state_addr = vm_ep_state.state.regs.r8
    orig_rsp = BitVec('orig_rsp', 64)
    # r8 = rsp - X
    # where X is the size of the VM state.
    # to calculate X, we do:
    # rsp - r8 = rsp - (rsp - X) = rsp - rsp + X = X
    state_size = expr_to_concrete(simplify(orig_rsp - state_addr))
    print('state size = {}'.format(hex(state_size)))

    for i in range(state_size // 8):
        addr = simplify(state_addr + (i*8))
        mem_access = MemAccess(addr, 8)
        if not vm_ep_state.state.was_entire_mem_written_to(mem_access):
            continue
        qword = vm_ep_state.state.read_mem(mem_access)
        print('mem[R8 + {}] = {}'.format(hex(i*8), qword))

    print('final R8 = {}'.format(vm_ep_state.state.regs.r8))

def get_vm_first_handler_addr(pushed_magic: int):
    pushed_magic_var = BitVec('pushed_magic', 64)
    vm_ep_state = get_vm_entrypoint_final_state(pushed_magic_var)
    handler_addr_expr = vm_ep_state.state.substitute(
        vm_ep_state.next_insn_addr, read_dump_byte, (pushed_magic_var, BitVecVal(pushed_magic, 64))
    )
    return expr_to_concrete(handler_addr_expr)

def get_vm_handler_final_state(addr: int) -> UnconstrainedState:
    initial_state = State()
    simgr = SimManager(DUMP_READER, initial_state, addr)
    simgr.run(StepOptions(True))
    assert len(simgr.unconstrained) == 1
    return simgr.unconstrained[0]

def explore_ep_final_state():
    pushed_magic = BitVec('pushed_magic', 64)
    final_state = get_vm_entrypoint_final_state(pushed_magic)

    print(final_state.state.regs.r9)
    r9 = final_state.state.substitute(final_state.state.regs.r9, read_dump_byte, (pushed_magic, BitVecVal(EXAMPLE_PUSHED_MAGIC, 64)))
    print(r9)

def decode_vm_insn_find_relevant_writes(final_state: State) -> List[TrackedMemWriteAggregator]:
    result = []
    for insn_addr, write in final_state.mem_writes.items():
        write_end_addr = simplify(write.addr + write.size_in_bytes)
        if is_concretely_unsigned_lower_or_eq_to(final_state.solver, write_end_addr, final_state.regs.rsp):
            # if the end address of the write is below (or equal to) rsp, then the write is no longer relevant.
            continue
        result.append(write)
    return result

class VmInsnWriteTarget(enum.Enum):
    VM_STATE_REG = 1

class VmInsnWrittenValue(enum.Enum):
    VM_TOP_OF_STACK = 1

def are_lists_concretely_equal_regardless_of_order(solver: Solver, a: List[BitVecRef], b: List[BitVecRef]) -> bool:
    if len(a) != len(b):
        return False
    b = b.copy()
    for a_item in a:
        found = False
        for b_index in range(len(b)):
            if are_concretely_equal(solver, a_item, b[b_index]):
                found = True
                del b[b_index]
                break
        if not found:
            return False
    return True

def decode_vm_insn_write_target(write: TrackedMemWriteAggregator) -> VmInsnWriteTarget:
    write_addr_vars = z3util.get_vars(write.addr)
    if are_lists_concretely_equal_regardless_of_order(
        EMPTY_SOLVER,
        write_addr_vars,
        [BitVec('vm_state_ptr', 64), BitVec('code_byte_0', 8), BitVec('vm_checksum_accumulator', 64)]
    ):
        return VmInsnWriteTarget.VM_STATE_REG
    else:
        assert False, 'unknown insn write target, write addr = {}'.format(write.addr)

def decode_vm_insn_written_value(write: TrackedMemWriteAggregator) -> VmInsnWrittenValue:
    value = write.value
    value_vars = z3util.get_vars(value)
    if value == BitVec('vm_stack_0', 64):
        return VmInsnWrittenValue.VM_TOP_OF_STACK
    else:
        assert False, 'unknown insn written value, value = {}'.format(value)

def decode_vm_insn(vm_handler_addr: int):
    initial_state = State()
    initial_state.regs.rbx = BitVecVal(vm_handler_addr, 64)
    initial_state.set_read_mem_single_byte_fallback(read_dump_byte)
    vm_state_ptr = BitVec('vm_state_ptr', 64)
    initial_state.regs.rsp = vm_state_ptr

    # some conditions can have weird results if `rsp` is close to one of the ends of the address space,
    # so make sure that it isn't.
    rsp_distance_from_ends_of_address_space = 0x16000
    min_rsp = rsp_distance_from_ends_of_address_space
    max_rsp = 2**64 - rsp_distance_from_ends_of_address_space
    initial_state.add_constraint(UGE(initial_state.regs.rsp, BitVecVal(min_rsp, 64)))
    initial_state.add_constraint(ULT(initial_state.regs.rsp, BitVecVal(max_rsp, 64)))

    vm_state_size = 0x100
    for reg_offset in range(0, vm_state_size, 8):
        initial_state.write_mem(MemAccess(initial_state.regs.rsp + reg_offset, 8), BitVec('vm_reg_{}'.format(reg_offset), 64), None)

    vm_stack_ptr = BitVec('vm_stack_ptr', 64)
    initial_state.regs.r8 = vm_stack_ptr

    stack_vars_amount = 16
    for stack_off in range(0, 8*stack_vars_amount, 8):
        initial_state.write_mem(MemAccess(initial_state.regs.r8 + stack_off, 8), BitVec('vm_stack_{}'.format(stack_off), 64), None)

    vm_checksum_accumulator = BitVec('vm_checksum_accumulator', 64)
    initial_state.regs.r9 = vm_checksum_accumulator

    vm_ip = BitVec('vm_ip', 64)
    initial_state.regs.r10 = vm_ip

    max_insn_size = 64
    for stack_off in range(max_insn_size):
        initial_state.write_mem(MemAccess(initial_state.regs.r10 + stack_off, 1), BitVec('code_byte_{}'.format(stack_off), 8), None)

    initial_state.enable_mem_write_tracking()

    simgr = SimManager(DUMP_READER, initial_state, vm_handler_addr)
    simgr.run(StepOptions(False))
    assert len(simgr.unconstrained) == 1
    assert len(simgr.stopped) == 0
    final_state = simgr.unconstrained[0].state
    relevant_writes = decode_vm_insn_find_relevant_writes(final_state)
    if (
        len(relevant_writes) == 1 and
        decode_vm_insn_write_target(relevant_writes[0]) == VmInsnWriteTarget.VM_STATE_REG and
        decode_vm_insn_written_value(relevant_writes[0]) == VmInsnWrittenValue.VM_TOP_OF_STACK
    ):
        print('POP <REG>')
    else:
        assert False, 'failed to decode vm instruction'

def shit():
    vm_simgr = VmSimManager(EXAMPLE_PUSHED_MAGIC)
    vm_simgr.simgr.run(StepOptions(allow_indirect_branches=True))
    # run the vm entry handler
    # vm_simgr.exec_single_vm_handler()
    # for i in range(28):
    #     assert len(vm_simgr.simgr.active) == 1
    #     decode_vm_insn(vm_simgr.simgr.active[0].next_insn_addr)
    #     vm_simgr.exec_single_vm_handler()

    # decode_vm_insn(0xce79b8)

    # handler_addr = get_vm_first_handler_addr(EXAMPLE_PUSHED_MAGIC)
    # final_state = get_vm_handler_final_state(handler_addr)
    # print(final_state.next_insn_addr)
    # print(z3util.get_vars(final_state.next_insn_addr))

def main():
    shit()
    # explore_ep_final_state()
    # calculate_vm_state_structure()

# main()

vm_simgr = VmSimManager(EXAMPLE_PUSHED_MAGIC)
vm_simgr.simgr.run(StepOptions(allow_indirect_branches=True))
