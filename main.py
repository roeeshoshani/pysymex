from __future__ import annotations
from z3 import *
from capstone import *
from typing import Callable, Optional, Tuple, List
from dataclasses import dataclass
from minidump.minidumpfile import MinidumpFile
from IPython import embed
import pypcode

BITS_PER_BYTE = 8
DUMP_FILE_PATH = '/home/sho/Documents/freelance/getcode/GetCode.DMP'
VIRT_ENTRY_POINT_ADDR = 0x00d6bd08
X86_MAX_INSN_LEN = 15
EXAMPLE_PUSHED_MAGIC = 0x72a7c5d7
MEM_VAR_NAME_PREFIX = 'orig_mem'

@dataclass(frozen=True)
class VarnodeAddr:
    space: pypcode.AddrSpace
    off: int

@dataclass(frozen=True)
class MemAccess:
    addr: ExprRef
    size_in_bytes: int

def bits_to_bytes_safe(bits_amount: int) -> int:
    assert bits_amount % BITS_PER_BYTE == 0
    return bits_amount // BITS_PER_BYTE

@dataclass(frozen=True)
class BranchedTo:
    addr: ExprRef
    is_ret: bool

@dataclass(frozen=True)
class ExecPcodeOpRes:
    branched_to: Optional[BranchedTo]

@dataclass
class Successor:
    state: State
    next_insn_addr: ExprRef
    is_branch: bool
    is_return: bool

def is_extract(expr: ExprRef) -> bool:
    return is_app_of(expr, Z3_OP_EXTRACT)

def are_concretely_equal(a: ExprRef, b: ExprRef) -> bool:
    if a.size() != b.size():
        return False
    solver = Solver()
    solver.add(a != b)
    return solver.check() == unsat

def simplify_concat_extract(single_byte_values: List[ExprRef]) -> List[ExprRef]:
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
        if not are_concretely_equal(byte_val_a.arg(0), byte_val_b.arg(0)):
            # not equal, can't merge
            continue
        combined = Extract(a_high, b_low, byte_val_a.arg(0))
        new_values =single_byte_values[:i] + [combined] + single_byte_values[i+2:]
        return simplify_concat_extract(new_values)
    return single_byte_values

class State:
    def __init__(self):
        self.ctx = pypcode.Context("x86:LE:64:default")
        self.varnode_values = {}
        self.mem_values = {}
        self.mem_var_addresses = []

    def copy(self):
        new_state = State()
        new_state.varnode_values = self.varnode_values.copy()
        new_state.mem_values = self.mem_values.copy()
        new_state.mem_var_addresses = self.mem_var_addresses.copy()
        return new_state

    def get_reg_name_containting_addr(self, addr: VarnodeAddr) -> Optional[str]:
        for reg_name, reg_varnode in self.ctx.registers.items():
            if reg_varnode.space != addr.space:
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

    def read_varnode_single_byte(self, addr: VarnodeAddr) -> ExprRef:
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

    def read_non_const_multibyte_varnode(self, varnode: pypcode.Varnode) -> ExprRef:
        single_byte_values = []
        for rel_byte_off in range(varnode.size):
            addr = VarnodeAddr(varnode.space, varnode.offset + rel_byte_off)
            single_byte_values.append(self.read_varnode_single_byte(addr))
        single_byte_values.reverse()
        single_byte_values = simplify_concat_extract(single_byte_values)
        if len(single_byte_values) == 1:
            return single_byte_values[0]
        else:
            return Concat(single_byte_values)

    def read_non_const_varnode(self, varnode: pypcode.Varnode) -> ExprRef:
        if varnode.size == 1:
            # single byte
            addr = VarnodeAddr(varnode.space, varnode.offset)
            return self.read_varnode_single_byte(addr)
        else:
            # multi byte
            return self.read_non_const_multibyte_varnode(varnode)

    def read_varnode(self, varnode: pypcode.Varnode) -> ExprRef:
        if varnode.space.name == 'const':
            return BitVecVal(varnode.offset, varnode.size * BITS_PER_BYTE)
        else:
            return simplify(self.read_non_const_varnode(varnode))

    def read_mem_single_byte(self, addr: ExprRef) -> ExprRef:
        # simplify the address before trying to access the dictionary.
        # this is important since simplification makes the expression deterministic.
        addr = simplify(addr)
        if addr in self.mem_values:
            return self.mem_values[addr]
        else:
            # value is uninitialized, need to initialize it with a variable
            # var_name = '{}[{}]'.format(MEM_VAR_NAME_PREFIX, addr)
            mem_var_id = len(self.mem_var_addresses)
            var_name = '{}_{}'.format(MEM_VAR_NAME_PREFIX, mem_var_id)
            self.mem_var_addresses.append(addr)
            var = BitVec(var_name, 8)
            self.write_mem_single_byte(addr, var)
            return var

    def read_multibyte_mem(self, access: MemAccess) -> ExprRef:
        single_byte_values = []
        for rel_byte_off in range(access.size_in_bytes):
            addr = access.addr + rel_byte_off
            single_byte_values.append(self.read_mem_single_byte(addr))
        single_byte_values.reverse()
        single_byte_values = simplify_concat_extract(single_byte_values)
        if len(single_byte_values) == 1:
            return single_byte_values[0]
        else:
            return Concat(single_byte_values)

    def read_mem(self, access: MemAccess) -> ExprRef:
        if access.size_in_bytes == 1:
            # single byte
            return self.read_mem_single_byte(access.addr)
        else:
            # multi byte
            return simplify(self.read_multibyte_mem(access))

    def write_varnode_single_byte(self, addr: VarnodeAddr, value: ExprRef):
        assert value.size() == 8
        self.varnode_values[addr] = value
        
    def write_varnode(self, varnode: pypcode.Varnode, value: ExprRef):
        assert value.size() == varnode.size * BITS_PER_BYTE
        value = simplify(value)
        for rel_byte_off in range(varnode.size):
            addr = VarnodeAddr(varnode.space, varnode.offset + rel_byte_off)
            start_bit_offset = rel_byte_off * BITS_PER_BYTE
            extracted_byte = Extract(start_bit_offset + 7, start_bit_offset, value)
            self.write_varnode_single_byte(addr, extracted_byte)

    def write_mem_single_byte(self, addr: ExprRef, value: ExprRef):
        assert value.size() == 8

        # simplify the address before trying to access the dictionary.
        # this is important since simplification makes the expression deterministic.
        addr = simplify(addr)

        self.mem_values[addr] = value
        
    def write_mem(self, access: MemAccess, value: ExprRef):
        assert value.size() == access.size_in_bytes * BITS_PER_BYTE
        value = simplify(value)
        for rel_byte_off in range(access.size_in_bytes):
            addr = access.addr + rel_byte_off
            start_bit_offset = rel_byte_off * BITS_PER_BYTE
            extracted_byte = Extract(start_bit_offset + 7, start_bit_offset, value)
            self.write_mem_single_byte(addr, extracted_byte)

    def exec_binop(self, op: pypcode.PcodeOp, binary_operation: Callable[[ExprRef, ExprRef], ExprRef]):
        assert len(op.inputs) == 2
        input_a = self.read_varnode(op.inputs[0])
        input_b = self.read_varnode(op.inputs[1])
        result = binary_operation(input_a, input_b)
        self.write_varnode(op.output, result)

    def exec_comparison(self, op: pypcode.PcodeOp, comparison_operation: Callable[[ExprRef, ExprRef], BoolRef]):
        assert len(op.inputs) == 2
        input_a = self.read_varnode(op.inputs[0])
        input_b = self.read_varnode(op.inputs[1])
        cond = comparison_operation(input_a, input_b)
        result = If(cond, BitVecVal(1, 8), BitVecVal(0, 8))
        self.write_varnode(op.output, result)

    @staticmethod
    def shift_right(a: ExprRef, b: ExprRef) -> ExprRef:
        if b.size() > a.size():
            b = Extract(a.size() - 1, 0, b)
        if b.size() < a.size():
            b = ZeroExt(a.size() - b.size(), b)
        return LShR(a, b)

    @staticmethod
    def shift_left(a: ExprRef, b: ExprRef) -> ExprRef:
        if b.size() > a.size():
            b = Extract(a.size() - 1, 0, b)
        if b.size() < a.size():
            b = ZeroExt(a.size() - b.size(), b)
        return a << b

    def exec_pcode_op(self, op: pypcode.PcodeOp):
        binops = {
            pypcode.OpCode.INT_XOR: lambda a,b: a ^ b,
            pypcode.OpCode.INT_AND: lambda a,b: a & b,
            pypcode.OpCode.INT_ADD: lambda a,b: a + b,
            pypcode.OpCode.INT_SUB: lambda a,b: a - b,
            pypcode.OpCode.INT_MULT: lambda a,b: a * b,
            pypcode.OpCode.INT_REM: lambda a,b: URem(a,b),
            pypcode.OpCode.INT_OR: lambda a,b: a | b,
            pypcode.OpCode.INT_RIGHT: State.shift_right,
            pypcode.OpCode.INT_LEFT: State.shift_left,
            pypcode.OpCode.BOOL_OR: lambda a,b: a | b,
            pypcode.OpCode.BOOL_XOR: lambda a,b: a ^ b,
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
        if op.opcode == pypcode.OpCode.IMARK:
            # do nothing
            pass
        elif op.opcode == pypcode.OpCode.COPY:
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
            self.write_mem(mem_access, result)
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
            self.write_varnode(op.output, -value)
        elif op.opcode == pypcode.OpCode.BOOL_NEGATE:
            assert len(op.inputs) == 1
            value = self.read_varnode(op.inputs[0])
            result = If(value == 0, BitVecVal(1, 8), BitVecVal(0, 8))
            self.write_varnode(op.output, result)
        # elif op.opcode == pypcode.OpCode.BRANCH:
        #     assert len(op.inputs) == 1
        #     addr_varnode = op.inputs[0]
        #     assert addr_varnode.space.name == 'ram'
        #     addr = addr_varnode.offset
        #     branched_to = BranchedTo(BitVecVal(addr, 64), False)
        # elif op.opcode == pypcode.OpCode.CBRANCH:
        #     assert len(op.inputs) == 2
        #     addr_varnode = op.inputs[0]
        #     assert addr_varnode.space.name == 'ram'
        #     addr = addr_varnode.offset
        #     cond_expr = self.read_varnode(op.inputs[1])
        #     if isinstance(cond_expr, BitVecNumRef):
        #         cond = cond_expr.as_long()
        #         assert cond == 0 or cond == 1
        #         if cond != 0:
        #             branched_to = BranchedTo(BitVecVal(addr, 64), False)
        #         else:
        #             # the branch is not takes, do nothing
        #             pass
        #     else:
        #         raise Exception('unresolved condition')
        # elif op.opcode == pypcode.OpCode.RETURN:
        #     assert len(op.inputs) == 1
        #     addr = self.read_varnode(op.inputs[0])
        #     branched_to = BranchedTo(addr, True)
        elif op.opcode in binops:
            binop = binops[op.opcode]
            self.exec_binop(op, binop)
        elif op.opcode in comparisons:
            comparison = comparisons[op.opcode]
            self.exec_comparison(op, comparison)
        else:
            raise Exception('no handler for opcode {}'.format(op.opcode))
        # return ExecPcodeOpRes(branched_to)

    def exec_single_insn(self, code: bytes, base_addr: int) -> List[Successor]:
        tx = self.ctx.translate(code,base_address=base_addr)
        branched_to = None
        assert len(tx.ops) > 0
        imark_op = tx.ops[0]
        assert imark_op.opcode == pypcode.OpCode.IMARK
        assert imark_op.inputs[0].offset == base_addr

        for i, op in enumerate(tx.ops):
            if op.opcode == pypcode.OpCode.IMARK:
                if i == 0:
                    # we already looked at this pcode insn before the loop, ignore it
                    continue
                else:
                    # we reached the next instruction, don't execute it
                    break
            elif op.opcode == pypcode.OpCode.BRANCH:
                assert len(op.inputs) == 1
                addr_varnode = op.inputs[0]
                assert addr_varnode.space.name == 'ram'
                addr = addr_varnode.offset
                return [Successor(self, BitVecVal(addr, 64), True, False)]
            elif op.opcode == pypcode.OpCode.CBRANCH:
                assert len(op.inputs) == 2
                addr_varnode = op.inputs[0]
                assert addr_varnode.space.name == 'ram'
                addr = addr_varnode.offset
                cond_expr = self.read_varnode(op.inputs[1])
                if isinstance(cond_expr, BitVecNumRef):
                    cond = cond_expr.as_long()
                    assert cond == 0 or cond == 1
                    if cond != 0:
                        return [Successor(self, BitVecVal(addr, 64), True, False)]
                    else:
                        # the branch is not taken, continue to the next pcode insn
                        continue
                else:
                    raise Exception('unresolved condition')
            elif op.opcode == pypcode.OpCode.RETURN:
                assert len(op.inputs) == 1
                addr = self.read_varnode(op.inputs[0])
                return [Successor(self, addr, True, True)]
                
            self.exec_pcode_op(op)
        return [Successor(self, BitVecVal(base_addr + imark_op.inputs[0].size, 64), False, False)]

    @property
    def regs(self) -> StateRegs:
        return StateRegs(self)
            
@dataclass
class StateRegs:
    state: State
    def __getattr__(self, name):
        for reg_name, reg_varnode in self.state.ctx.registers.items():
            if reg_name.lower() == name:
                return self.state.read_varnode(reg_varnode)
        raise Exception('no register named {}'.format(name))
    

def expr_to_concrete(expr: ExprRef) -> int:
    assert isinstance(expr, BitVecNumRef), 'expression {} is not a concrete value, its type is {}'.format(expr, type(expr))
    return expr.as_long()
    

def exec_dump_file():
    state = State()
    dump = MinidumpFile.parse(DUMP_FILE_PATH)
    dump_reader = dump.get_reader()
    cs = Cs(CS_ARCH_X86, CS_MODE_64)

    pushed_magic = BitVec('pushed_magic', 64)
    state.write_mem(MemAccess(state.regs.rsp + 8, 8), pushed_magic)

    cur_addr = VIRT_ENTRY_POINT_ADDR
    while True:
        insn_bytes = dump_reader.read(cur_addr, X86_MAX_INSN_LEN)

        insn_addr, insn_size, insn_mnemonic, insn_op_str = next(cs.disasm_lite(insn_bytes, cur_addr))
        print('executing insn {} {} {}'.format(hex(cur_addr), insn_mnemonic, insn_op_str))

        successors = state.exec_single_insn(insn_bytes, cur_addr)

        assert len(successors) == 1
        successor = successors[0]

        if successor.is_return:
            # return
            ret_addr = successor.next_insn_addr

            pushed_magic_example_value = BitVecVal(EXAMPLE_PUSHED_MAGIC, 64)
            ret_addr = substitute(ret_addr, (pushed_magic, pushed_magic_example_value))
            vars = z3util.get_vars(ret_addr)
            for var in vars:
                prefix = MEM_VAR_NAME_PREFIX + '_'
                var_name = var.decl().name()
                assert var_name.startswith(prefix)
                var_id = int(var_name[len(prefix):])
                mem_addr_expr = state.mem_var_addresses[var_id]
                mem_addr_expr = simplify(substitute(mem_addr_expr, (pushed_magic, pushed_magic_example_value)))
                mem_addr = expr_to_concrete(mem_addr_expr)
                assert var.size() == 8
                mem_byte_value = dump_reader.read(mem_addr, 1)[0]
                ret_addr = substitute(ret_addr, (var, BitVecVal(mem_byte_value, 8)))

            ret_addr = simplify(ret_addr)
            print(ret_addr)
            raise
        else:
            cur_addr = expr_to_concrete(successor.next_insn_addr)

def quick():
    state = State()
    state.exec_single_insn(b"\x50\x48\x31\x1C\x24\x59", 0)
    print(statesuccessor.next_insn_addr.rcx)

# quick()
exec_dump_file()
