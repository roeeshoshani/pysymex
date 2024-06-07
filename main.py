from __future__ import annotations
import pypcode
from z3 import *
from typing import Callable, Optional, Tuple
from dataclasses import dataclass
from minidump.minidumpfile import MinidumpFile

BITS_PER_BYTE = 8

@dataclass(frozen=True)
class VarnodeAddr:
    space: pypcode.AddrSpace
    off: int

def bits_to_bytes_sage(bits_amount: int) -> int:
    assert bits_amount % BITS_PER_BYTE == 0
    return bits_amount // BITS_PER_BYTE

class Cpu:
    def __init__(self):
        self.ctx = pypcode.Context("x86:LE:64:default")
        self.varnode_values = {}

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
        # simplify the address before trying to access the dictionary.
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
                var_name = '{}_{}'.format(addr.space.name, addr.off)
                var = BitVec(var_name, 8)
                self.write_varnode_single_byte(addr, var)
                return var

    def read_non_const_multibyte_varnode(self, varnode: pypcode.Varnode) -> ExprRef:
        single_byte_values = []
        for rel_byte_off in range(varnode.size):
            addr = VarnodeAddr(varnode.space, varnode.offset + rel_byte_off)
            single_byte_values.append(self.read_varnode_single_byte(addr))
        single_byte_values.reverse()
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
            x = self.read_non_const_varnode(varnode)
            return simplify(self.read_non_const_varnode(varnode))

    def write_varnode_single_byte(self, addr: VarnodeAddr, value: ExprRef):
        assert value.size() == 8
        self.varnode_values[addr] = simplify(value)
        
    def write_varnode(self, varnode: pypcode.Varnode, value: ExprRef):
        assert value.size() == varnode.size * BITS_PER_BYTE
        value = simplify(value)
        for rel_byte_off in range(varnode.size):
            addr = VarnodeAddr(varnode.space, varnode.offset + rel_byte_off)
            start_bit_offset = rel_byte_off * BITS_PER_BYTE
            extracted_byte = Extract(start_bit_offset + 7, start_bit_offset, value)
            self.write_varnode_single_byte(addr, extracted_byte)

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

    def exec_pcode_op(self, op: pypcode.PcodeOp):
        binops = {
            pypcode.OpCode.INT_XOR: lambda a,b: a ^ b,
            pypcode.OpCode.INT_AND: lambda a,b: a & b,
            pypcode.OpCode.INT_ADD: lambda a,b: a + b,
        }
        comparisons = {
            pypcode.OpCode.INT_SLESS: lambda a,b: a < b,
            pypcode.OpCode.INT_EQUAL: lambda a,b: a == b,
            pypcode.OpCode.INT_SCARRY: lambda a,b: Not(BVAddNoOverflow(a, b, True)),
        }
        if op.opcode == pypcode.OpCode.IMARK:
            # do nothing
            pass
        elif op.opcode == pypcode.OpCode.COPY:
            input = self.read_varnode(op.inputs[0])
            self.write_varnode(op.output, input)
        elif op.opcode == pypcode.OpCode.POPCOUNT:
            input = self.read_varnode(op.inputs[0])
            desired_size = op.output.size * BITS_PER_BYTE
            bits = (Extract(i, i, input) for i in range(input.size()))
            expanded_bits = (Concat(BitVecVal(0, desired_size - 1), bit) for bit in bits)
            result = Sum(*expanded_bits)
            self.write_varnode(op.output, result)
        elif op.opcode in binops:
            binop = binops[op.opcode]
            self.exec_binop(op, binop)
        elif op.opcode in comparisons:
            comparison = comparisons[op.opcode]
            self.exec_comparison(op, comparison)
        else:
            raise Exception('no handler for opcode {}'.format(op.opcode))

    def exec(self, code: bytes):
        tx = self.ctx.translate(code)
        for op in tx.ops:
            self.exec_pcode_op(op)

    @property
    def regs(self) -> CpuRegs:
        return CpuRegs(self)
            
@dataclass
class CpuRegs:
    cpu: Cpu
    def __getattr__(self, name):
        for reg_name, reg_varnode in self.cpu.ctx.registers.items():
            if reg_name.lower() == name:
                return self.cpu.read_varnode(reg_varnode)
        raise Exception('no register named {}'.format(name))
    

cpu = Cpu()
cpu.exec(b"\x48\x35\x34\x12\x00\x00")
print(cpu.regs.rax)
# print(cpu.varnode_values)
