from ast import *
from compiler import *
from utils import repr_Module
import type_check_Pvar
import interp_Pvar

# test program here
# prog = """
# a = 20 + - 30
# b = input_int() + 10 + 20
# print(a + b + 60)
# """

# prog = """
# a = 2
# b = 1
# c = a + b
# print(c)
# """

prog = """
a = -1
print(a)
"""

p = parse(prog)
type_check_Pvar.TypeCheckPvar().type_check_P(p)
print("======= type check passes")

print("======= interpreting original program")
interp = interp_Pvar.InterpPvar()
interp.interp_P(p)

print("======= interpreting RCOed program")
compiler = Compiler()
p_rcoed = compiler.remove_complex_operands(p)
interp.interp_P(p_rcoed)
print("======= printing RCOed program")
print(p_rcoed)

print("======= selecting instructions")
p_x64_var = compiler.select_instructions(p_rcoed)
print(p_x64_var)
