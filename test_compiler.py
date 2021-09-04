from ast import *
from compiler import *
from utils import repr_Module
import type_check_Pvar
import interp_Pvar

# test program here
prog1 = """
a = 20 + - 30
b = input_int() + 10 + 20
print(a + b + 60)
"""

p = parse(prog1)
type_check_Pvar.TypeCheckPvar().type_check_P(p)
print("======= type check passes")

print("======= interpreting original program")
interp = interp_Pvar.InterpPvar()
interp.interp_P(p)

print("======= interpreting RCOed program")
compiler = Compiler()
p_rcoed = compiler.remove_complex_operands(p)
interp.interp_P(p_rcoed)
