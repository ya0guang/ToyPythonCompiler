from ast import *
from compiler import *
from utils import repr_Module
import type_check_Pif
import interp_Pif
import interp_Cif
import interp_Pvar
from interp_x86 import eval_x86

prog = """
x = 1
y = 1
if False or x!= y and x == y or True:
  u = x < y
  v = x <= y
  w = x > y
  z = x >= y
else:
  u = True
  v = True
  w = True
  z = True

print((x +- y if not u and v else 0))
"""

# prog = """
# pyc_temp_var_0 = input_int()
# pyc_temp_var_3 = 42 if (input_int() == 0 if pyc_temp_var_0 == 1 else input_int() == 2) else 777
# print(pyc_temp_var_3)
# """

# pyc_temp_var_0 = input_int()
# pyc_temp_var_3 = (10 + 32 if (let Name('pyc_temp_var_1') = Call(Name('input_int'), []) in Compare(Name('pyc_temp_var_1'), [Eq()], [Constant(0)]) if pyc_temp_var_0 == 1 else let Name('pyc_temp_var_2') = Call(Name('input_int'), []) in Compare(Name('pyc_temp_var_2'), [Eq()], [Constant(2)])) else 700 + 77)
# print(pyc_temp_var_3)

# prog = """
# pyc_temp_var_0 = (42 if 2 > 1 else 0)
# print(pyc_temp_var_0)
# """

# prog = """
# x = 1
# y = 1
# if False or x!= y and x == y or True:
#   u = x < y
#   v = x <= y
#   w = x > y
#   z = x >= y
# else:
#   u = True
#   v = True
#   w = True
#   z = True

# print((x +- y if not u and v else 0))
# """

# test program here
# prog = """
# a = 20 + - 30
# b = input_int() + 10 + 20
# print(a + b + 60)
# """

# prog = """
# v = 1
# w = 42
# x = v + 7
# y = x
# z = x + w
# print(z + -y )
# """

# prog = """
# x = input_int()
# y = input_int()
# print(x + -y)
# """

# prog = """
# a = 5
# b = 30
# c = a
# b = 10
# c = c + b
# """

# prog = """
# x1 = input_int()
# x2 = input_int()
# x3 = input_int()
# x4 = input_int()
# x5 = input_int()
# x6 = input_int()
# x7 = input_int()
# x8 = input_int()
# x9 = input_int()
# x10 = input_int()
# x11 = input_int()
# x12 = input_int()
# x13 = input_int()
# x14 = input_int()
# x15 = input_int()
# x16 = input_int()
# print(x1 + - x2 + x3 + - x4 + x5 + - x6 + x7 + - x8 + x9 + - x10 + x11 + - x12 + x13 + - x14 + x15 + - x16 + 42)
# """

interp = interp_Pif.InterpPif()
# interp = interp_Pvar.InterpPvar()

p = parse(prog)

print("\n======= AST of the original program")
print(p)

type_check_Pif.TypeCheckPif().type_check_P(p)
print("\n======= type check passes")

print("\n======= interpreting original program")
interp.interp_P(p)

print("\n======= interpreting RCOed program")
compiler = Compiler()
p_rcoed = compiler.remove_complex_operands(p)
interp.interp_P(p_rcoed)

print("\n======= printing RCOed program")
print(p_rcoed)

print("\n======= explicate control")
print("\n======= printing EXPed program")
p_exped = compiler.explicate_control(p_rcoed)
print(p_exped)

print("\n======= interpreting EXPed program")
cif_interp = interp_Cif.InterpCif()
cif_interp.interp_C(p_exped)

print("\n======= selecting instructions")
p_x64 = compiler.select_instructions(p_exped)
print(p_x64)

print("\n======= evaluating x86 program")
eval_x86.interp_x86(p_x64)

print("\n======= uncovering live after sets")
las = compiler.uncover_live(p_x64_var)
for s in p_x64_var.body:
    print(repr(s) + '\t' + str(las[s]))

print("\n======= building interference graph")
las_list = compiler.uncover_live(p_x64_var, True)
rv = compiler.build_interference(p_x64_var.body, las_list)
print(compiler.int_graph.show())

print("\n======= building move graph")
rv = compiler.build_move_graph(p_x64_var.body)
print(compiler.move_graph.show())

print("\n======= graph coloring")
coloring = compiler.color_graph(compiler.int_graph)
print(coloring)

print("\n======= assigning homes")
p_x64_stack = compiler.assign_homes(p_x64_var)
print(p_x64_stack)

print("\n======= patching instructions")
p_x64_int = compiler.patch_instructions(p_x64_stack)
print(p_x64_int)
