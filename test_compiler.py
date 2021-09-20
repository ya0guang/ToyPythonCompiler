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

prog = """
v = 1
w = 42
x = v + 7
y = x
z = x + w
print(z + -y )
"""

# prog = """
# a = 5
# b = 30
# c = a
# b = 10
# c = c + b
# """

# prog = """
# a = -1
# print(a)
# """

p = parse(prog)
type_check_Pvar.TypeCheckPvar().type_check_P(p)
print("\n======= type check passes")

print("\n======= interpreting original program")
interp = interp_Pvar.InterpPvar()
interp.interp_P(p)

print("\n======= interpreting RCOed program")
compiler = Compiler()
p_rcoed = compiler.remove_complex_operands(p)
interp.interp_P(p_rcoed)
print("\n======= printing RCOed program")
print(p_rcoed)

print("\n======= selecting instructions")
p_x64_var = compiler.select_instructions(p_rcoed)
print(p_x64_var)

print("\n======= uncovering live after sets")
las = compiler.uncover_live(p_x64_var)
for s in p_x64_var.body:
    print(repr(s) + '\t' + str(las[s]))

print("\n======= building inference graph")
las_list = compiler.uncover_live(p_x64_var, True)
inf_graph = compiler.build_interference(p_x64_var.body, las_list)
print(inf_graph.show())

print("\n======= graph coloring")
coloring = compiler.color_graph(inf_graph)
print(coloring)

print("\n======= assigning homes")
p_x64_stack = compiler.assign_homes(p_x64_var)
print(p_x64_stack)

print("\n======= patching instructions")
p_x64_int = compiler.patch_instructions(p_x64_stack)
print(p_x64_int)
