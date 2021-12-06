from ast import *
from compiler import *
from utils import repr_Module
import type_check_Lfun
import type_check_Cfun
import interp_Lfun
import interp_Cfun

from interp_x86 import eval_x86

prog = """

t1 = (1,(44,))



# prog ="""
# x = input_int()
# y = input_int()
# if ((True if x == y else True) if (True if False else x != y) else False):
#   u = x < y
#   v = x < y
#   w = x > y
#   z = x >= y
# else:
#   u = True
#   v = True
#   w = True
#   z = True
# pyc_temp_var_0 = (v if u else False)
# pyc_temp_var_1 = (x - y if not pyc_temp_var_0 else 0)
# print(pyc_temp_var_1)
# """

# prog = """
# while False:
#   input_int()
#   print(1)
# print(42)
# """

# prog = """
# sum = 0
# m = 3
# n = 4
# i = 1
# while i < m:
#     j = 1
#     while j < n:
#         sum = sum + i + j
#         j = j + 1
#     i = i + 1
# print(sum)
# """

# prog = """
# x = 0
# while (True if input_int() == 5 else False):
#     x = x + 42
# print(x)
# """

# prog = """
# a = 1

# if a == 1:
#     b = 2
# else:
#     b = 3

# print(b)
# """

# prog = """
# x = 42
# y = 0
# if False or x!= y and x == y or True:
#     u = x < y
#     v = x <= y
#     w = x > y
#     z = x >= y
# else:
#     u = True
#     v = True
#     w = True
#     z = True
# print((x - y if not u and v else 0))
# """

# prog = """
# x = input_int()
# pyc_temp_var_0 = x == 1
# if not pyc_temp_var_0:
#   if x == 0:
#     y = 42
#   else:
#     y = 777

# else:
#   y = 0

# print(y)
# """


# prog = """
# pyc_temp_var_0 = input_int()
# pyc_temp_var_3 = 42 if (input_int() == 0 if pyc_temp_var_0 == 1 else input_int() == 2) else 777
# print(pyc_temp_var_3)
# """


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

interp = interp_Lfun.InterpLfun()
# interp = interp_Pvar.InterpPvar()

p = parse(prog)

print("\n======= AST of the original program")
print(p)

type_check_Lfun.TypeCheckLfun().type_check(p)
print("\n======= type check passes")

# print("\n======= interpreting original program")
# interp.interp(p)

compiler = Compiler()

print("\n======= shrinked program")
p_shrinked = compiler.shrink(p)
print(p_shrinked)
print("\n======= interpreting shrinked program")
interp.interp(p_shrinked)

print("\n======= reveal functions")
p_revealed = compiler.reveal_functions(p_shrinked)
print(p_revealed)

print("\n======= reveal functions AST")
print(ast.dump(p_revealed))

print("\n======= interpreting revealed functions program")
interp.interp(p_revealed)

print("\n======= limit functions")
p_limited = compiler.limit_functions(p_revealed)
print(p_limited)

print("\n======= limit functions AST")
print(ast.dump(p_limited))

print("\n======= interpreting limit functions program")
interp.interp(p_limited)

type_check_Lfun.TypeCheckLfun().type_check(p_limited)

p_rcoed = compiler.remove_complex_operands(p_limited)

print("\n======= RCOed program AST")
print(ast.dump(p_rcoed))

print("\n======= printing RCOed program")
print(p_rcoed)

print("\n======= interpreting RCOed program")
interp.interp(p_rcoed)


print("\n======= explicate control")
print("\n======= printing EXPed program")
p_exped = compiler.explicate_control(p_rcoed)
print(p_exped)

print("\n======= type checking EXPed program")
type_check_Cfun.TypeCheckCfun().type_check(p_exped)


print("\n======= interpreting EXPed program")
cif_interp = interp_Cfun.InterpCfun()
cif_interp.interp(p_exped)

print("\n======= selecting instructions")
p_x64 = compiler.select_instructions(p_exped)
print(p_x64)

# print("\n======= evaluating x86 program")
# eval_x86.interp_x86(p_x64)

print("\n======= uncovering live after sets")
las = compiler.uncover_live(p_x64)
for (label, block) in p_x64.body.items():
    print(label)
    for s in block:
        print(repr(s) + '\t' + str(las[s]))

print("\n======= building interference graph")
las_dict = compiler.uncover_live(p_x64)
rv = compiler.build_interference(las_dict)
print(compiler.int_graph.show())

print("\n======= building move graph")
rv = compiler.build_move_graph(p_x64.body)
print(compiler.move_graph.show())

print("\n======= graph coloring")
coloring = compiler.color_graph(compiler.int_graph)
print(coloring)

print("\n======= assigning homes")
p_x64_reg = compiler.assign_homes(p_x64)
print(p_x64_reg)

# print("\n======= evaluating x86 program")
# eval_x86.interp_x86(p_x64_reg)

print("\n======= patching instructions")
p_x64_patched = compiler.patch_instructions(p_x64_reg)
print(p_x64_patched)

print("\n======= geenrating prelude and conclusion")
p_x64_final = compiler.prelude_and_conclusion(p_x64_patched)
print(p_x64_final)

# print("\n======= evaluating x86 program")
# eval_x86.interp_x86(p_x64_final)

