# import from parent directory
# ref: https://www.geeksforgeeks.org/python-import-from-parent-directory/
import sys
import os
current = os.path.dirname(os.path.realpath(__file__))
parent = os.path.dirname(current)
sys.path.append(parent)

from interp_Pvar import InterpPvar
from utils import repr_Module
from type_check_Pvar import TypeCheckPvar

from pe import Lvar_pe
from ast import *

def test_program(p: str):

    print("===== program:")
    p = parse(p)
    print(repr_Module(p))

    checker = TypeCheckPvar()
    checker.type_check_P(p)
    print("===== type checking...Pass!")

    print("===== partial evaluator result:")
    pe = Lvar_pe()
    peed = pe.pe_evaluate(p)
    print(peed)

    print("===== Original interpreter result")
    ori_inter = InterpPvar()
    ori_inter.interp_P(p)

    print("===== PEed interpreter result")
    pe_inter = InterpPvar()
    pe_inter.interp_P(peed)

prog1 = """
a = - 30
b = input_int()
c = 22 + 33 + b + a
d = a + 44
print(c + d)
"""

test_program(prog1)

# test_program(prog2)

# test_program(prog3)
