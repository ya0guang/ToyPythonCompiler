# import from parent directory
# ref: https://www.geeksforgeeks.org/python-import-from-parent-directory/
import sys
import os
current = os.path.dirname(os.path.realpath(__file__))
parent = os.path.dirname(current)
sys.path.append(parent)

from interp_Pint import interp_P
from utils import repr_Module
from utils import input_int

from pe import pe_P_int
from ast import *

def test_program(p: str):
    print("===== program:")
    p = parse(p)
    print(repr_Module(p))

    print("===== partial evaluator result:")
    pe1 = pe_P_int(p)
    print(pe1)

    print("===== interpreter result:")
    interp_P(p)

prog1 = """
print(10 + 30)
"""

prog2 = """
print(input_int() + 10)
"""

prog3 = """
print((input_int() + 22) + (-10 + 22))
"""

test_program(prog1)

test_program(prog2)

test_program(prog3)
