import os
import sys
import compiler
import interp_Pvar
import type_check_Pvar
import interp_Llambda
import type_check_Llambda
import interp_Clambda
import type_check_Clambda
from utils import run_tests, run_one_test, enable_tracing

compiler = compiler.Compiler()
enable_tracing() #comment this to see less information in the output
arg = sys.argv[1]
run_tests(arg, compiler, arg, type_check_Llambda.TypeCheckLlambda().type_check, interp_Llambda.InterpLlambda().interp,type_check_Clambda.TypeCheckClambda().type_check, interp_Clambda.InterpClambda().interp)


""" if False:
    run_one_test(os.getcwd() + '/tests/var/zero.py', 'var',
                 compiler, 'var',
                 type_check_Pvar.TypeCheckPvar().type_check_P,
                 interp_Pvar.InterpPvar().interp_P,
                 None)
else:
    run_tests('var', compiler, 'var',
              type_check_Pvar.TypeCheckPvar().type_check_P,
              interp_Pvar.InterpPvar().interp_P,
              None) """