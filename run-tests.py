import os
import compiler
import interp_Pvar
import type_check_Pvar
import interp_Llambda
import type_check_Llambda
import interp_Clambda
import type_check_Clambda
from utils import run_tests, run_one_test

compiler = compiler.Compiler()
run_tests('lambda', compiler, 'lambda', type_check_Llambda.TypeCheckLlambda().type_check, interp_Llambda.InterpLlambda().interp,type_check_Clambda.TypeCheckClambda().type_check, interp_Clambda.InterpClambda().interp)


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