import ast
from ast import *
from utils import *
from x86_ast import *
import os
from typing import List, Tuple, Set, Dict

# Type notes
Binding = Tuple[Name, expr]
Temporaries = List[Binding]


class Compiler:
    temp_count: int = 0
    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr, Temporaries]:

        def is_atm(e: expr):
            """helper function to check if `e` is an `atm` """
            match e:
                case Constant(_):
                    return True
                case Name(_):
                    return True
            return False

        temps = []
        # tail must be assigned in the match cases
        if is_atm(e):
            """nothing need to do if it's already an `atm`"""
            return (e, temps)

        match e:
            case UnaryOp(USub(), exp):
                if is_atm(exp):
                    tail = e
                else:
                    (atm, temps) = self.rco_exp(exp, True)
                    tail = UnaryOp(USub(), atm)
            case BinOp(exp1, Add(), exp2):
                if is_atm(exp1):
                    (exp1_atm, exp1_temps) = (exp1, [])
                else:
                    (exp1_atm, exp1_temps) = self.rco_exp(exp1, True)

                if is_atm(exp2):
                    (exp2_atm, exp2_temps) = (exp2, [])
                else:
                    (exp2_atm, exp2_temps) = self.rco_exp(exp2, True)

                tail = BinOp(exp1_atm, Add(), exp2_atm)
                temps = exp1_temps + exp2_temps
            case Call(Name('input_int'), []):
                tail = e

        if need_atomic:
            var = Name("pyc_temp_var_" + str(self.temp_count))
            temps.append((var, tail))
            self.temp_count += 1
            tail = var

        return (tail, temps)

    def rco_stmt(self, s: stmt) -> List[stmt]:
        result = []
        temps = []
        match s:
            case Expr(Call(Name('print'), [exp])):
                (atm, temps) = self.rco_exp(exp, True)
                tail = Expr(Call(Name('print'), [atm]))
            case Expr(exp):
                (exp_rcoed, temps) = self.rco_exp(exp, False)
                tail = Expr(exp_rcoed)
            case Assign([Name(var)], exp):
                (exp_rcoed, temps) = self.rco_exp(exp, False)
                tail = Assign([Name(var)], exp_rcoed)

        for binding in temps:
            result.append(Assign([binding[0]], binding[1]))

        result.append(tail)
        return result

    def remove_complex_operands(self, p: Module) -> Module:
        match p:
            case Module(stmts):
                new_stmts = [new_stat for s in stmts for new_stat in self.rco_stmt(s)]
                return Module(new_stmts)

    ############################################################################
    # Select Instructions
    ############################################################################
    
    def select_arg(self, e: expr) -> arg:
        match e:
            case Constant(c):
                return Immediate(c)
            case Name(var):
                return e

    def select_expr(self, e: expr) -> List[instr]:
        instrs = []
        match e:
            case Call(Name('input_int'), []):
                instrs.append(Callq("read_int", 0))
                instrs.append(Instr('movq', [Reg('rax'), Name("Unnamed_Pyc_Var")]))
            case UnaryOp(USub(), atm):
                instrs.append(Instr('negq', [Name("Unnamed_Pyc_Var")]))
            case BinOp(atm1, Add(), atm2):
                # TODO: optimize when the oprand and destination is the same
                # if isinstance(atm1, Name):
                #     (atm1, atm2) = (atm2, atm1)
                # if isinstance(atm2, Name):
                #     instrs.append(Instr('addq', [select_arg, Name("Unbounded_Pyc_Var")]))
                instrs.append(Instr('movq', [self.select_arg(atm1), Name("Unnamed_Pyc_Var")]))
                instrs.append(Instr('addq', [self.select_arg(atm2), Name("Unnamed_Pyc_Var")]))
        
        return instrs


    def select_stmt(self, s: stmt) -> List[instr]:

        def bound_unamed(instrs: List[instr], var: str) -> List[instr]:
            new_instrs = []
            for i in instrs:
                match i:
                    case Instr(oprtr, args):
                        new_args = [Name(var) if a == Name("Unnamed_Pyc_Var") else a for a in args]
                        new_instrs.append(Instr(oprtr, new_args))
            
            return new_instrs
                            
        instrs = []
        match s:
            case Expr(Call(Name('print'), [atm])):
                instrs.append(Instr('movq', [self.select_arg(atm), Reg('rdi')]))
                instrs.append(Callq("print_int", 1))
            case Expr(exp):
                instrs += self.select_expr(exp)
            case Assign([Name(var)], exp):
                instrs += bound_unamed(self.select_expr(exp), var)
        
        return instrs
        

    def select_instructions(self, p: Module) -> X86Program:
        match p:
            case Module(stmts):
                insts = [inst for s in stmts for inst in self.select_stmt(s)]
                return X86Program(insts)

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:
        # YOUR CODE HERE
        pass

    def assign_homes_instr(self, i: instr,
                           home: Dict[location, arg]) -> instr:
        # YOUR CODE HERE
        pass

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[location, arg]) -> List[instr]:
        # YOUR CODE HERE
        pass

    def assign_homes(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        # YOUR CODE HERE
        pass

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        # YOUR CODE HERE
        pass

    def patch_instructions(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        # YOUR CODE HERE
        pass
