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
    # used for tracking static stack usage
    stack_count: int = 0
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
                return Variable(var)

    def select_expr(self, e: expr) -> List[instr]:
        instrs = []
        match e:
            case Call(Name('input_int'), []):
                instrs.append(Callq('read_int', 0))
                instrs.append(Instr('movq', [Reg('rax'), Variable("Unnamed_Pyc_Var")]))
            case UnaryOp(USub(), atm):
                instrs.append(Instr('movq', [self.select_arg(atm), Variable("Unnamed_Pyc_Var")]))
                instrs.append(Instr('negq', [Variable("Unnamed_Pyc_Var")]))
            case BinOp(atm1, Add(), atm2):
                # TODO: optimize when the oprand and destination is the same
                # if isinstance(atm1, Name):
                #     (atm1, atm2) = (atm2, atm1)
                # if isinstance(atm2, Name):
                #     instrs.append(Instr('addq', [select_arg, Name("Unbounded_Pyc_Var")]))
                instrs.append(Instr('movq', [self.select_arg(atm1), Variable("Unnamed_Pyc_Var")]))
                instrs.append(Instr('addq', [self.select_arg(atm2), Variable("Unnamed_Pyc_Var")]))
            case _:
                instrs.append(Instr('movq', [self.select_arg(e), Variable("Unnamed_Pyc_Var")]))

        
        return instrs


    def select_stmt(self, s: stmt) -> List[instr]:

        def bound_unamed(instrs: List[instr], var: str) -> List[instr]:
            new_instrs = []
            for i in instrs:
                match i:
                    case Instr(oprtr, args):
                        new_args = [Variable(var) if a == Variable("Unnamed_Pyc_Var") else a for a in args]
                        new_instrs.append(Instr(oprtr, new_args))
                    case wild:
                        new_instrs.append(wild)
            
            return new_instrs
                            
        instrs = []
        match s:
            # TODO: may delete all instructions containing `Variable("Unnamed_Pyc_Var")``
            case Expr(Call(Name('print'), [atm])):
                instrs.append(Instr('movq', [self.select_arg(atm), Reg('rdi')]))
                instrs.append(Callq('print_int', 1))
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
        
        if a in home.keys():
            return home[a]
        else:
            return a

    def assign_homes_instr(self, i: instr,
                           home: Dict[location, arg]) -> instr:
        match i:
            case Instr(oprtr, args):
                new_args = []
                for a in args:
                    new_args.append(self.assign_homes_arg(a, home))
                return Instr(oprtr, new_args)
            case other:
                return other

    def assign_homes_instrs(self, ss: List[instr],
                            home: Dict[location, arg]) -> List[instr]:
        new_ins = []
        for i in ss:
            new_ins.append(self.assign_homes_instr(i, home))
        
        return new_ins
        

    def assign_homes(self, p: X86Program) -> X86Program:
        
        def extract_var(ins: instr) -> List[Variable]:
            var_list = []
            match ins:
                case Instr(_, args):
                    for a in args:
                        if isinstance(a, Variable):
                            var_list.append(a)
            return var_list

        var_set = set([])
        if type(p.body) == dict:
            pass
        else: # list
            for s in p.body:
                var_set.update(extract_var(s))
        self.stack_count = len(var_set)

        home = {}
        assigned_homes = 0
        for v in var_set:
            home[v] = Deref("rbp", - (assigned_homes + 1) * 8)
            assigned_homes += 1
        
        # print(home)

        if type(p.body) == dict:
            pass
        else: # list
            return X86Program(self.assign_homes_instrs(p.body, home))
            

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        patched_instrs = []
        match i:
            case Instr("movq", [Deref(reg1, offset1), Deref(reg2, offset2)]):
                # MOV: Two memory locations in args
                patched_instrs.append(Instr("movq", [Deref(reg1, offset1), Reg("rax")]))
                patched_instrs.append(Instr("movq", [Reg("rax"), Deref(reg2, offset2)]))
            case Instr("addq", [Deref(reg1, offset1), Deref(reg2, offset2)]):
                # ADD: Two memory locations in args
                patched_instrs.append(Instr("movq", [Deref(reg1, offset1), Reg("rax")]))
                patched_instrs.append(Instr("addq", [Reg("rax"), Deref(reg2, offset2)]))
            case _:
                patched_instrs.append(i)
        
        return patched_instrs

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        new_instrs = []
        for i in ss:
            new_instrs += self.patch_instr(i)
        
        return new_instrs

    def patch_instructions(self, p: X86Program) -> X86Program:

        if type(p.body) == dict:
            pass
        else: # list
            return X86Program(self.patch_instrs(p.body))

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        stack_frame_size = ((self.stack_count + 1) // 2) * 16

        prelude = []
        prelude.append(Instr('pushq', [Reg('rbp')]))
        prelude.append(Instr('movq', [Reg('rsp'), Reg('rbp')]))
        prelude.append(Instr('subq', [Immediate(stack_frame_size), Reg('rsp')]))


        conclusion = []
        conclusion.append(Instr('addq', [Immediate(stack_frame_size), Reg('rsp')]))
        conclusion.append(Instr('popq', [Reg('rbp')]))
        conclusion.append(Instr('retq', []))
            
        if type(p.body) == dict:
            pass
        else: # list
            return X86Program(prelude + p.body + conclusion)