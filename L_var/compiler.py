import ast
from ast import *
from utils import *
from x86_ast import *
import os
from typing import List, Tuple, Set, Dict

# Type notes
Binding = Tuple[Name, expr]
Temporaries = List[Binding]

# Challenges: Partial Evaluator
# A small tester can be found here: https://github.com/ya0guang/ToyPythonCompiler/blob/main/L_var/test_pe.py

class Lvar_pe:

    env: Dict = {}
    new_body: List = []

    def equivalent(self, newer_body: List) -> bool:
        if len(newer_body) != len(self.new_body):
            return False
        for i in range(len(newer_body)):
            # print("DEBUG:", repr(self.new_body[i]))
            # print("DEBUG:", repr(newer_body[i]))
            # print("DEBUG: type: ", type(repr(newer_body[i])))
            if repr(self.new_body[i]) != repr(newer_body[i]):
                return False
        return True

    def find(self, v: Name) -> Tuple[expr, bool]:
        """return the founded var and if the var is unbounded"""
        if not isinstance(v, Name):
            return (v, True)
        if v in self.env.keys():
            return (self.env[v], False)
        return (v, True)

    def pe_neg(self, r):
        (oprd, _) = self.find(r)
        match oprd:
            case Constant(n):
                return Constant(-n)
            case _:
                return UnaryOp(USub(), oprd)

    def pe_add(self, r1, r2):
        (oprd1, _) = self.find(r1)
        (oprd2, _) = self.find(r2)
        match (oprd1, oprd2):
            case (Constant(n1), Constant(n2)):
                return Constant(n1 + n2)
            case (op1, Constant(n2)):
                return BinOp(Constant(n2), Add(), op1)
            case _:
                return BinOp(oprd1, Add(), oprd2)

    def pe_exp(self, e: expr) -> Tuple[expr, bool]:
        """evaluate the expression according to the environment and tell the result and if the result contains unbound variable(s)"""
        match e:
            case BinOp(left, Add(), right):
                # print("DEBUG: add ast", e)
                # print("DEBUG: L:", left, "R:", right)
                (left_evaed, left_unresolved) = self.pe_exp(left)
                (right_evaed, right_unresolved) = self.pe_exp(right)
                return (self.pe_add(left_evaed, right_evaed), left_unresolved or right_unresolved)
            case UnaryOp(USub(), v):
                (v_evaed, v_bounded) = self.pe_exp(v)
                return (self.pe_neg(v_evaed), v_bounded)
            case Constant(_):
                return (e, False)
            case Call(Name('input_int'), []):
                return (e, True)
            case Name(var):
                # if self.find(var):
                #     return (self.find(var), False)
                return self.find(Name(var))

    def pe_stmt(self, s: stmt):
        """takes a statement, then add the PEed statement to new_body and modify environment"""
        match s:
            case Expr(Call(Name('print'), [arg])):
                (evaluated, _) = self.pe_exp(arg)
                self.new_body.append(Expr(Call(Name('print'), [evaluated])))
            case Expr(exp):
                (evaluated, unresolved) = self.pe_exp(exp)
                if unresolved:
                    self.new_body.append(Expr(evaluated))
            case Assign([Name(var)], exp):
                (evaluated, unresolved) = self.pe_exp(exp)
                if unresolved:
                    self.new_body.append(Assign([Name(var)], evaluated))
                else:
                    self.env[Name(var)] = evaluated
        
    def pe_evaluate(self, p: Module):
        iter_once = False
        match p:
            case Module(body):
                body_last = body
                while not self.equivalent(body_last):
                    """recursively perform transformation until no further optimization is needed"""
                    # print("DEBUG: equivalent", self.equivalent(body_last))
                    # print("DEBUG: last_body", body_last)
                    # print("DEBUG: self.body", self.new_body)
                    if iter_once:
                        body_last = parse(repr(Module(self.new_body))).body
                        self.new_body = []
                    for s in body_last:
                        self.pe_stmt(s)
                    iter_once = True
        
        return Module(self.new_body)



class Compiler:
    temp_count: int = 0
    # used for tracking static stack usage
    stack_count: int = 0

    ############################################################################
    # PE
    ############################################################################
    def partial_eval(self, p: Module) -> Module:
        pe = Lvar_pe()
        return pe.pe_evaluate(p)

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
            case Instr("movq", [Immediate(v), dest]):
                if v > 2147483647 or v < -2147483648: # not fit into 32-bit
                    # TODO: may need to check for `dest` for optimization
                    patched_instrs.append(Instr("movq", [Immediate(v), Reg("rax")]))
                    patched_instrs.append(Instr("movq", [Reg("rax"), dest]))
                else: 
                    patched_instrs.append(i)
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

