# tester program: https://github.com/ya0guang/ToyPythonCompiler/tree/main/L_var/test_pe.py

from ast import *
from typing import List, Tuple, Set, Dict

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
