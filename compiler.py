import ast
from ast import *
from utils import *
from x86_ast import *
from graph import *
from collections import deque
from priority_queue import *
import os
import types
from functools import *
from typing import List, Set, Dict
import typing

# Type notes
Binding = typing.Tuple[Name, expr]
Temporaries = List[Binding]

# Global register categorization

# Register used for argument passing
arg_passing = ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9', ]
caller_saved = arg_passing + ['rax', 'r10', 'r11']
callee_saved = ['rsp', 'rbp', 'rbx', 'r12', 'r13', 'r14', 'r15']

# Allocatable registers = all - rsp - rbp - rax - r11 - r15
allocatable = callee_saved + caller_saved

# TODO: use a list: reserved_regs = ['rsp', 'rbp', 'rbx', 'rax', 'r11', 'r15']
allocatable.remove('rsp')
allocatable.remove('rbp')
allocatable.remove('rax')
allocatable.remove('r11')
allocatable.remove('r15')


def force(promise):
    if isinstance(promise, types.FunctionType):
        return force(promise())
    else:
        return promise


def analyze_dataflow(G: DirectedAdjList, transfer: FunctionType, bottom, join: FunctionType):
    """return a mapping from vertices in G to their dataflow result"""
    trans_G = transpose(G)
    mapping = {}
    for v in G.vertices():
        mapping[v] = bottom
    worklist = deque()
    for v in G.vertices():
        worklist.append(v)
    while worklist:
        node = worklist.pop()
        input = reduce(join, [mapping[v] for v in G.out[node]], bottom)
        # input = reduce(join, [mapping[v] for v in trans_G.adjacent(node)], bottom)
        output = transfer(node, input)
        if output != mapping[node]:
            mapping[node] = output
            # for v in G.adjacent(node):
            for v in G.ins[node]:
                worklist.append(v)

    return mapping


class Compiler:
    """compile the whole program, and for each function, call methods in `CompileFunction`"""

    # TODO: How to ref CompileFunction.arg_passing?
    # num_arg_passing_regs = len(CompileFunction.arg_passing)
    num_arg_passing_regs = 6

    def __init__(self):
        self.functions = []
        # function -> CompileFunction instance
        self.function_compilers = {}
        # function -> {original_name: new_name}
        self.function_limit_renames = {}
        self.num_uniquified_counter = 0
        

    def shrink(self, p: Module) -> Module:
        """create main function, making the module body a series of function definitions"""
        assert(isinstance(p, Module))
        # main_args = arguments([], [], [], [], [])
        main = FunctionDef('main', args=[], body=[],
                           decorator_list=[], returns=int)

        new_module = []
        for c in p.body:
            match c:
                case FunctionDef(name, _args, _body, _deco_list, _rv_type):
                    new_module.append(c)
                    self.functions.append(name)
                    # print("DEBUG, function: ", name, "args: ", args.args, body, _deco_list, _rv_type)
                case stmt():
                    main.body.append(c)

        main.body.append(Return(Constant(0)))
        new_module.append(main)
        print("DEBUG, new module: ", new_module)
        return Module(new_module)

    def uniquify(self, p: Module) -> Module:

        class Uniquify(NodeTransformer):
            
            def __init__(self, outer: Compiler, mapping: dict):
                self.outer_instance = outer
                self.uniquify_mapping = mapping
                super().__init__()

            def visit_Lambda(self, node):
                self.generic_visit(node)
                match node:
                    case Lambda(args, body_expr):
                        new_mapping = self.uniquify_mapping.copy()
                        new_args = []
                        for v in args:
                            new_v = v + "_" + str(self.outer_instance.num_uniquified_counter)
                            # find the new name in the previous mapping
                            new_mapping[new_mapping[v]] = new_v
                            # delete the old mapping
                            del new_mapping[v]
                            new_args.append(new_v)
                            self.outer_instance.num_uniquified_counter += 1
                        new_uniquifier = Uniquify(self.outer_instance, new_mapping)
                        new_body_expr = new_uniquifier.visit(body_expr)
                        return Lambda(new_args, new_body_expr)
                    case _:
                        return node

            def visit_Name(self, node):
                self.generic_visit(node)
                match node:
                    case Name(id):
                        if id in self.uniquify_mapping:
                            return Name(self.uniquify_mapping[id])
                        else:
                            return node
                    case _:
                        return node

        
        def do_uniquify(stmts: list, uniquify_mapping: dict) -> list:
            """change the variable names of statements in place according to the uniquify_mapping"""
            uniquifier = Uniquify(self, uniquify_mapping)
            new_body = []
            for s in stmts:
                new_body.append(uniquifier.visit(s))
            return new_body
        
        assert(isinstance(p, Module))

        for f in p.body:
            uniquify_mapping = {}
            new_args = []
            for v in f.args:
                print("DEBUG, v: ", v[0], "type: ", type(v[0]))
                new_arg_name = v[0] + "_" + str(self.num_uniquified_counter)
                uniquify_mapping[v[0]] = new_arg_name
                new_args.append((new_arg_name, v[1], ))
                self.num_uniquified_counter += 1
            f.args = new_args
            f.body = do_uniquify(f.body, uniquify_mapping)
        
        return p

    def reveal_functions(self, p: Module) -> Module:
        """change `Name(f)` to `FunRef(f)` for functions defined in the module"""

        class RevealFunction(NodeTransformer):

            def __init__(self, outer: Compiler):
                self.outer_instance = outer
                super().__init__()

            def visit_Name(self, node):
                self.generic_visit(node)
                match node:
                    case Name(f) if f in self.outer_instance.functions:
                        # TODO: iterable `FunRef`
                        # what if f is a builtin function? guard needed
                        self.generic_visit(node)
                        return FunRef(f)
                    case _:
                        return node

        assert(isinstance(p, Module))
        # Why this does't work?
        # new_body = RevealFunction(self).visit_Call(p)
        # p.body = new_body

        for f in p.body:
            new_body = []
            for s in f.body:
                new_line = RevealFunction(self).visit_Name(s)
                new_body.append(new_line)
                # print("DEBUG, new node: ", ast.dump(n))
            f.body = new_body

        return p

    def limit_functions(self, p: Module) -> Module:
        """limit functions to 6 arguments, anything more gets put into a 6th tuple-type argument"""

        class LimitFunction(NodeTransformer):
            # limit call sites & convert name of args

            def __init__(self, outer: Compiler, mapping: dict = {}):
                self.outer_instance = outer
                self.mapping = mapping
                super().__init__()

            def visit_Name(self, node):
                # substitute the >5th arguments with subscript of a tuple
                self.generic_visit(node)
                match node:
                    case Name(n) if n in self.mapping.keys():
                        return self.mapping[n]
                    case _:
                        return node

            def visit_Call(self, node):
                self.generic_visit(node)
                match node:
                    case Call(FunRef(f), args) if len(args) > Compiler.num_arg_passing_regs:
                        # print("DEBUG, HIT in visit_FunRef: ", ast.dump(node))
                        new_args = args[:Compiler.num_arg_passing_regs - 1]
                        new_args.append(
                            Tuple(args[Compiler.num_arg_passing_regs - 1:], Load()))
                        return Call(FunRef(f), new_args)
                    case _:
                        return node

        def args_need_limit(args):
            if isinstance(args, list):
                # print("DEBUG, args: ", args, type(args))
                # print("DEBUG, argsAST: ", args[1][0])
                return len(args) > Compiler.num_arg_passing_regs
            # else:
                # print("DEBUG, args: ", ast.dump(args))
            return False

        assert(isinstance(p, Module))
        # limit defines
        for f in p.body:
            match f:
                case FunctionDef(_name, args, _body, _deco_list, _rv_type) if args_need_limit(args):
                    # args = args.args
                    new_args = args[:5]
                    arg_tup = ('tup_arg', TupleType([a[1] for a in args[5:]]))
                    alias_mapping = {}
                    for i in range(5, len(args)):
                        # TODO: How is this allocated on the heap or appears in shadow stack?
                        # print("DEBUG, dump arg[i]: ", ast.dump(args.args[i]))
                        alias_mapping[args[i][0]] = Subscript(
                            Name('tup_arg'), Constant(i - 5), Load())
                    print("DEBUG, alias_mapping: ", alias_mapping)
                    new_args.append(arg_tup)
                    print("DEBUG, new_args: ", new_args)
                    f.args = new_args
                    new_body = []
                    for s in f.body:
                        # new_line is new node
                        new_line = LimitFunction(
                            self, alias_mapping).visit_Name(s)
                        print("DEBUG, new_line: ", new_line)
                        new_body.append(new_line)
                    print("DEBUG, new_body: ", new_body)
                    f.body = new_body
                case _:
                    assert(isinstance(f, FunctionDef))
                    new_body = []
                    for s in f.body:
                        new_line = LimitFunction(self).visit_Call(s)
                        new_body.append(new_line)
                    f.body = new_body

        # force the autograder to re-evaluate the types in function definition
        # should be removed in production
        import type_check_Llambda
        type_check_Llambda.TypeCheckLlambda().type_check(p)
        return p

    def remove_complex_operands(self, p: Module) -> Module:
        assert(isinstance(p, Module))
        for f in p.body:
            assert(isinstance(f, FunctionDef))
            self.function_compilers[f.name] = CompileFunction(f.name)
            f.body = self.function_compilers[f.name].remove_complex_operands(
                Module(f.body))
        return p

    def explicate_control(self, p: Module) -> CProgramDefs:
        match p:
            case Module(defs):
                for f in p.body:
                    assert(isinstance(f, FunctionDef))
                    f.body = self.function_compilers[f.name].explicate_control(
                        Module(f.body))
                return CProgramDefs(p.body)

    def select_instructions(self, p: CProgramDefs) -> X86ProgramDefs:
        assert(isinstance(p, CProgramDefs))
        for f in p.defs:
            assert(isinstance(f, FunctionDef))
            # select instructions
            f.body = self.function_compilers[f.name].select_instructions(
                CProgram(f.body))
            new_start_block = []
            i = 0
            # add instr to move each register into arg in at the beginning of the block
            for arg in f.args:
                match arg[0]:
                    case var if isinstance(var, str):
                        new_start_block.append(
                            Instr('movq', [Reg(arg_passing[i]), Variable(var)]))
                        i += 1
                    case Default:
                        print("DEBUG in selecting ARG: " + str(type(arg[0])))
            # fix the block
            new_start_block += f.body[f.name + "start"]
            f.body[f.name + "start"] = new_start_block
            # fix function definition
            f.args = []
            # TODO: why?
            f.returns = int

        return X86ProgramDefs(p.defs)

    def assign_homes(self, p: X86ProgramDefs) -> X86ProgramDefs:
        # assert(isinstance(p, X86ProgramDefs))
        # for f in p.defs:
        #     assert(isinstance(f, FunctionDef))
        #     f.body = self.function_compilers[f.name].select_instructions(X86Program(f.body))

        # print("finished assigning homes")
        # return X86ProgramDefs(p.defs)
        assert(isinstance(p, X86ProgramDefs))
        for f in p.defs:
            assert(isinstance(f, FunctionDef))
            f.body = self.function_compilers[f.name].assign_homes(
                X86Program(f.body))
        return X86ProgramDefs(p.defs)

    def patch_instructions(self, p: X86ProgramDefs) -> X86ProgramDefs:
        assert(isinstance(p, X86ProgramDefs))
        for f in p.defs:
            assert(isinstance(f, FunctionDef))
            f.body = self.function_compilers[f.name].patch_instructions(
                X86Program(f.body))
        return X86ProgramDefs(p.defs)

    def prelude_and_conclusion(self, p: X86ProgramDefs) -> X86Program:
        assert(isinstance(p, X86ProgramDefs))
        new_body = {}
        for f in p.defs:
            assert(isinstance(f, FunctionDef))
            f.body = self.function_compilers[f.name].prelude_and_conclusion(
                X86Program(f.body))
            # print("DEBUG, f.body: ", f.body)
            new_body.update(f.body)

        return X86Program(new_body)


class CompileFunction:
    """compile a single function"""

    temp_count: int = 0
    tup_temp_count: int = 0

    # used for tracking static stack usage
    normal_stack_count: int = 0
    shadow_stack_count: int = 0
    tuple_vars = []

    # `calllq`: include first `arg_num` registers in its read-set R
    arg_passing = [Reg(x) for x in arg_passing]
    # `callq`: include all caller_saved registers in write-set W
    caller_saved = [Reg(x) for x in caller_saved]

    callee_saved = [Reg(x) for x in callee_saved]

    builtin_functions = ['input_int', 'print', 'len']
    builtin_functions = [Name(i) for i in builtin_functions]

    def __init__(self, name: str):
        self.name = name
        self.basic_blocks = {}
        # mappings from a single instruction to a set
        self.read_set_dict = {}
        self.write_set_dict = {}
        self.live_before_set_dict = {}
        self.live_after_set_dict = {}
        # this list can be changed for testing spilling
        self.allocatable = [Reg(x) for x in allocatable]
        all_reg = [Reg('r11'), Reg('r15'), Reg('rsp'), Reg(
            'rbp'), Reg('rax')] + self.allocatable
        self.int_graph = UndirectedAdjList()
        self.move_graph = UndirectedAdjList()
        self.control_flow_graph = DirectedAdjList()
        self.live_before_block = {}

        self.prelude_label = self.name
        # assign this when iterating CFG
        self.conclusion_label = self.name + 'conclusion'
        self.basic_blocks[self.conclusion_label] = []
        # make the initial conclusion non-empty to avoid errors
        # TODO: come up with a more elegant solution, maybe from `live_before_block`
        # self.basic_blocks[self.conclusion_label] = [Expr(Call(Name('input_int'), []))]
        # why need this?
        self.sorted_control_flow_graph = []
        self.used_callee = set()
        self.stack_frame_size: int
        self.shadow_stack_size: int

        # Reserved registers
        self.color_reg_map = {}
        color_from = -5
        for reg in all_reg:
            self.color_reg_map[color_from] = reg
            color_from += 1

    def extend_reg(r: Reg) -> Reg:
        match r:
            case Reg(name) if len(name) == 3 and name[0] == 'r':
                return r
            case Reg(name) if len(name) == 3 and name[0] == 'e':
                return Reg('r' + name[1:])
            case Reg(name) if len(name) == 2:
                return Reg('r' + name[0] + 'x')
            case _:
                raise Exception(
                    'error in extend_reg, unsupported register name ' + repr(r))

    ############################################################################
    # Expose Allocation
    ############################################################################

    def expose_allocation_hide(self, t: Tuple) -> Begin:
        # Autograder call `expose_allocation` in a wrong way, so this is hidden from the autograder
        """convert a tuple creation into a begin"""
        assert(isinstance(t, Tuple))
        content = t.elts
        body = []

        for i in range(len(content)):
            if not CompileFunction.is_atm(content[i]):
                print("DEBUG: ???")
                temp_name = 'temp_tup' + \
                    str(self.tup_temp_count) + 'X' + str(i)
                body.append(Assign([Name(temp_name)], content[i]))

        tup_bytes = (len(content) + 1) * 8

        if_cond = Compare(BinOp(GlobalValue('free_ptr'), Add(), Constant(tup_bytes)), [
                          Lt()], [GlobalValue('fromspace_end')])

        # TODO: Expr(Constant(0)) OK here?
        body.append(If(if_cond, [], [Collect(tup_bytes)]))

        var = Name("pyc_temp_tup_" + str(self.tup_temp_count))
        body.append(Assign([var], Allocate(len(content), t.has_type)))

        for i in range(len(content)):
            if not CompileFunction.is_atm(content[i]):
                body.append(Assign([Subscript(var, Constant(i), Store())], Name(
                    'temp_tup' + str(self.tup_temp_count) + 'X' + str(i))))
            else:
                body.append(
                    Assign([Subscript(var, Constant(i), Store())], content[i]))

        self.tup_temp_count += 1
        return Begin(body, var)

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    def is_atm(e: expr):
        """helper function to check if `e` is an `atm` """
        match e:
            case Constant(c):
                return True
                return isinstance(c, bool) or isinstance(c, int)
            case Name(_):
                return True
        return False

    def letize(self, exp: expr) -> expr:
        """using `let`s to remove complex in an expression"""
        # TODO: also allow some `exp`s rather than atoms only
        (tail, temps) = self.rco_exp(exp, False)
        for var in reversed(temps):
            tail = Let(var[0], var[1], tail)
        return tail

    def rco_exp(self, e: expr, need_atomic: bool) -> typing.Tuple[expr, Temporaries]:

        temps = []
        # tail must be assigned in the match cases
        if CompileFunction.is_atm(e):
            """nothing need to do if it's already an `atm`"""
            return (e, temps)

        match e:
            # recursively call rco_exp on each op
            # shrink `and` & `or`
            case BoolOp(And(), args):
                return self.rco_exp(IfExp(args[0], args[1], Constant(False)), need_atomic)
            case BoolOp(Or(), args):
                return self.rco_exp(IfExp(args[0], Constant(True), args[1]), need_atomic)
            # call expose_allocation for tuple creation
            case Tuple(_, Load()):
                # TODO: may need to consider temps and bindings
                return self.rco_exp(self.expose_allocation_hide(e), need_atomic)
            case Begin(body, result):
                # TODO
                new_body = [
                    new_stat for s in body for new_stat in self.rco_stmt(s)]
                tail = Begin(new_body, result)
            case UnaryOp(uniop, exp):
                # `Not()` and `USub`
                if CompileFunction.is_atm(exp):
                    tail = e
                else:
                    (atm, temps) = self.rco_exp(exp, True)
                    tail = UnaryOp(uniop, atm)
            case BinOp(exp1, binop, exp2):
                """Sub() and Add()"""
                if CompileFunction.is_atm(exp1):
                    (exp1_atm, exp1_temps) = (exp1, [])
                else:
                    (exp1_atm, exp1_temps) = self.rco_exp(exp1, True)

                if CompileFunction.is_atm(exp2):
                    (exp2_atm, exp2_temps) = (exp2, [])
                else:
                    (exp2_atm, exp2_temps) = self.rco_exp(exp2, True)

                tail = BinOp(exp1_atm, binop, exp2_atm)
                temps = exp1_temps + exp2_temps
            case Compare(left, [cmp], [right]):
                # similar to `BinOp` case
                if CompileFunction.is_atm(left):
                    (left_atm, left_temps) = (left, [])
                else:
                    (left_atm, left_temps) = self.rco_exp(left, True)

                if CompileFunction.is_atm(right):
                    (right_atm, right_temps) = (right, [])
                else:
                    (right_atm, right_temps) = self.rco_exp(right, True)

                tail = Compare(left_atm, [cmp], [right_atm])
                temps = left_temps + right_temps
            case IfExp(exp_test, exp_body, exp_else):
                (tail, test_temps) = self.rco_exp(exp_test, False)
                tail = IfExp(tail, self.letize(
                    exp_body), self.letize(exp_else))
                temps = test_temps
            case Call(Name('input_int'), []):
                tail = e
            case Call(Name('len')):
                # TODO not sure if more needs to be done
                tail = e
            case GlobalValue(v):
                # TODO: create a temp to hold it
                tail = e
            case Allocate(len, type_list):
                # TODO: ???
                tail = e
            case Subscript(var, idx, Load()):
                (var_rcoed, var_temps) = self.rco_exp(var, True)
                (idx_rcoed, idx_temps) = self.rco_exp(idx, True)
                tail = Subscript(var_rcoed, idx_rcoed, Load())
                temps = var_temps + idx_temps
            case Call(funRef, args):
                (funRef_rcoed, funRef_temps) = self.rco_exp(funRef, True)
                print("DEBUG, in rco_exp, call match case: ", funRef_rcoed)
                args_rcoed = []
                args_temps = []
                for arg in args:  # make sure all args are atomic
                    (arg_rcoed, arg_temps) = self.rco_exp(arg, True)
                    args_rcoed.append(arg_rcoed)
                    args_temps += arg_temps
                tail = Call(funRef_rcoed, args_rcoed)
                temps = args_temps + funRef_temps
            case FunRef(f):
                tail = e
            case _:
                raise Exception(
                    'error in rco_exp, unsupported expression ' + repr(e))

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
                # Record all tuples here
                if isinstance(exp, Tuple):
                    print("DEBUG: hit tuple, ", var, type(var))
                    self.tuple_vars.append(var)
                (exp_rcoed, temps) = self.rco_exp(exp, False)
                tail = Assign([Name(var)], exp_rcoed)
            case If(exp, stmts_body, stmts_else):
                # need test
                (exp_rcoed, temps) = self.rco_exp(exp, False)
                body_rcoed = [
                    new_stat for s in stmts_body for new_stat in self.rco_stmt(s)]
                else_rcoed = [
                    new_stat for s in stmts_else for new_stat in self.rco_stmt(s)]
                tail = If(exp_rcoed, body_rcoed, else_rcoed)
            case While(exp, stmts_body, []):
                exp_rcoed = self.letize(exp)
                # (exp_rcoed, temps) = self.rco_exp(exp, False)
                body_rcoed = [
                    new_stat for s in stmts_body for new_stat in self.rco_stmt(s)]
                tail = While(exp_rcoed, body_rcoed, [])
            case Collect(bytes):
                # TODO: ???
                tail = s
            case Assign([Subscript(var, idx, Store())], exp):
                (var_rcoed, var_temps) = self.rco_exp(var, True)
                (idx_rcoed, idx_temps) = self.rco_exp(idx, True)
                (exp_rcoed, exp_temps) = self.rco_exp(exp, False)
                tail = Assign(
                    [Subscript(var_rcoed, idx_rcoed, Store())], exp_rcoed)
                temps = var_temps + idx_temps + exp_temps
            case Return(exp):
                (atm, temps) = self.rco_exp(exp, False)
                tail = Return(atm)
            case _:
                raise Exception(
                    'error in rco_stmt, stmt not supported ' + repr(s))

        for binding in temps:
            # print("DEBUG, binding: ", binding)
            result.append(Assign([binding[0]], binding[1]))

        result.append(tail)
        return result

    def remove_complex_operands(self, p: Module) -> List:
        match p:
            case Module(stmts):
                new_stmts = [
                    new_stat for s in stmts for new_stat in self.rco_stmt(s)]
                return new_stmts

    ############################################################################
    # Explicate Control
    ############################################################################

    def create_block(self, promise, label: str = None) -> Goto:
        """promise can be a list of statements, or a function returning a list of statements"""
        stmts = force(promise)
        match stmts:
            case [Goto(l)]:
                return Goto(l)
            case _:
                if not label:
                    label = label_name(generate_name('block' + self.name))
                self.basic_blocks[label] = stmts
                return Goto(label)

    def create_block_no_lazy(self, stmts: List[stmt], label: str = None) -> str:
        # TODO:
        """create a block and add it to the block dict,
        return label name of the new block"""
        if not label:
            label = label_name(generate_name('block'))

        self.basic_blocks[label] = force(stmts)
        return Goto(label)

    def explicate_effect(self, e, cont):
        match e:
            case IfExp(test, body, orelse):
                return self.explicate_pred(test, body, orelse) + cont
            case Call(func, args):
                return [Expr(e)] + force(cont)
            case Let(var, rhs, body):
                ...
            case _:
                print("DEBUG: hit explicate_effect wild")
                return cont

    def explicate_assign(self, rhs: expr, lhs: Name, cont: List[stmt]) -> List[stmt]:
        match rhs:
            case IfExp(test, body, orelse):
                # dispatch to `explicate_pred`
                # `cont` must not be empty
                trampoline = self.create_block(cont)
                body_ss = self.explicate_assign(body, lhs, [trampoline])
                orelse_ss = self.explicate_assign(orelse, lhs, [trampoline])
                return self.explicate_pred(test, body_ss, orelse_ss)
            case Let(var, let_rhs, let_body):
                return [Assign([var], let_rhs)] + self.explicate_assign(let_body, lhs, []) + force(cont)
            case Begin(body, result):
                new_cont = [Assign([lhs], result)] + force(cont)
                body_ss = self.explicate_stmts(body, new_cont)
                return body_ss
                # return body_ss + [Assign([lhs], result)] + force(cont)
            case _:
                print("DEBUG: hit explicate_assign wild ", rhs)
                return [Assign([lhs], rhs)] + force(cont)

    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt]):
        match cnd:
            case Compare(left, [op], [right]):
                return [If(cnd,
                           [self.create_block(thn)],
                           [self.create_block(els)])]
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case Subscript(tup, idx, Load()):
                var = Name("pyc_temp_var_" + str(self.temp_count))
                self.temp_count += 1
                return [Assign([var], cnd)] + self.explicate_pred(var, thn, els)
            case UnaryOp(Not(), operand):
                return [If(Compare(operand, [Eq()], [Constant(False)]),
                           [self.create_block(thn)],
                           [self.create_block(els)])]
            case IfExp(test, body, orelse):
                # in `IfExp` inside pred, body and orelse must also be predicate
                thn_goto = self.create_block(thn)
                els_goto = self.create_block(els)
                # TODO: what if body/orelse is T/F?
                # body_ss = [If(body, [Goto(thn_label)], [Goto(els_label)])]

                def body_ss(): return self.explicate_pred(
                    body, [thn_goto], [els_goto])
                # orelse_ss = [If(orelse, [Goto(thn_label)], [Goto(els_label)])]
                def orelse_ss(): return self.explicate_pred(
                    orelse, [thn_goto], [els_goto])
                return lambda: self.explicate_pred(test, body_ss, orelse_ss)
            case Let(var, let_rhs, body):
                # `body must be a predicate`
                # TODO
                # print("DEBUG: Let, cnd:", cnd)
                tail = self.explicate_pred(body, thn, els)
                # print("DEBUG: tail:", tail, "force: ", force(tail))
                # return [Assign([var], let_rhs)] + self.explicate_pred(body, thn, els)
                return [Assign([var], let_rhs)] + force(tail)
            case Call(funRef, args):
                var = Name("pyc_temp_var_" + str(self.temp_count))
                self.temp_count += 1
                return [Assign([var], cnd)] + self.explicate_pred(var, thn, els)
            case _:
                print("DEBUG: hit explicate_pred wild")
                return [If(Compare(cnd, [Eq()], [Constant(False)]),
                           [self.create_block(els)],
                           [self.create_block(thn)])]

    def explicate_tail(self, e) -> List[stmt]:  # e is a return value
        match e:
            case IfExp(test, thn, orelse):
                new_thn = self.explicate_tail(thn)
                new_els = self.explicate_tail(orelse)
                return self.explicate_pred(test, new_thn, new_els)
            case Let(var, rhs, thn):
                return [Assign([var], rhs)] + self.explicate_tail(thn)
            case Begin(body, result):
                new_cont = [Return(result)]
                return self.explicate_stmts(body, new_cont)
            # built-in functions don't need to be converted into tail call
            case Call(f) if f in CompileFunction.builtin_functions:
                return [Return(e)]
            case Call(func, args):
                return [TailCall(func, args)]
            case _:
                return [Return(e)]

    def explicate_stmt(self, s, cont) -> List[stmt]:
        match s:
            case Assign([lhs], rhs):
                return lambda: self.explicate_assign(rhs, lhs, cont)
            case Expr(value):
                return lambda: self.explicate_effect(value, cont)
            case If(test, body, orelse):
                # `cont` must be nonempty.
                trampoline = self.create_block(cont)
                body_exped = self.explicate_stmts(body, [trampoline])
                orelse_exped = self.explicate_stmts(orelse, [trampoline])
                return lambda: self.explicate_pred(test, body_exped, orelse_exped)
            case While(cnd, body, []):
                loopBlock = self.create_block([])
                trampoline = self.create_block(cont)
                body_exped = self.explicate_stmts(body, [loopBlock])
                cnd_exped = self.explicate_pred(cnd, body_exped, [trampoline])
                # update loop block to have the if condition
                self.create_block_no_lazy(cnd_exped, loopBlock.label)
                return [loopBlock]
            case Collect(_):
                print("DEBUG: HIT Collect")
                return [s] + force(cont)
            case Return(exp):
                return self.explicate_tail(exp)
            case _:
                print("DEBUG: hit explicate_stmt wild" + repr(s))

        return cont

    def explicate_stmts(self, ss: List[stmt], cont) -> List[stmt]:
        for s in reversed(ss):
            cont = self.explicate_stmt(s, cont)
        return cont

    def explicate_control(self, p: Module) -> Dict:
        cont = [Return(Constant(0))]
        label = label_name(self.name + 'start')
        match p:
            case Module(body):
                new_body = self.explicate_stmts(body, cont)
                self.create_block_no_lazy(new_body, label=label)
                # print("DEBUG: .start: ", self.basic_blocks[label])
                return self.basic_blocks

    ############################################################################
    # Select Instructions
    ############################################################################

    def condition_abbr(cmp: cmpop) -> str:
        """covert the compare operation to an abbreviation in instruction"""
        match cmp:
            case Eq():
                return 'e'
            case NotEq():
                return 'ne'
            case Gt():
                return 'g'
            case GtE():
                return 'ge'
            case Lt():
                return 'l'
            case LtE():
                return 'le'
            case _:
                raise Exception(
                    'error in condition_abbr, cmp not supported' + repr(cmp))

    def select_arg(self, e: expr) -> arg:
        match e:
            case Constant(True):
                return Immediate(1)
            case Constant(False):
                return Immediate(0)
            case Constant(c):
                return Immediate(c)
            case Name(var):
                return Variable(var)

    def select_expr(self, e: expr) -> List[instr]:
        # TODO: binary Sub
        # pretending the variable will always be assigned

        def generate_tag(length: int, ts: List) -> int:
            # TODO: complete this function
            """a helper function to generate the 64-bit tag based on the length of tuple and types"""
            # 1 bit to indicate forwarding (0) or not (1). If 0, then the header is the forwarding pointer.
            # 6 bits to store the length of the tuple (max of 50)
            # 50 bits for the pointer mask to indicate which elements of the tuple are pointers.
            tag = 0
            assert(isinstance(ts, TupleType))
            ts = ts.types
            assert(length == len(ts))
            tag = length << 1
            tag = tag | 1
            ptrMsk = 0
            for i in range(length):
                #print("DEBUG: ts[i]: ", ts[i], "type: ", type(ts[i]), "equal?: ", ts[i] is Tuple)

                # if ts[i] is int:
                #     print("DEBUG: hit int")
                # if ts[i] is Tuple:
                #     # Do something to tag here
                #     print("DEBUG: hit Tuple")
                match ts[i]:
                    case TupleType(nest_ts):
                        # Do something to tag here
                        ptrMsk = ptrMsk + 1
                        ptrMsk = ptrMsk << 1
                        #print("DEBUG: hit Tuple")
                    case _:
                        #print("DEBUG: type ignored for now")
                        ptrMsk = ptrMsk << 1
            ptrMsk = ptrMsk << 6  # check this
            tag = ptrMsk | tag
            # print(bin(tag))

            return tag

        instrs = []
        match e:
            case Call(Name('input_int'), []):
                instrs.append(Callq('read_int', 0))
                instrs.append(
                    Instr('movq', [Reg('rax'), Variable("Unnamed_Pyc_Var")]))
            case UnaryOp(USub(), atm):
                instrs.append(
                    Instr('movq', [self.select_arg(atm), Variable("Unnamed_Pyc_Var")]))
                instrs.append(Instr('negq', [Variable("Unnamed_Pyc_Var")]))
            case UnaryOp(Not(), atm):
                instrs.append(
                    Instr('movq', [self.select_arg(atm), Variable("Unnamed_Pyc_Var")]))
                instrs.append(
                    Instr('xorq', [Immediate(1), Variable("Unnamed_Pyc_Var")]))
            case Compare(atm1, [cmp], [atm2]):
                # switch atm1 and atm2
                instrs.append(
                    Instr('cmpq', [self.select_arg(atm2), self.select_arg(atm1)]))
                instrs.append(
                    Instr('set' + CompileFunction.condition_abbr(cmp), [Reg('al')]))
                instrs.append(
                    Instr('movzbq', [Reg('al'), Variable("Unnamed_Pyc_Var")]))
            case BinOp(atm1, Add(), atm2):
                # TODO: optimize when the oprand and destination is the same
                # if isinstance(atm1, Name):
                #     (atm1, atm2) = (atm2, atm1)
                # if isinstance(atm2, Name):
                #     instrs.append(Instr('addq', [select_arg, Name("Unbounded_Pyc_Var")]))
                instrs.append(
                    Instr('movq', [self.select_arg(atm1), Variable("Unnamed_Pyc_Var")]))
                instrs.append(
                    Instr('addq', [self.select_arg(atm2), Variable("Unnamed_Pyc_Var")]))
            case BinOp(atm1, Sub(), atm2):
                # may need test
                instrs.append(
                    Instr('movq', [self.select_arg(atm1), Variable("Unnamed_Pyc_Var")]))
                instrs.append(
                    Instr('subq', [self.select_arg(atm2), Variable("Unnamed_Pyc_Var")]))
            case Subscript(tup, idx, Load()):
                match idx:
                    case Constant(i):
                        offset = 8 * (i + 1)
                instrs.append(
                    Instr('movq', [self.select_arg(tup), Reg('r11')]))
                instrs.append(
                    Instr('movq', [Deref('r11', (offset)), Reg('r11')]))
                instrs.append(
                    Instr('movq', [Reg('r11'), Variable("Unnamed_Pyc_Var")]))
                # TODO
            case Call(Name('len'), [exp]):
                # print("DEBUG: exp: ", exp, type(exp))
                # TODO get length based on tag?
                instrs.append(
                    Instr('movq', [self.select_arg(exp), Reg('rax')]))
                instrs.append(Instr('movq', [Deref('rax', 0), Reg('rax')]))
                # gets just the length part of the tag
                instrs.append(Instr('andq', [Immediate(126), Reg('rax')]))
                # shift right one
                instrs.append(Instr('sarq', [Immediate(1), Reg('rax')]))
                instrs.append(
                    Instr('movq', [Reg('rax'), Variable("Unnamed_Pyc_Var")]))
                # print(exp)
            case Allocate(length, ts):
                tag = generate_tag(length, ts)
                instrs.append(Instr('movq', [Global('free_ptr'), Reg('r11')]))
                instrs.append(
                    Instr('addq', [Immediate(8 * (length + 1)), Global('free_ptr')]))
                instrs.append(Instr('movq', [Immediate(tag), Deref('r11', 0)]))
                instrs.append(
                    Instr('movq', [Reg('r11'), Variable("Unnamed_Pyc_Var")]))
            case GlobalValue(var):
                instrs.append(
                    Instr('movq', [Global(var), Variable("Unnamed_Pyc_Var")]))
                # instrs.append(Global(var))
            case FunRef(f):
                instrs.append(
                    Instr('leaq', [FunRef(f), Variable("Unnamed_Pyc_Var")]))
            case Call(Name(func), args):
                i = 0
                new_args = [self.select_arg(arg) for arg in args]
                for arg in new_args:
                    instrs.append(
                        Instr('movq', [arg, CompileFunction.arg_passing[i]]))
                    i += 1
                # TODO: what if not an indirect call?
                instrs.append(IndirectCallq(Variable(func), i))
                # TODO: what if nothing returned? Delete "Unnamed_Pyc_Var" instructions
                instrs.append(
                    Instr('movq', [Reg('rax'), Variable("Unnamed_Pyc_Var")]))
            case _:
                instrs.append(
                    Instr('movq', [self.select_arg(e), Variable("Unnamed_Pyc_Var")]))

        return instrs

    def select_stmt(self, s: stmt) -> List[instr]:

        def bound_unamed(instrs: List[instr], var) -> List[instr]:
            new_instrs = []
            for i in instrs:
                match i:
                    # for variable name
                    case Instr(oprtr, args) if isinstance(var, str):
                        new_args = [Variable(var) if a == Variable(
                            "Unnamed_Pyc_Var") else a for a in args]
                        new_instrs.append(Instr(oprtr, new_args))
                    # if var is a register
                    case Instr(oprtr, args) if isinstance(var, Reg):
                        new_args = [var if a == Variable(
                            "Unnamed_Pyc_Var") else a for a in args]
                        new_instrs.append(Instr(oprtr, new_args))
                    case wild:
                        new_instrs.append(wild)

            return new_instrs

        instrs = []
        match s:
            # TODO: may delete all instructions containing `Variable("Unnamed_Pyc_Var")``
            case If(test, body, orelse):
                assert isinstance(body[0], Goto)
                body_label = body[0].label
                assert isinstance(orelse[0], Goto)
                else_label = orelse[0].label
                match test:
                    case Compare(atm1, [cmp], [atm2]):
                        instrs.append(
                            Instr('cmpq', [self.select_arg(atm2), self.select_arg(atm1)]))
                        abbr = CompileFunction.condition_abbr(cmp)
                    case _:
                        raise Exception(
                            'error in select_expr, if: invlaid test ' + repr(test))
                instrs.append(JumpIf(abbr, body_label))
                instrs.append(Jump(else_label))
            case Expr(Call(Name('print'), [atm])):
                instrs.append(
                    Instr('movq', [self.select_arg(atm), Reg('rdi')]))
                instrs.append(Callq('print_int', 1))
            case Goto(label):
                instrs.append(Jump(label))
            case Expr(exp):
                instrs += self.select_expr(exp)
            case Assign([Name(var)], exp):
                instrs += bound_unamed(self.select_expr(exp), var)
            case Assign([Subscript(tup, idx, Store())], exp):
                instrs.append(
                    Instr('movq', [self.select_arg(tup), Reg('r11')]))
                match idx:
                    case Constant(i):
                        reg = 8*(i+1)
                instrs.append(
                    Instr('movq', [self.select_arg(exp), Deref('r11', (reg))]))
                # movq exp, 8(idx + 1)(%r11)
            case Collect(bytes):
                instrs.append(Instr('movq', [Reg('r15'), Reg('rdi')]))
                instrs.append(Instr('movq', [Immediate(bytes), Reg('rsi')]))
                instrs.append(Callq('collect', 2))
                # how many args? 2?
            case TailCall(Name(func), args):
                print("TAIL CALL")
                i = 0
                new_args = [self.select_arg(arg) for arg in args]
                for arg in new_args:
                    instrs.append(
                        Instr('movq', [arg, CompileFunction.arg_passing[i]]))
                    i += 1
                instrs.append(TailJump(Variable(func), i))
            case Return(exp):
                instrs += bound_unamed(self.select_expr(exp), Reg('rax'))
                instrs.append(Jump(self.conclusion_label))
                # TODO: ret instruction
            case _:
                raise Exception('error in select_stmt, unhandled ' + repr(s))

        return instrs

    def select_instructions(self, p: CProgram) -> Dict:
        match p:
            # case Module(stmts):
            #     insts = [inst for s in stmts for inst in self.select_stmt(s)]
            #     return X86Program(insts)
            case CProgram(blks):
                x86_blks = {}
                for (label, block) in blks.items():
                    x86_blks[label] = [
                        inst for s in block for inst in self.select_stmt(s)]
                return x86_blks
            case _:
                raise Exception(
                    'error in select_instructions, ' + repr(p))

    ############################################################################
    # Liveness after set generation
    ############################################################################

    def uncover_live(self, p: X86Program) -> List[Set]:

        def extract_locations(args: List[arg]) -> set:
            """extract all the locations from a list of args"""

            extracted = set()
            for a in args:
                if isinstance(a, location):
                    extracted.add(a)
                    self.int_graph.add_vertex(a)

            return extracted

        def analyze_instr(s: instr) -> set[str]:
            """take an instrunction, analyze the read/write locations of each instruction and return the potential jumping target (label) if it's a jump"""

            read_set = set()
            write_set = set()
            target = set()

            match s:
                # TODO: Instr cmpq, xorq, set, movzbq need to be added? Yes
                case Instr("movq", [src, dest]):
                    (read_set, write_set) = (extract_locations(
                        [src]), extract_locations([dest]))
                case Instr(binop, [arg1, arg2]) if binop in ['addq', 'subq']:
                    (read_set, write_set) = (extract_locations(
                        [arg1, arg2]), extract_locations([arg2]))
                case Instr("negq", [arg]):
                    (read_set, write_set) = (extract_locations(
                        [arg]), extract_locations([arg]))
                # case Instr("subq", [arg1, arg2]):
                #     (read_set, write_set) = (extract_locations([arg1, arg2]), extract_locations([arg2]))
                case Instr("cmpq", [arg1, arg2]):
                    (read_set, write_set) = (
                        extract_locations([arg1, arg2]), {})
                case Instr("xorq", [arg1, arg2]):
                    (read_set, write_set) = (
                        extract_locations([arg1, arg2]), {})
                case Instr("movzbq", [src, dest]):
                    # TODO: remove hardcode to %al
                    (read_set, write_set) = (
                        [Reg('rax')], extract_locations([dest]))
                case Instr("sarq", [Immediate(_), arg]):
                    (read_set, write_set) = (extract_locations(
                        [arg]), extract_locations([arg]))
                case Instr("andq", [arg1, arg2]):
                    (read_set, write_set) = (extract_locations(
                        [arg1, arg2]), extract_locations([arg2]))
                case Instr(ins, [arg]) if len(ins) >= 3 and ins[:3] == 'set':
                    # TODO: match each sub instructions of `set`, maybe in an elegant way?
                    (read_set, write_set) = (
                        {}, extract_locations([Reg('rax')]))
                case Callq(_func_name, num_args):
                    (read_set, write_set) = (extract_locations(
                        CompileFunction.arg_passing[:num_args]), extract_locations(CompileFunction.caller_saved))
                case Instr('nop', _):
                    pass
                case Jump(dest):
                    target.add(dest)
                case JumpIf(_cc, dest):
                    target.add(dest)
                case IndirectCallq(address, num_args):
                    (read_set, write_set) = (extract_locations(
                        CompileFunction.arg_passing[:num_args] + [address]), extract_locations(CompileFunction.caller_saved))
                case TailJump(address, num_args):
                    (read_set, write_set) = (extract_locations(
                        CompileFunction.arg_passing[:num_args] + [address]), extract_locations(CompileFunction.caller_saved))
                # TODO check this, should be same as move'
                case Instr("leaq", [src, dest]):
                    print("DEBUG: hit leaq")
                    (read_set, write_set) = (extract_locations(
                        [src]), extract_locations([dest]))
                case _:
                    raise Exception(
                        'error in read_write_sets, unhandled' + repr(s))

            self.read_set_dict[s] = read_set
            self.write_set_dict[s] = write_set
            return target

        def transfer(label: str, starting_las: set) -> set:
            """take a label and the starting point(las), return the live before set of the block"""
            block = self.basic_blocks[label]
            last_set = starting_las
            for ins in reversed(block):
                self.live_after_set_dict[ins] = last_set
                self.live_before_set_dict[ins] = last_set.difference(
                    self.write_set_dict[ins]).union(self.read_set_dict[ins])
                last_set = self.live_before_set_dict[ins]

            return last_set

        ####### Build Control Flow Graph ##########

        # Hongbo: I use label here to build control_flow_graph, please use self.basic_blocks[label] or p.body[label] to find the corres block

        # generate the read & write set for each instruction, and build CFG
        assert(isinstance(p, X86Program))
        assert(isinstance(p.body, dict))
        self.basic_blocks = p.body
        for (label, block) in p.body.items():
            self.control_flow_graph.add_vertex(label)
            jumping_targets = set()
            for s in reversed(block):
                jumping_targets = jumping_targets.union(analyze_instr(s))
            for t in jumping_targets:
                # please note the sequence of argument MATTERS
                self.control_flow_graph.add_edge(label, t)

        def join(x, y): return x.union(y)

        mapping = analyze_dataflow(
            self.control_flow_graph, transfer, set(), join)

        print(mapping)
        self.live_before_block = mapping

        return self.live_after_set_dict

    ############################################################################
    # inference and move graph building
    ############################################################################

    def build_move_graph(self, ins_list: list[instr]) -> bool:
        """store the mvoe graph in member, `self.move_graph`"""
        for s in ins_list:
            match s:
                case Instr("movq", [src, dest]) if isinstance(src, location):
                    self.move_graph.add_edge(src, dest)
                case _:  # ingore other cases for now
                    pass

        return True

    def build_interference(self, las_dict: Dict[instr, set]) -> bool:
        """store the interference graph in member, `self.int_graph`"""
        for ins, las in las_dict.items():
            match ins:
                case Instr("movq", [src, dest]):
                    for loc in las:
                        self.int_graph.add_vertex(loc)
                        if not (loc == src or loc == dest):
                            self.int_graph.add_edge(loc, dest)
                # TODO: make movzbq more general
                case Instr("movzbq", [_, dest]):
                    for loc in las:
                        self.int_graph.add_vertex(loc)
                        # now assumes the src is always %al
                        if not (loc == Reg("rax") or loc == dest):
                            self.int_graph.add_edge(loc, dest)
                case Instr(ins, [arg]) if len(ins) >= 3 and ins[:3] == 'set':
                    # now assumes the arg is always %al
                    for loc in las:
                        self.int_graph.add_vertex(loc)
                        self.int_graph.add_edge(loc, Reg("rax"))
                case Instr(binop, [_, arg]) if binop in ['addq', 'subq', 'andq', 'orq']:
                    for loc in las:
                        if not loc == arg:
                            self.int_graph.add_edge(loc, arg)
                case Instr("negq", [arg]):
                    for loc in las:
                        if not loc == arg:
                            self.int_graph.add_edge(loc, arg)
                case Instr("sarq", [Immediate(_), arg]):  # similar to negq
                    for loc in las:
                        if not loc == arg:
                            self.int_graph.add_edge(loc, arg)
                case Callq(_func_name, _num_args):
                    for loc in las:
                        for dest in CompileFunction.caller_saved:
                            if not dest == loc:
                                self.int_graph.add_edge(loc, dest)
                # TODO check this, not sure if it should be the same as Callq
                case IndirectCallq(address, _num_args):
                    for loc in las:
                        for dest in CompileFunction.caller_saved:
                            if not dest == loc:
                                self.int_graph.add_edge(loc, dest)
                case TailJump(_):  # TODO not sure what it should be
                    pass
                # TODO check if this should be the same as movq or not
                case Instr("leaq", [src, dest]):
                    for loc in las:
                        self.int_graph.add_vertex(loc)
                        if not (loc == src or loc == dest):
                            self.int_graph.add_edge(loc, dest)
                # trivial reads/jumps
                case Jump(_):
                    pass
                case JumpIf(_, _):
                    pass
                case Instr("cmpq", [_, _]):
                    pass
                case _:
                    raise Exception(
                        'error in build_interference, unhandled' + repr(ins))

        return True

    ############################################################################
    # graph coloring
    ############################################################################

    def color_graph(self, graph: UndirectedAdjList) -> Dict[location, int]:
        """use negative numbers to represent reserved registers
        use positive number to represent allocatable reg/stack spills
        use imaginary number to represent shadow stack"""

        saturation_dict = {}
        assign_dict = {}

        def less(x: location, y: location):
            return len(saturation_dict[x.key]) < len(saturation_dict[y.key])

        def shadow_or_stack(v: Variable):
            assert(isinstance(v, Variable))
            # How to check it's really a tup?
            if v.id.startswith('pyc_temp_tup') or v.id.startswith('temp_tup') or (v.id in self.tuple_vars):
                # goes to shadow stack
                return (0+1j, 0+1j)
            else:
                # goes to stack
                return (0, 1)

        # initialize saturation_dict
        for v in graph.vertices():
            saturation_dict[v] = set()

        # check if the vertices are already a register
        for v in graph.vertices():
            if isinstance(v, Reg):
                # find key for the register in `allocation` dict
                for index, reg in self.color_reg_map.items():
                    # TODO: correct? extended_reg is not used
                    extended_reg = CompileFunction.extend_reg(reg)
                    # print("DEBUG: v:,", v, " reg: ", reg)
                    if reg == v:
                        assign_dict[v] = index
                        break
                # color the adjacent of allocated registers first
                # there should be no confliction!
                for adjacent in graph.adjacent(v):
                    saturation_dict[adjacent].add(assign_dict[v])

        pq = PriorityQueue(less)
        for k, v in saturation_dict.items():
            pq.push(k)
        for _ in range(len(saturation_dict)):
            v = pq.pop()
            # skip register vertices or already assigned vars, since they've been assigned a home
            if isinstance(v, Reg) or isinstance(v, Global) or isinstance(v, Deref):
                continue
            v_saturation = saturation_dict[v]
            colored = False

            # biased coloring if it's in move graph
            if v in self.move_graph.vertices():
                for candidate in self.move_graph.adjacent(v):
                    # check if the candidate can be biased for v, which means:
                    # 1. adjacent to v in move_graph
                    # 2. allocatable register
                    # 3. not in v's saturation set
                    if (candidate in assign_dict) and (0 <= assign_dict[candidate] < len(self.allocatable)) and (assign_dict[candidate] not in v_saturation):
                        assign_dict[v] = assign_dict[candidate]
                        colored = True
            # color = 0
            (color, step) = shadow_or_stack(v)

            # if not going into biased move
            print("DEBUG in color_graph: v, ", v)
            while not colored:
                if color not in v_saturation:
                    assign_dict[v] = color
                    colored = True
                else:
                    color += step

            for adjacent in graph.adjacent(v):
                saturation_dict[adjacent].add(assign_dict[v])
                pq.increase_key(adjacent)

        # print("DEBUG: saturation_dict:\n", saturation_dict)
        return assign_dict

    ############################################################################
    # Assign Homes
    ############################################################################

    def assign_homes_arg(self, a: arg, home: Dict[Variable, arg]) -> arg:

        if a in home.keys():
            return home[a]
        else:
            print("WARNING: home not found for a in assign_homes_arg", a.__repr__())
            return a

    def assign_homes_instr(self, i: instr,
                           home: Dict[location, arg]) -> instr:
        match i:
            case Instr(oprtr, args):
                new_args = []
                for a in args:
                    new_args.append(self.assign_homes_arg(a, home))
                return Instr(oprtr, new_args)
            case IndirectCallq(func, num_args):
                new_func = self.assign_homes_arg(func, home)
                print("DEBUG, IndirectCallq case in assign_homes_instr, new_func: ")
                return IndirectCallq(new_func, num_args)
            case TailJump(func, num_args):
                new_func = self.assign_homes_arg(func, home)
                return TailJump(new_func, num_args)
            case other:
                print("WARNING, hit wild case in assign_homes_instr: ",
                      other.__repr__())
                return other

    def assign_homes_instrs(self, basic_blocks: Dict[str, List[instr]],
                            home: Dict[location, arg]) -> Dict[str, List[instr]]:
        new_bbs = {}
        for label, block in basic_blocks.items():
            new_block = []
            for i in block:
                new_block.append(self.assign_homes_instr(i, home))
            new_bbs[label] = new_block

        return new_bbs

    def map_colors(self, coloring: Dict[location, int]) -> Dict[location, arg]:
        """return a dict mapping colors to registers or stack locations"""

        # TODO: record how much shadow stack and stack space is used here
        allocatable_reg_num = len(self.allocatable)
        result = {}

        shadow_stack = {}
        normal_stack = {}

        # seprate the shadow stack and normal stack
        for vertex, color in coloring.items():
            if isinstance(color, int):
                normal_stack[vertex] = color
            if isinstance(color, complex):
                shadow_stack[vertex] = color

        for vertex, color in normal_stack.items():
            if color < allocatable_reg_num:
                result[vertex] = self.color_reg_map[color]
            else:
                result[vertex] = Deref(
                    "rbp", - (color - allocatable_reg_num + 1) * 8)
                self.normal_stack_count += 1

        for vertex, color in shadow_stack.items():
            # TODO: may not be right
            # spill all
            offset = int(color.imag - 1)
            result[vertex] = Deref(
                "r15", - (offset + 1) * 8)
            self.shadow_stack_count += 1

        return result

    def assign_homes(self, p: X86Program) -> Dict:

        # assuming p.body is a list
        las_list = self.uncover_live(p)
        self.build_interference(las_list)
        self.build_move_graph(p.body)
        coloring = self.color_graph(self.int_graph)

        # figure out which registers need saving
        for r in CompileFunction.callee_saved[2:]:
            # find the color of register
            color = None
            for index, reg in self.color_reg_map.items():
                if reg == r:
                    color = index
            # this color(reg) is used
            if color in coloring.values():
                self.used_callee.add(r)

        home = self.map_colors(coloring)
        print("DEBUG: home: ", home)

        return self.assign_homes_instrs(p.body, home)

    ############################################################################
    # Patch Instructions
    ############################################################################
    # TODO: Patch Instructions is not modified for tuples, may subject to change

    def patch_instr(self, i: instr) -> List[instr]:
        patched_instrs = []
        match i:
            case Instr("movq", [Deref(reg1, offset1), Deref(reg2, offset2)]):
                # MOV: Two memory locations in args
                patched_instrs.append(
                    Instr("movq", [Deref(reg1, offset1), Reg("rax")]))
                patched_instrs.append(
                    Instr("movq", [Reg("rax"), Deref(reg2, offset2)]))
            case Instr(binop, [Deref(reg1, offset1), Deref(reg2, offset2)]) if binop in ['addq', 'subq']:
                # ADD/SUB: Two memory locations in args
                patched_instrs.append(
                    Instr("movq", [Deref(reg1, offset1), Reg("rax")]))
                patched_instrs.append(
                    Instr(binop, [Reg("rax"), Deref(reg2, offset2)]))
            case Instr("movq", [Immediate(v), dest]):
                if v > 2147483647 or v < -2147483648:  # not fit into 32-bit
                    # TODO: may need to check for `dest` for optimization
                    patched_instrs.append(
                        Instr("movq", [Immediate(v), Reg("rax")]))
                    patched_instrs.append(Instr("movq", [Reg("rax"), dest]))
                else:
                    patched_instrs.append(i)
            case Instr("movq", [Reg(reg1), Reg(reg2)]) if reg1 == reg2:
                # MOV: Trivial move (move to same place after allocating registers)
                # THROW AWAY (don't let it be added in in last case)
                pass
            case Instr("cmpq", [src, Immediate(v)]):
                # 2nd arg must not be an immediate value
                patched_instrs.append(
                    Instr("movq", [Immediate(v), Reg("rax")]))
                patched_instrs.append(
                    Instr("cmpq", [src, Reg("rax")]))
            case Instr("movzbq", [src, Immediate(v)]):
                # 2nd Argument must be a register
                patched_instrs.append(
                    Instr("movq", [Immediate(v), Reg("rax")]))
                patched_instrs.append(
                    Instr("movzbq", [src, Reg("rax")]))
            case Instr('leaq', [exp, dest]) if not isinstance(dest, Reg):
                # destination must be a register
                patched_instrs.append(
                    Instr('leaq', [exp, Reg('rax')]))
                patched_instrs.append(
                    Instr('movq', [Reg('rax'), dest]))
            case TailJump(arg, argCt):
                # make sure arg is the reserved rax register
                if arg != Reg('rax'):
                    patched_instrs.append(
                        Instr('movq', [arg, Reg('rax')]))
                # pop the current frame then jump to the function (same as the code for the conclusion of a function, except the retq is replaced with jmp *arg)
                patched_instrs.append(
                    Instr('subq', [Immediate(self.shadow_stack_size), Reg('r15')]))
                patched_instrs.append(
                    Instr('addq', [Immediate(self.stack_frame_size), Reg('rsp')]))
                for r in reversed(self.used_callee):
                    patched_instrs.append(Instr('popq', [r]))
                patched_instrs.append(Instr('popq', [Reg('rbp')]))
                patched_instrs.append(IndirectJump(Reg('rax')))
            case _:
                patched_instrs.append(i)

        return patched_instrs

    def patch_instrs(self, ss: List[instr]) -> List[instr]:
        new_instrs = []
        for i in ss:
            new_instrs += self.patch_instr(i)

        return new_instrs

    def patch_instructions(self, p: X86Program) -> Dict:

        assert(type(p.body) == dict)
        # get frame sizes for tail jumps

        def align():
            alignment = 8 * (len(self.used_callee) +
                             self.normal_stack_count)  # current alignment
            if (alignment % 16) != 0:
                alignment += 8
            return alignment - (8 * len(self.used_callee))
        self.used_callee = list(self.used_callee)
        self.stack_frame_size = align()
        self.shadow_stack_size = self.shadow_stack_count * 8

        new_body = {}

        for label, block in p.body.items():
            new_body[label] = self.patch_instrs(block)

        return new_body

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> Dict:

        prelude = []
        prelude.append(Instr('pushq', [Reg('rbp')]))
        prelude.append(Instr('movq', [Reg('rsp'), Reg('rbp')]))
        for r in self.used_callee:
            prelude.append(Instr('pushq', [r]))
        # TODO: ignore this when sub 0
        prelude.append(
            Instr('subq', [Immediate(self.stack_frame_size), Reg('rsp')]))
        # shadow stack handling for main
        if self.name == "main":  # TODO: may need string compare
            prelude.append(Instr('movq', [Immediate(16384), Reg('rdi')]))
            prelude.append(Instr('movq', [Immediate(16384), Reg('rsi')]))
            prelude.append(Callq('initialize', 2))
            prelude.append(
                Instr('movq', [Global('rootstack_begin'), Reg('r15')]))

        # Zero out all locations on the root stack "movq $0, $0(%r15)" = "movq $0, (%r15)"
        prelude.append(Instr('movq', [Immediate(0), Deref('r15', 0)]))
        prelude.append(
            Instr('addq', [Immediate(self.shadow_stack_size), Reg('r15')]))
        # jump to start of function
        prelude.append((Jump(self.name + 'start')))

        conclusion = []
        conclusion.append(
            Instr('subq', [Immediate(self.shadow_stack_size), Reg('r15')]))
        conclusion.append(
            Instr('addq', [Immediate(self.stack_frame_size), Reg('rsp')]))
        for r in reversed(self.used_callee):
            conclusion.append(Instr('popq', [r]))
        conclusion.append(Instr('popq', [Reg('rbp')]))
        conclusion.append(Instr('retq', []))

        assert(type(p.body) == dict)

        p.body[self.prelude_label] = prelude
        p.body[self.conclusion_label] = conclusion

        return p.body
