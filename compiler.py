import ast
from ast import *
from utils import *
from x86_ast import *
from graph import *
from priority_queue import *
import os
from typing import List, Tuple, Set, Dict

# Type notes
Binding = Tuple[Name, expr]
Temporaries = List[Binding]

# Global register categorization

# Register used for argument passing
arg_passing = ['rdi', 'rsi', 'rdx', 'rcx', 'r8', 'r9', ]
caller_saved = arg_passing + ['rax', 'r10', 'r11']
callee_saved = ['rsp', 'rbp', 'rbx', 'r12', 'r13', 'r14', 'r15']

# Allocatable registers = all - rsp - rbp - rax
allocatable = callee_saved + caller_saved
allocatable.remove('rsp')
allocatable.remove('rbp')
allocatable.remove('rax')


class Compiler:

    temp_count: int = 0
    # used for tracking static stack usage
    stack_count: int = 0

    # `calllq`: include first `arg_num` registers in its read-set R
    arg_passing = [Reg(x) for x in arg_passing]
    # `callq`: include all caller_saved registers in write-set W
    caller_saved = [Reg(x) for x in caller_saved]

    callee_saved = [Reg(x) for x in callee_saved]

    def __init__(self):
        self.read_set_dict = {}
        self.write_set_dict = {}
        self.live_after_set_dict = {}
        self.basic_blocks = {}
        # this list can be changed for testing spilling
        self.allocatable = [Reg(x) for x in allocatable]
        all_reg = [Reg('rsp'), Reg('rbp'), Reg('rax')] + self.allocatable
        self.int_graph = UndirectedAdjList()
        self.move_graph = UndirectedAdjList()
        self.used_callee = set()

        self.color_reg_map = {}
        color_from = -3
        for reg in all_reg:
            self.color_reg_map[color_from] = reg
            color_from += 1

    ############################################################################
    # Remove Complex Operands
    ############################################################################

    # def shrink_stmt(self, s: stmt) -> stmt:
    #     """    
    #     # e1 and e2 ⇒ e2 if e1 else False
    #     # e1 or e2 ⇒ True if e1 else e2
    #     # IfExp(test, body, orelse)
    #     """
    #     match s:
    #         case Expr(BoolOp(And(), [e1, e2])):
    #             return Expr(IfExp(e1, e2, False))
    #         case Expr(BoolOp(Or(), [e1, e2])):
    #             return Expr(IfExp(e1, True, e2))
    #         case somethingElse:
    #             return somethingElse
    # def shrink(self, p: Module) -> Module:
    #     """Removing 'and' & 'or' by translating them into if-statements"""
    #     match p:
    #         case Module(stmts):
    #             new_stmts = [self.shrink_stmt(s) for s in stmts]
    #             return Module(new_stmts)

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

    def rco_exp(self, e: expr, need_atomic: bool) -> Tuple[expr, Temporaries]:

        temps = []
        # tail must be assigned in the match cases
        if Compiler.is_atm(e):
            """nothing need to do if it's already an `atm`"""
            return (e, temps)

        match e:
            # recursively call rco_exp on each op
            # shrink `and` & `or`
            case BoolOp(And(), [e1, e2]):
                return self.rco_exp(IfExp(e1, e2, Constant(False)), need_atomic)
            case BoolOp(Or(), [e1, e2]):
                return self.rco_exp(IfExp(e1, Constant(True), e2), need_atomic)
            case UnaryOp(uniop, exp):
                # `Not()` and `USub`
                if Compiler.is_atm(exp):
                    tail = e
                else:
                    (atm, temps) = self.rco_exp(exp, True)
                    tail = UnaryOp(uniop, atm)
            case BinOp(exp1, Add(), exp2):
                if Compiler.is_atm(exp1):
                    (exp1_atm, exp1_temps) = (exp1, [])
                else:
                    (exp1_atm, exp1_temps) = self.rco_exp(exp1, True)

                if Compiler.is_atm(exp2):
                    (exp2_atm, exp2_temps) = (exp2, [])
                else:
                    (exp2_atm, exp2_temps) = self.rco_exp(exp2, True)

                tail = BinOp(exp1_atm, Add(), exp2_atm)
                temps = exp1_temps + exp2_temps
            case Compare(left, [cmp], [right]):
                # similar to `BinOp` case
                if Compiler.is_atm(left):
                    (left_atm, left_temps) = (left, [])
                else:
                    (left_atm, left_temps) = self.rco_exp(left, True)

                if Compiler.is_atm(right):
                    (right_atm, right_temps) = (right, [])
                else:
                    (right_atm, right_temps) = self.rco_exp(right, True)

                tail = Compare(left_atm, [cmp], [right_atm])
                temps = left_temps + right_temps
            case IfExp(exp_test, exp_body, exp_else):
                (tail, test_temps) = self.rco_exp(exp_test, False)
                tail = IfExp(tail, self.letize(exp_body), self.letize(exp_else))
                temps = test_temps
            case Call(Name('input_int'), []):
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
                (exp_rcoed, temps) = self.rco_exp(exp, False)
                tail = Assign([Name(var)], exp_rcoed)
            case If(exp, stmts_body, stmts_else):
                body_rcoed = [new_stat for s in stmts_body for new_stat in self.rco_stmt(s)]
                else_rcoed = [new_stat for s in stmts_else for new_stat in self.rco_stmt(s)]
                tail = If(exp, body_rcoed, else_rcoed)

        for binding in temps:
            result.append(Assign([binding[0]], binding[1]))

        result.append(tail)
        return result

    def remove_complex_operands(self, p: Module) -> Module:
        match p:
            case Module(stmts):
                new_stmts = [
                    new_stat for s in stmts for new_stat in self.rco_stmt(s)]
                return Module(new_stmts)

    ############################################################################
    # Explicate Control
    ############################################################################


    # def create_block(stmts, basic_blocks):
    #     label = label_name(generate_name('block'))
    #     basic_blocks[label] = stmts
    #     return Goto(label)

    def create_block(self, stmts: List[stmt], label: str = None) -> str:
        """create a block and add it to the block dict,
        return label name of the new block"""
        if not label:
            label = label_name(generate_name('block'))
        
        self.basic_blocks[label] = stmts
        return label

    def explicate_effect(self, e, cont):
        match e:
            case IfExp(test, body, orelse):
                return self.explicate_pred(test, body, orelse) + cont
            case Call(func, args):
                return [Expr(e)] + cont
            case Let(var, rhs, body):
                ...
            case _:
                return cont


    def explicate_assign(self, rhs: expr, lhs: Name, cont: List[stmt]) -> List[stmt]:
        match rhs:
            case IfExp(test, body, orelse):
                # dispatch to `explicate_pred`
                # `cont` must not be empty

                trampoline = self.create_block(cont)
                body_ss = self.explicate_assign(body, lhs, [Goto(trampoline)])
                orelse_ss = self.explicate_assign(orelse, lhs, [Goto(trampoline)])
                return self.explicate_pred(test, body_ss, orelse_ss)
            case Let(var, let_rhs, let_body):
                return [Assign([var], let_rhs)] + self.explicate_assign(let_body, lhs, []) + cont
            case _:
                return [Assign([lhs], rhs)] + cont
    
    def explicate_pred(self, cnd: expr, thn: List[stmt], els: List[stmt]):
        match cnd:
            case Compare(left, [op], [right]):
                return [If(cnd,
                    [Goto(self.create_block(thn))],
                    [Goto(self.create_block(els))])]
            case Constant(True):
                return thn
            case Constant(False):
                return els
            case UnaryOp(Not(), operand):
                # return [If(UnaryOp(Not(), operand),
                #     [Goto(self.create_block(thn))],
                #     [Goto(self.create_block(els))])]
                # change to a compare here
                return [If(Compare(operand, [Eq()], [Constant(False)]),
                    [Goto(self.create_block(thn))],
                    [Goto(self.create_block(els))])]
            case IfExp(test, body, orelse):
                # in `IfExp` inside pred, body and orelse must also be predicate
                thn_label = self.create_block(thn)
                els_label = self.create_block(els)
                # TODO: what if body/orelse is T/F?
                # body_ss = [If(body, [Goto(thn_label)], [Goto(els_label)])]
                body_ss = self.explicate_pred(body, [Goto(thn_label)], [Goto(els_label)])
                # orelse_ss = [If(orelse, [Goto(thn_label)], [Goto(els_label)])]
                orelse_ss = self.explicate_pred(orelse, [Goto(thn_label)], [Goto(els_label)])
                return self.explicate_pred(test, body_ss, orelse_ss)
            case Let(var, let_rhs, body):
                # `body must be a predicate`
                # TODO
                # print("DEBUG: Let, cnd:", cnd)
                return [Assign([var], let_rhs)] + self.explicate_pred(body, thn, els)
            case _:
                return [If(Compare(cnd, [Eq()], [Constant(False)]),
                    [Goto(self.create_block(els))],
                    [Goto(self.create_block(thn))])]

    def explicate_stmt(self, s, cont) -> List[stmt]:
        match s:
            case Assign([lhs], rhs):
                return self.explicate_assign(rhs, lhs, cont)
            case Expr(value):
                return self.explicate_effect(value, cont)
            case If(test, body, orelse):
                # `cont` must be nonempty.
                # TODO: trampoline
                trampoline = self.create_block(cont)
                self.explicate_pred(test, body, orelse)
                body_exped = self.explicate_stmts(body, [Goto(trampoline)])
                orelse_exped = self.explicate_stmts(orelse, [Goto(trampoline)])
                return self.explicate_pred(test, body_exped, orelse_exped)
                # cont = [If(test, [Goto(self.explicate_stmts(body))], [Goto(self.explicate(orelse))])] + cont

        return cont
    
    def explicate_stmts(self, ss: List[stmt], cont) -> List[stmt]:
        for s in reversed(ss):
            cont = self.explicate_stmt(s, cont)
        
        return cont

    def explicate_control(self, p: Module) -> CProgram:
        cont = [Return(Constant(0))]
        label = label_name('start')
        match p:
            case Module(body):
                new_body = self.explicate_stmts(body, cont)
                self.create_block(new_body, label)
                # print("DEBUG: .start: ", self.basic_blocks[label])
                return CProgram(self.basic_blocks)

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
                raise Exception('error in condition_abbr, cmp not supported' + repr(cmp))

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


        # pretending the variable will always be assigned
        instrs = []
        match e:
            case Call(Name('input_int'), []):
                instrs.append(Callq('read_int', 0))
                instrs.append(Instr('movq', [Reg('rax'), Variable("Unnamed_Pyc_Var")]))
            case UnaryOp(USub(), atm):
                instrs.append(Instr('movq', [self.select_arg(atm), Variable("Unnamed_Pyc_Var")]))
                instrs.append(Instr('negq', [Variable("Unnamed_Pyc_Var")]))
            case UnaryOp(Not(), atm):
                instrs.append(Instr('movq', [self.select_arg(atm), Variable("Unnamed_Pyc_Var")]))
                instrs.append(Instr('xorq', [Immediate(1), Variable("Unnamed_Pyc_Var")]))
            case Compare(atm1, [cmp], [atm2]):
                # switch atm1 and atm2
                instrs.append(Instr('cmpq', [self.select_arg(atm2), self.select_arg(atm1)]))
                instrs.append(Instr('set' + Compiler.condition_abbr(cmp), [Reg('al')]))
                instrs.append(Instr('movzbq', [Reg('al'), Variable("Unnamed_Pyc_Var")]))
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
            case _:
                instrs.append(
                    Instr('movq', [self.select_arg(e), Variable("Unnamed_Pyc_Var")]))

        return instrs

    def select_stmt(self, s: stmt) -> List[instr]:

        def bound_unamed(instrs: List[instr], var: str) -> List[instr]:
            new_instrs = []
            for i in instrs:
                match i:
                    case Instr(oprtr, args):
                        new_args = [Variable(var) if a == Variable(
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
                        instrs.append(Instr('cmpq', [self.select_arg(atm2), self.select_arg(atm1)]))
                        abbr = Compiler.condition_abbr(cmp)
                    case _:
                        raise Exception('error in select_expr, if: invlaid test ' + repr(test))
                instrs.append(JumpIf(abbr, body_label))
                instrs.append(Jump(else_label))
            case Return(rv):
                instrs.append(
                    Instr('movq', [self.select_arg(rv), Reg('rax')]))
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

        return instrs

    def select_instructions(self, p: Module) -> X86Program:
        match p:
            # case Module(stmts):
            #     insts = [inst for s in stmts for inst in self.select_stmt(s)]
            #     return X86Program(insts)
            case CProgram(blks):
                x86_blks = {}
                for (label, block) in blks.items():
                    x86_blks[label] = [inst for s in block for inst in self.select_stmt(s)]
                return X86Program(x86_blks)
            case _:
                raise Exception(
                        'error in read_write_sets, select_instructions' + repr(p))

    ############################################################################
    # Liveness after set generation
    ############################################################################

    def uncover_live(self, p: X86Program, need_list=False) -> List[Set]:

        def extract_locations(args: List[arg]) -> set:
            """extract all the locations from a list of args"""

            extracted = set()
            for a in args:
                if isinstance(a, location):
                    extracted.add(a)
                    self.int_graph.add_vertex(a)

            return extracted

        def read_write_sets(s: instr):
            """take an instrunction, return sets of its read and write locations"""

            read_set = set()
            write_set = set()

            match s:
                case Instr("movq", [src, dest]):
                    (read_set, write_set) = (extract_locations([src]), extract_locations([dest]))
                case Instr("addq", [arg1, arg2]):
                    (read_set, write_set) = (extract_locations([arg1, arg2]), extract_locations([arg2]))
                case Instr("negq", [arg]):
                    (read_set, write_set) = (extract_locations([arg]), extract_locations([arg]))
                case Callq(_func_name, num_args):
                    (read_set, write_set) = (extract_locations(Compiler.arg_passing[:num_args]), extract_locations(Compiler.caller_saved))
                case _:
                    raise Exception(
                        'error in read_write_sets, unhandled' + repr(s))

            self.read_set_dict[s] = read_set
            self.write_set_dict[s] = write_set
        
        last_set = set()

        # generate the read & write set for each instruction
        if type(p.body) == dict:
            pass
        else:  # list
            for s in reversed(p.body):
                read_write_sets(s)
                self.live_after_set_dict[s] = last_set.difference(self.write_set_dict[s]).union(self.read_set_dict[s])
                last_set = self.live_after_set_dict[s]

        # output
        if need_list:
            live_after_sets_list = []
            for s in p.body:
                live_after_sets_list.append(self.live_after_set_dict[s])
            return live_after_sets_list
        else:
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

    def build_interference(self, ins_list: list[instr], las_list: list[set]) -> bool:
        """store the interference graph in member, `self.int_graph`"""

        for i in range(len(ins_list)):
            ins = ins_list[i]  # instruction
            las = las_list[i]  # live-after set
            match ins:
                case Instr("movq", [src, dest]):
                    for loc in las:
                        self.int_graph.add_vertex(loc)
                        if not (loc == src or loc == dest):
                            self.int_graph.add_edge(loc, dest)
                case Instr("addq", [_, arg]):
                    for loc in las:
                        if not loc == arg:
                            self.int_graph.add_edge(loc, arg)
                case Instr("negq", [arg]):
                    for loc in las:
                        if not loc == arg:
                            self.int_graph.add_edge(loc, arg)
                case Callq(_func_name, _num_args):
                    for loc in las:
                        for dest in Compiler.caller_saved:
                            if not dest == loc:
                                self.int_graph.add_edge(loc, dest)
                case _:
                    raise Exception(
                        'error in build_interference, unhandled' + repr(ins))

        return True

    ############################################################################
    # graph coloring
    ############################################################################

    def color_graph(self, graph: UndirectedAdjList) -> Dict[location, int]:

        # TODO: move biasing

        saturation_dict = {}
        assign_dict = {}

        def less(x: location, y: location):
            return len(saturation_dict[x.key]) < len(saturation_dict[y.key])

        # initialize saturation_dict
        for v in graph.vertices():
            saturation_dict[v] = set()

        # check if the vertices are already a register
        for v in graph.vertices():
            if isinstance(v, Reg):
                # find key for the register in `allocation` dict
                for index, reg in self.color_reg_map.items():
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
            # skip register vertices, since they've been assigned a home
            if isinstance(v, Reg):
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

            color = 0
            # if not going into biased move
            while not colored:
                if color not in v_saturation:
                    assign_dict[v] = color
                    colored = True
                else:
                    color += 1

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

    def map_colors(self, coloring: Dict[location, int]) -> Dict[location, arg]:
        """return a dict mapping colors to registers or stack locations"""
        allocatable_reg_num = len(self.allocatable)
        result = {}
        for vertex, color in coloring.items():
            if color < allocatable_reg_num:
                result[vertex] = self.color_reg_map[color]
            else:
                result[vertex] = Deref(
                    "rbp", - (color - allocatable_reg_num + 1) * 8)
                self.stack_count += 1

        return result

    def assign_homes(self, p: X86Program) -> X86Program:

        # assuming p.body is a list
        las_list = self.uncover_live(p, True)
        self.build_interference(p.body, las_list)
        self.build_move_graph(p.body)
        coloring = self.color_graph(self.int_graph)

        # figure out which registers need saving
        for r in Compiler.callee_saved[2:]:
            # find the color of register
            color = None
            for index, reg in self.color_reg_map.items():
                if reg == r:
                    color = index
            # this color(reg) is used
            if color in coloring.values():
                self.used_callee.add(r)
        
        home = self.map_colors(coloring)

        if type(p.body) == dict:
            pass
        else:  # list
            return X86Program(self.assign_homes_instrs(p.body, home))

    ############################################################################
    # Patch Instructions
    ############################################################################

    def patch_instr(self, i: instr) -> List[instr]:
        patched_instrs = []
        match i:
            case Instr("movq", [Deref(reg1, offset1), Deref(reg2, offset2)]):
                # MOV: Two memory locations in args
                patched_instrs.append(
                    Instr("movq", [Deref(reg1, offset1), Reg("rax")]))
                patched_instrs.append(
                    Instr("movq", [Reg("rax"), Deref(reg2, offset2)]))
            case Instr("addq", [Deref(reg1, offset1), Deref(reg2, offset2)]):
                # ADD: Two memory locations in args
                patched_instrs.append(
                    Instr("movq", [Deref(reg1, offset1), Reg("rax")]))
                patched_instrs.append(
                    Instr("addq", [Reg("rax"), Deref(reg2, offset2)]))
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
        else:  # list
            return X86Program(self.patch_instrs(p.body))

    ############################################################################
    # Prelude & Conclusion
    ############################################################################

    def prelude_and_conclusion(self, p: X86Program) -> X86Program:
        stack_frame_size = ((self.stack_count + 1) // 2) * 16

        self.used_callee = list(self.used_callee)

        prelude = []
        prelude.append(Instr('pushq', [Reg('rbp')]))
        prelude.append(Instr('movq', [Reg('rsp'), Reg('rbp')]))
        for r in self.used_callee:
            prelude.append(Instr('pushq', [r]))
        prelude.append(
            Instr('subq', [Immediate(stack_frame_size), Reg('rsp')]))

        conclusion = []
        conclusion.append(
            Instr('addq', [Immediate(stack_frame_size), Reg('rsp')]))
        for r in reversed(self.used_callee):
            prelude.append(Instr('popq', [r]))
        conclusion.append(Instr('popq', [Reg('rbp')]))
        conclusion.append(Instr('retq', []))

        if type(p.body) == dict:
            pass
        else:  # list
            return X86Program(prelude + p.body + conclusion)
