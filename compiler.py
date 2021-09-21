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
                new_stmts = [
                    new_stat for s in stmts for new_stat in self.rco_stmt(s)]
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
                instrs.append(
                    Instr('movq', [Reg('rax'), Variable("Unnamed_Pyc_Var")]))
            case UnaryOp(USub(), atm):
                instrs.append(
                    Instr('movq', [self.select_arg(atm), Variable("Unnamed_Pyc_Var")]))
                instrs.append(Instr('negq', [Variable("Unnamed_Pyc_Var")]))
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
            case Expr(Call(Name('print'), [atm])):
                instrs.append(
                    Instr('movq', [self.select_arg(atm), Reg('rdi')]))
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

        def read_write_sets(s: instr) -> Tuple[set]:
            """take an instrunction, return sets of its read and write locations"""

            match s:
                case Instr("movq", [src, dest]):
                    return (extract_locations([src]), extract_locations([dest]))
                case Instr("addq", [arg1, arg2]):
                    return (extract_locations([arg1, arg2]), extract_locations([arg2]))
                case Instr("negq", [arg]):
                    return (extract_locations([arg]), extract_locations([arg]))
                case Callq(_func_name, num_args):
                    # print("DEBUG: in callq case, num_args: ", num_args)
                    return (extract_locations(Compiler.arg_passing[:num_args]), extract_locations(Compiler.caller_saved))
                    # print("DEBUG" + str(tmp))
                    # return tmp
                case _:
                    raise Exception(
                        'error in read_write_sets, unhandled' + repr(s))

        def previous_las(s: instr, next_las: set) -> set:
            """calculate the live after set of the previous instruction"""

            (read_set, write_set) = read_write_sets(s)

            return next_las.difference(write_set).union(read_set)

        live_after_dict = {}
        live_after_sets = []
        last_set = set()

        if type(p.body) == dict:
            pass
        else:  # list
            for s in reversed(p.body):
                live_after_dict[s] = last_set
                live_after_sets.insert(0, previous_las(s, last_set))
                last_set = live_after_sets[0]
            live_after_sets.append(set())

        if need_list:
            return live_after_sets[1:]
        else:
            return live_after_dict

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

        for r in Compiler.callee_saved:
            if self.color_reg_map[r] in coloring.values():
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

        prelude = []
        prelude.append(Instr('pushq', [Reg('rbp')]))
        prelude.append(Instr('movq', [Reg('rsp'), Reg('rbp')]))
        for r in self.callee_saved:
            prelude.append(Instr('pushq', [r]))
        prelude.append(
            Instr('subq', [Immediate(stack_frame_size), Reg('rsp')]))

        conclusion = []
        conclusion.append(
            Instr('addq', [Immediate(stack_frame_size), Reg('rsp')]))
        for r in self.callee_saved:
            prelude.append(Instr('popq', [r]))
        conclusion.append(Instr('popq', [Reg('rbp')]))
        conclusion.append(Instr('retq', []))

        if type(p.body) == dict:
            pass
        else:  # list
            return X86Program(prelude + p.body + conclusion)
