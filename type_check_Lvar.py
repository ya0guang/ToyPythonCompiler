from ast import *

def check_type_equal(t1, t2, e):
  if t1 != t2:
    raise Exception('error: ' + repr(t1) + ' != ' + repr(t2) + ' in ' + repr(e))

class TypeCheckLvar:
          
  def type_check_exp(self, e, env):
    match e:
      case BinOp(left, Add(), right):
        l = self.type_check_exp(left, env)
        check_type_equal(l, int, left)
        r = self.type_check_exp(right, env)
        check_type_equal(r, int, right)
        return int
      case UnaryOp(USub(), v):
        t = self.type_check_exp(v, env)
        check_type_equal(t, int, v)
        return int
      case Name(id):
        return env[id]
      case Constant(value) if isinstance(value, int):
        return int
      case Call(Name('input_int'), []):
        return int
      case _:
        raise Exception('error in type_check_exp, unexpected ' + repr(e))

  def type_check_stmts(self, ss, env):
    if len(ss) == 0:
      return
    match ss[0]:
      case Assign([Name(id)], value):
        t = self.type_check_exp(value, env)
        if id in env:
          check_type_equal(env[id], t, value)
        else:
          env[id] = t
        return self.type_check_stmts(ss[1:], env)
      case Expr(Call(Name('print'), [arg])):
        t = self.type_check_exp(arg, env)
        check_type_equal(t, int, arg)
        return self.type_check_stmts(ss[1:], env)
      case Expr(value):
        self.type_check_exp(value, env)
        return self.type_check_stmts(ss[1:], env)
      case _:
        raise Exception('error in type_check_stmt, unexpected ' + repr(ss))

  def type_check(self, p):
    match p:
      case Module(body):
        self.type_check_stmts(body, {})