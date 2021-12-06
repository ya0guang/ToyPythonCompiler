from ast import *
from type_check_Lwhile import TypeCheckLwhile
from utils import *
import typing

class TypeCheckLtup(TypeCheckLwhile):

  def check_type_equal(self, t1, t2, e):
    match t1:
      case TupleType(ts1):
        match t2:
          case TupleType(ts2):
            for (ty1, ty2) in zip(ts1,ts2):
              self.check_type_equal(ty1, ty2, e)
          case _:
            raise Exception('error: ' + repr(t1) + ' != ' + repr(t2) \
                      + ' in ' + repr(e))
      case _:
        super().check_type_equal(t1, t2, e)
  
  def type_check_exp(self, e, env):
    match e:
      case Compare(left, [cmp], [right]) if isinstance(cmp, Is):
        l = self.type_check_exp(left, env)
        r = self.type_check_exp(right, env)
        self.check_type_equal(l, r, e)
        return bool
      case Tuple(es, Load()):
        ts = [self.type_check_exp(e, env) for e in es]
        e.has_type = TupleType(ts)
        return e.has_type
      case Subscript(tup, Constant(index), Load()):
        tup_ty = self.type_check_exp(tup, env)
        index_ty = self.type_check_exp(Constant(index), env)
        self.check_type_equal(index_ty, int, index)
        match tup_ty:
          case TupleType(ts):
            return ts[index]
          case _:
            raise Exception('error: expected a tuple, not ' + repr(tup_ty))
      case Call(Name('len'), [tup]):
        tup_t = self.type_check_exp(tup, env)
        match tup_t:
          case TupleType(ts):
            return int
          case Bottom():
            return Bottom()
          case _:
            raise Exception('error, expected a tuple, not ' + repr(tup_t))
      case _:
        return super().type_check_exp(e, env)

if __name__ == "__main__":
  t1 = Tuple([Constant(1), Constant(2)], Load())
  t1_at_0 = Subscript(t1, Constant(0), Load())
  pr = Expr(Call(Name('print'), [t1_at_0]))
  p = Module([pr])
  TypeCheckLtup().type_check(p)

