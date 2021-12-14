def f(x : int) -> Callable[[int], int] :
    y = 4
    lam : Callable[[int],int] = lambda a: x + y + a
    return lam

g = f(5)
h = f(3)
print( g(11) + h(15) )