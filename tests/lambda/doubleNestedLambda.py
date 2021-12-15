def f(x : int) -> Callable[[int], Callable[[int], Callable[[int], int]]]:
    y = 4
    return lambda z : (lambda a: lambda b: x + y) 

g = f(5)
h = f(3)
print( g(11)(34)(1) + h(15)(34)(2) )