def foo(x: int, y: int, z: int) -> Callable[[int],int]:
    x = 100
    y = 200
    bar: Callable[[int],int] = lambda x: x + y + z
    z = 10
    return bar

z = 30
print(foo(1, 2, z)(1))