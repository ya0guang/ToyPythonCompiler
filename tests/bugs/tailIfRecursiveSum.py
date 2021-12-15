def sum(x:int,s:int)-> int :
    if x == 0:
        return s
    else:
        return sum(x - 1, x + s)
print(sum(3, 0) + 36)