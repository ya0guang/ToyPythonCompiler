def sum(x:int)-> int :
    if x == 0:
        return 0
    else:
        return x + sum(x - 1)
print(sum(3) + 36)