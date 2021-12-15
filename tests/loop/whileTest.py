sum = 0
m = 5#input_int()
n = 3#input_int()
i = 1
while i < m:
    j = 1
    while j < n:
        sum = sum + i + j
        j = j + 1
    i = i + 1
print(sum)