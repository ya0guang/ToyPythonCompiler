from x86_ast import *

s1 = Callq('print_int', 1)
s2 = Callq('print_int', 1)

dict = {}
dict[s1] = 1
dict[s2] = 2

print(dict)

# {       callq print_int: 1,     callq print_int: 2}