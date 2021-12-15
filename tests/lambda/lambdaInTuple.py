lam : Callable[[int],int] = lambda a: a + a 
tup = (3, lam )

print( tup[1](10) )