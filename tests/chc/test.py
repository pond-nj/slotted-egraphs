def g(n):
    c = n
    if n == 0:
        return 0
    g(n - 1)
    return c


print(g(2))
