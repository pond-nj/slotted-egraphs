# from z3 import *
from pysat.solvers import Solver
import time
import random
import numpy as np

n = 100
nFact = 1
for i in range(n):
    nFact *= i + 1

dummySearchTime = 0.01

nSquare = n * n


# time a function
def timeit(f):
    def wrap(*args, **kw):
        start = time.time()
        res = f(*args, **kw)
        end = time.time()
        total = end - start
        return res, total

    return wrap


# proportion can be 1, nFact * 1/4, nFact /2, nFact * 3/4, etc.
@timeit
def permuteAll(proportion):
    for i in range(nFact):
        time.sleep(dummySearchTime * n)
        prob = min(1 * proportion / (nFact - i), 1)
        res = np.random.binomial(1, prob, 1)
        if res[0] == 1:
            break

    return 1


@timeit
def encode(prob):
    # for i in range(nSquare):
    #     time.sleep(dummySearchTime)

    v = [
        [bool(np.random.binomial(1, prob, 1)[0] == 1) for j in range(n)]
        for i in range(n)
    ]

    # v = [[(i == j) for j in range(n)] for i in range(n)]
    # x = [[Bool("x_%d_%d" % (i, j)) for j in range(n)] for i in range(n)]

    # s = Solver()
    # for i in range(n):
    #     for j in range(n):
    #         notClause = []
    #         for k in range(n):
    #             if k != i:
    #                 notClause.append(x[k][j])

    #         s.add(Implies(x[i][j], Not(Or(notClause))))

    #     selectClause = []
    #     for j in range(n):
    #         selectClause.append(And(x[i][j], v[i][j]))
    #     s.add(Or(selectClause))

    # if s.check() == sat:
    #     return 1
    # else:
    #     return 0

    s = Solver()
    x = []
    count = 1
    for i in range(n):
        tmp = []
        for j in range(n):
            tmp.append(count)
            count += 1
        x.append(tmp)

    for i in range(n):
        for j in range(n):
            for k in range(j + 1, n):
                s.add_clause([-x[k][i], -x[j][i]])
    for i in range(n):
        tmp = []
        for j in range(n):
            if v[i][j]:
                tmp.append(x[i][j])
        s.add_clause(tmp)
    if s.solve():
        return 1
    else:
        return 0


def testEncode(repeat):
    def test(prob):
        totalSat, sumEncode = 0, 0
        for i in range(repeat):
            res = encode(prob)
            totalSat += res[0]
            sumEncode += res[1]
        print(sumEncode, totalSat)

    print("1/n")
    test(1 / n)
    print("0.2")
    test(0.2)
    print("0.5")
    test(0.5)
    print("0.9")
    test(0.9)


def testPermuteAll(repeat):
    sumPermuteAll = 0
    for i in range(repeat):
        sumPermuteAll += permuteAll(1)
    print("1", sumPermuteAll)

    sumPermuteAll = 0
    for i in range(repeat):
        sumPermuteAll += permuteAll(nFact * 1 / 4)
    print("nFact * 1/4", sumPermuteAll)

    sumPermuteAll = 0
    for i in range(repeat):
        sumPermuteAll += permuteAll(nFact / 2)
    print("nFact / 2", sumPermuteAll)

    sumPermuteAll = 0
    for i in range(repeat):
        sumPermuteAll += permuteAll(nFact * 3 / 4)
    print("nFact * 3/4", sumPermuteAll)


repeat = 10
testEncode(repeat)
testPermuteAll(repeat)
