from z3 import Int, Distinct, And, Solver, sat, Or

n = 3
matrix = [[Int(f"x_{i}_{j}") for j in range(n)] for i in range(n)]

solver = Solver()

distinct_numbers = [matrix[i][j] for i in range(n) for j in range(n)]
solver.add(Distinct(distinct_numbers))
solver.add(
    [And(matrix[i][j] >= 1, matrix[i][j] <= 9) for i in range(n) for j in range(n)]
)

while solver.check() == sat:
    model = solver.model()
    solution = [[model.evaluate(matrix[i][j]) for j in range(n)] for i in range(n)]
    print("Solution:")
    for row in solution:
        print(row)

    solver.add(
        Or(
            [
                matrix[i][j] != model.evaluate(matrix[i][j])
                for i in range(n)
                for j in range(n)
            ]
        )
    )
