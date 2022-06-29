from z3 import *
from timeit import default_timer as timer

def Solve_SMT(n, print_result):
    Q = [Int('Q%i' % (i+1)) for i in range(n)]
    val_c = [And(Q[i] >= 1, Q[i] <= n) for i in range(n)]
    col_c = [Distinct(Q)]
    diag_c = [If(i == j, True, And(i+Q[i] != j+Q[j], i+Q[j] != j+Q[i]))
              for i in range(n) for j in range(i)]
    s = Solver()
    s.add(val_c)
    s.add(col_c)
    s.add(diag_c)
    tic = timer()
    # solve(val_c + col_c + diag_c)
    s.check()
    toc = timer()
    print('SMT Solver for %d queens Time(sec): '%n, end='')
    print(toc - tic)
    if print_result:
        print(s.model())


def Solve_SAT(n, print_result):
    p = [[] for i in range(n)]
    for i in range(n):
        for j in range(n):
            p[i].append(Bool('p_%i%i' % (i+1, j+1)))
    # row_c1 = [Or(p[i][0], p[i][1], p[i][2], p[i][3], p[i][4],
                # p[i][5], p[i][6], p[i][7]) for i in range(8)]
    row_c1 = []
    for i in range(n):
        bool_vector = []
        for j in range(n):
            bool_vector.append(p[i][j])
        row_c1.append(Or(bool_vector))

    # row_c2 = [Or(Not(p[i][j]), Not(p[i][k])) for k in range(2, 8)
            # for j in range(k) for i in range(8)]
    row_c2 = []
    for i in range(n):
        for k in range(2, n):
            for j in range(k):
                row_c2.append(Or(Not(p[i][j]), Not(p[i][k])))

    # col_c1 = [Or(p[0][j], p[1][j], p[2][j], p[3][j], p[4][j],
                # p[5][j], p[6][j], p[7][j]) for j in range(8)]
    col_c1 = []
    for j in range(n):
        bool_vector = []
        for i in range(n):
            bool_vector.append(p[i][j])
        col_c1.append(Or(bool_vector))

    # col_c2 = [Or(Not(p[i][j]), Not(p[k][j])) for k in range(2, 8)
            # for i in range(k) for j in range(8)]
    col_c2 = []
    for j in range(n):
        for k in range(2, n):
            for i in range(k):
                col_c2.append(Or(Not(p[i][j]), Not(p[k][j])))

    diag_c = []
    for i in range(n-1):
        for i1 in range(i+1, n):
            for j in range(n):
                for j1 in range(n):
                    if i+j == i1+j1 or i-j == i1-j1:
                        diag_c.append(Or(Not(p[i][j]), Not(p[i1][j1])))
    # solve(row_c1 + row_c2 + col_c1 + col_c2 + diag_c)
    s = Solver()
    s.add(row_c1)
    s.add(row_c2)
    s.add(col_c1)
    s.add(col_c2)
    s.add(diag_c)
    tic = timer()
    s.check()
    toc = timer()
    print('SAT Solver for %d queens Time(sec): '%n, end='')
    print(toc - tic)
    if print_result:
        for i in range(n):
            for j in range(n):
                print(s.model().eval(p[i][j]), end=' ')
            print('')


# main
for n in range(8, 40):
    Solve_SMT(n, False)
    Solve_SAT(n, False)
    print('')
