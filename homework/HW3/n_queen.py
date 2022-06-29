from z3 import *
from timeit import default_timer as timer

def Solve_SMT(n, print_result):
    '''
    使用SMT求解n皇后问题, print_result设置为True时输出求解结果, 否则不输出结果
    '''
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
    s.check()
    toc = timer()
    print('SMT Solver for %d queens Time(sec): '%n, end='')
    print(toc - tic)
    if print_result:
        print(s.model())


def Solve_SAT(n, print_result):
    '''
    使用SAT求解n皇后问题, print_result设置为True时输出求解结果, 否则不输出结果
    '''
    p = [[] for i in range(n)]
    for i in range(n):
        for j in range(n):
            p[i].append(Bool('p_%i%i' % (i+1, j+1)))

    row_c1 = []
    for i in range(n):
        bool_vector = []
        for j in range(n):
            bool_vector.append(p[i][j])
        row_c1.append(Or(bool_vector))

    row_c2 = []
    for i in range(n):
        for k in range(2, n):
            for j in range(k):
                row_c2.append(Or(Not(p[i][j]), Not(p[i][k])))

    col_c1 = []
    for j in range(n):
        bool_vector = []
        for i in range(n):
            bool_vector.append(p[i][j])
        col_c1.append(Or(bool_vector))

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
Solve_SMT(40, False)
Solve_SAT(40, False)
for n in range(8, 41):
    Solve_SMT(n, False)
    Solve_SAT(n, False)
    print('')
