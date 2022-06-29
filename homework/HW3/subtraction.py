from z3 import *
from timeit import default_timer as timer

def subtraction(a, b):
    '''
    输入被减数a和减数b, 使用SAT方法计算a-b后输出计算结果
    '''
    if a < b:
        print("a < b, try again")
        return

    Abit = []
    while True:
        bit = a % 2
        Abit.append(bit)
        a = a // 2
        if a == 0:
            break
    Abit.append(0)
    Abit.reverse()

    Bbit = []
    while True:
        bit = b % 2
        Bbit.append(bit)
        b = b // 2
        if b == 0:
            break
    Bbit.append(0)
    Bbit.reverse()

    if len(Abit) > len(Bbit):
        Bbit.reverse()
        while len(Bbit) < len(Abit):
            Bbit.append(0)
        Bbit.reverse()
    elif len(Bbit) > len(Abit):
        Abit.reverse()
        while len(Abit) < len(Bbit):
            Abit.append(0)
        Abit.reverse()

    print(Abit)
    print(Bbit)
    # 取B的补码
    for i in range(len(Bbit)):
        Bbit[i] = 1 - Bbit[i]
    c = 1
    Bbit.reverse()
    for i in range(len(Abit)):
        temp = Bbit[i]
        Bbit[i] = (Bbit[i] + c) % 2
        c = (temp + c) // 2
    Bbit.reverse()

    
    print(Bbit)

    n = len(Abit)
    A = [Bool('a%i'%i) for i in range(n+1)]
    B = [Bool('b%i'%i) for i in range(n+1)]
    C = [Bool('c%i'%i) for i in range(n+1)]
    D = [Bool('d%i'%i) for i in range(n+1)]
    
    cons1 = True
    for i in range(1, n+1):
        cons1 = And(cons1, D[i] == (A[i] == (B[i] == C[i])))

    cons2 = True
    for i in range(1, n+1):
        cons2 = And(cons2, C[i-1] == (Or(And(A[i], B[i]), And(A[i], C[i]), And(B[i], C[i]))))

    cons3 = Not(C[n])
    # cons4 = Not(C[0])

    cons5 = True
    for i in range(1, n+1):
        if Abit[i-1] == 1:
            cons5 = And(cons5, A[i])
        else:
            cons5 = And(cons5, Not(A[i]))
    
    cons6 = True
    for i in range(1, n+1):
        if Bbit[i-1] == 1:
            cons6 = And(cons6, B[i])
        else:
            cons6 = And(cons6, Not(B[i]))

    s = Solver()
    # cons = [cons1, cons2, cons3, cons4, cons5, cons6]
    cons = [cons1, cons2, cons3, cons5, cons6]
    s.add(cons)

    tic = timer()
    s.check()
    toc = timer()
    print(toc - tic)
    result_bit = []
    for i in range(1, n+1):
        if s.model().eval(D[i]) == True:
            result_bit.append(1)
        else:
            result_bit.append(0)
    exp = 1
    result = 0
    for i in range(n-1, -1, -1):
        result += exp * result_bit[i]
        exp *= 2
    print(result)

subtraction(586, 423)
