from z3 import *
aint = int(input('Input a:'))
bint = int(input('Input b:'))
if(aint < 0 or bint < 0):
    print("a b 都要大于0")
    exit()
if(aint < bint):
    fu = True
    tmp = aint
    aint = bint
    bint = tmp
else:
    fu = False
abits = []
while(aint != 0):
    abits.append(aint & 1)
    aint = aint >> 1
bbits = []
while(bint != 0):
    bbits.append(bint & 1)
    bint = bint >> 1
n = max(len(abits), len(bbits))+1
while(len(abits) < n):
    abits.append(0)
while(len(bbits) < n):
    bbits.append(0)

a = [Bool('A_%i' % (i + 1)) for i in range(n)]
b = [Bool('B_%i' % (i + 1)) for i in range(n)]
c = [Bool('C_%i' % (i + 1)) for i in range(n)]
d = [Bool('D_%i' % (i + 1)) for i in range(n)]

condition1 = True
for i in range(n):
    if(abits[i] == 1):
        condition1 = And(condition1, a[i])
    else:
        condition1 = And(condition1, Not(a[i]))
for i in range(n):
    if(bbits[i] == 1):
        condition1 = And(condition1, b[i])
    else:
        condition1 = And(condition1, Not(b[i]))
condition1 = And(condition1, Not(c[0]))

condition2 = True
for i in range(n):
    condition2 = And(condition2, d[i] == (a[i] == (b[i] == c[i])))

condition3 = True
for i in range(n-1):
    condition3 = And(
        condition3, c[i+1] == Or(And(a[i], b[i], c[i]), And(Not(a[i]), Or(b[i], c[i]))))
s = Solver()
s.add(condition1)
s.add(condition2)
s.add(condition3)
s.check()
m = s.model()
dint = 0
for i in range(n):
    if m.evaluate(d[i]):
        dint += 2**i
if(fu):
    print('-'+str(dint))
else:
    print(dint)
