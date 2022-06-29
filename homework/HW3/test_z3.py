from z3 import *
x = Int('x')
y = Int('y')
constraint = And(x>2, y<10, x + 2*y == 7)
# solve(x>2, y<10, x+2*y == 7)
solve(constraint)

n = 8
bool_vector = []
for i in range(n):
    bool_vector.append(Bool('p_%i'%(i+1)))
print(Or(bool_vector))