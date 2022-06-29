import sys
import copy

prop_count = 0
decide_count = 0
true_vars = set()
false_vars = set()

def negation(p):
    return '!' + p

def is_negation(literal):
    if '!' in literal:
        return True
    else:
        return False

def read_cnf(filename):
    f = open(filename, 'r')
    lines = f.read().splitlines()
    cnf = []
    for line in lines:
        cnf.append(line.split())
    return cnf

def get_variables(units):
    variables = set()
    for literal in units:
        if len(literal) == 2:
            variables.add(literal[1])
        elif len(literal) == 1:
            variables.add(literal[0])
        else:
            print('--invalid literal!!')
    return variables

def false_derived(units):
    variables = get_variables(units)
    for p in variables:
        if p in units and negation(p) in units:
            return True
    return False

def get_units(X):
    units = {clause[0] for clause in X if len(clause) == 1}
    return units

def unit_resol(X):
    units = get_units(X)
    if len(units) == 0:
        return {}
        
    # observation: a unit only can be resolved once!!
        
    # unit-resolution
    local_true = set()
    local_false = set()
    while len(units) > 0:
        # print('units:', end=' ')
        # print(units)
        l = units.pop()
        if not is_negation(l): # l is an atom without nagation
            local_true.add(l)
            # remove all clauses containing literal l
            # remove !l from all clauses containing !l
            nl = negation(l)
            i = 0
            while True:
                if nl in X[i]:
                    X[i].remove(nl)
                elif l in X[i]:
                    X.remove(X[i])
                    i -= 1
                i += 1
                if i >= len(X):
                    break
        else: # l is a negation atom !p
            p = l[1]
            local_false.add(p)
            # remove p from all clause containing p
            # remove all clauses containing l
            i = 0
            while True:
                if l in X[i]:
                    X.remove(X[i])
                    i -= 1
                elif p in X[i]:
                    X[i].remove(p)
                i += 1
                if i >= len(X):
                    break
        # print('after unit propagation of %s, X:'%l, end=' ')
        # print(X)
        units = units.union(get_units(X))
        if false_derived(units):
            X.append('False')
            return {}
                        
    # print('after unit propagation X:', end=' ')
    # print(X)
    
    i = 0
    if len(X) > 0: # clear empty clauses
        while True:
            if len(X[i]) == 0:
                X.remove(X[i])
                i -= 1
            i += 1
            if i >= len(X):
                break
            
    local_assignment = {}
    local_assignment['true'] = local_true
    local_assignment['false'] = local_false
    return local_assignment
    
def choose_variable(X):
    if len(X) > 0:
        literal = X[0][0]
        if '!' in literal:
            return literal[1]
        else:
            return literal

def dpll(cnf):
    global true_vars, false_vars
    local_assignment = unit_resol(cnf)
    if 'False' in cnf:
        return False
    elif len(cnf) == 0:
        true_vars = true_vars.union(local_assignment['true'])
        false_vars = false_vars.union(local_assignment['false'])
        return True
    else:
        # choose a variable p in cnf
        # DPLL(cnf ∪ {p})
        # DPLL(cnf ∪ {!p})
        cnf_bak = copy.deepcopy(cnf)
        p = choose_variable(cnf)
        new_clause = [p]
        cnf.append(new_clause)
        ret1 = dpll(cnf)
        if ret1 == True:
            true_vars = true_vars.union(local_assignment['true'])
            false_vars = false_vars.union(local_assignment['false'])
            return True
        cnf = cnf_bak
        new_clause = ['!'+p]
        cnf.append(new_clause)
        ret2 = dpll(cnf)
        if ret2 == True:
            if len(local_assignment) > 0:
                true_vars = true_vars.union(local_assignment['true'])
                false_vars = false_vars.union(local_assignment['false'])
            return True
        return False

def print_sat(cnf):
    print('the SAT to solve:')
    for k in range(len(cnf)):
        if k > 0:
            print(' ∧ ', end='')
        clause = cnf[k]
        print('(', end='')
        for i in range(len(clause)):
            if i > 0:
                print(' ∨ ', end='')
            print(clause[i], end='')
        print(')', end='')
    print()
    
if __name__ == '__main__':
    filename = sys.argv[1]
    # filename = 'test1.txt'
    print('input file: %s'%filename)
    cnf = read_cnf(filename)
    print_sat(cnf)
    ret = dpll(cnf)
    if ret == True:
        print('satisfiable')
        print('true list:', end=' ')
        print(true_vars)
        print('false list:', end=' ')
        print(false_vars)
    else:
        print('unsatifiable')