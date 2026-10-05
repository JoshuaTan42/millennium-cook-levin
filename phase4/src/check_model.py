"""Independent model evaluator: shares no code with the solver.
Usage: python check_model.py formula.cnf solver_output.txt  -> prints OK / FAIL with reason, exit code 0/1."""
import sys


def read_cnf(path):
    nv = None
    clauses = []
    cur = []
    with open(path) as f:
        for line in f:
            if line.startswith('%'):
                break                      # SATLIB end-of-file marker
            if not line.strip() or line[0] == 'c':
                continue
            if line.startswith('p'):
                nv = int(line.split()[2])
                continue
            for tok in line.split():
                v = int(tok)
                if v == 0:
                    clauses.append(cur); cur = []
                else:
                    cur.append(v)
    if cur:
        clauses.append(cur)
    return nv, clauses


def read_model(path):
    lits = []
    status = None
    with open(path) as f:
        for line in f:
            if line.startswith('s '):
                status = line.split()[1]
            elif line.startswith('v'):
                lits.extend(int(t) for t in line.split()[1:])
    lits = [l for l in lits if l != 0]
    return status, lits


def main():
    nv, clauses = read_cnf(sys.argv[1])
    status, lits = read_model(sys.argv[2])
    if status != 'SATISFIABLE':
        print('NOT-SAT-OUTPUT', status); sys.exit(2)
    asg = {}
    for l in lits:
        v = abs(l)
        if v in asg and asg[v] != (l > 0):
            print('FAIL inconsistent assignment on variable', v); sys.exit(1)
        asg[v] = (l > 0)
    missing = [v for v in range(1, nv + 1) if v not in asg]
    if missing:
        print('FAIL unassigned variables', missing[:10]); sys.exit(1)
    for i, cl in enumerate(clauses):
        if not any(asg.get(abs(l), None) == (l > 0) for l in cl):
            print('FAIL clause', i, cl, 'falsified'); sys.exit(1)
    print('OK model satisfies all', len(clauses), 'clauses over', nv, 'variables')
    sys.exit(0)


if __name__ == '__main__':
    main()
