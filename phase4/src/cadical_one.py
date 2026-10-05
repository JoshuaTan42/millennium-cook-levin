"""Solve one DIMACS file with CaDiCaL 1.9.5 (PySAT) and print a JSON line; run under a hard subprocess timeout by the caller.
If SAT, the model is verified here by direct evaluation (no solver code involved in the check).
DIMACS is parsed here (PySAT's parser rejects the SATLIB '%' end marker)."""
import sys, json, time
from pysat.solvers import Cadical195


def read_cnf(path):
    nv = None; clauses = []; cur = []
    with open(path) as f:
        for line in f:
            if line.startswith('%'):
                break
            if not line.strip() or line[0] == 'c':
                continue
            if line.startswith('p'):
                nv = int(line.split()[2]); continue
            for tok in line.split():
                v = int(tok)
                if v == 0:
                    clauses.append(cur); cur = []
                else:
                    cur.append(v)
    if cur:
        clauses.append(cur)
    return nv, clauses


path = sys.argv[1]
nv, clauses = read_cnf(path)
t0 = time.time()
with Cadical195(bootstrap_with=clauses) as s:
    r = s.solve()
    dt = time.time() - t0
    model_ok = None
    if r:
        m = set(s.get_model())
        model_ok = all(any(l in m for l in cl) for cl in clauses)
print(json.dumps(dict(result=('SAT' if r else 'UNSAT'), time=round(dt, 3), model_ok=model_ok, nvars=nv, nclauses=len(clauses))))
