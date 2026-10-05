"""Solver verification before any measurement (pre-registered rule: every SAT answer checked by the independent
evaluator, every UNSAT answer cross-checked against CaDiCaL and its proof checked by an independent PR checker).

Generates small random and structured CNFs, runs sdcl.exe in all three modes with proof logging, and checks:
  * answer agrees with CaDiCaL 1.9.5 (PySAT);
  * SAT: model verified by check_model.py (independent evaluator);
  * UNSAT: proof verified by dpr-trim (Heule's checker) AND by prcheck.py (own pure-Python checker).
Any disagreement is printed and counted.  Python output is evidence, never proof.
"""
import os, sys, random, subprocess, json, time
from pysat.formula import CNF
from pysat.solvers import Cadical195
from cnfgen import PigeonholePrinciple, TseitinFormula, MutilatedChessboard, CliqueColoring, RandomKCNF
import networkx as nx

HERE = os.path.dirname(os.path.abspath(__file__))
SDCL = os.path.join(HERE, 'sdcl.exe')
DPRTRIM = os.path.normpath(os.path.join(HERE, '..', 'tools', 'dpr-trim', 'dpr-trim.exe'))
TMP = os.path.normpath(os.path.join(HERE, '..', 'results', 'fuzz', 'seed' + (sys.argv[1] if len(sys.argv) > 1 else '0')))
os.makedirs(TMP, exist_ok=True)


def write_cnf(path, nv, clauses):
    with open(path, 'w', newline='\n') as f:
        f.write('p cnf %d %d\n' % (nv, len(clauses)))
        for c in clauses:
            f.write(' '.join(map(str, c)) + ' 0\n')


def cnfgen_clauses(F):
    s = F.to_dimacs()
    nv = None; cls = []
    for line in s.splitlines():
        if line.startswith('p'):
            nv = int(line.split()[2]); continue
        if not line.strip() or line[0] == 'c':
            continue
        toks = [int(t) for t in line.split()]
        cls.append(toks[:-1])
    return nv, cls


def gen_random(rng):
    n = rng.randint(5, 60)
    ratio = rng.choice([2.0, 3.0, 4.0, 4.26, 4.5, 5.0, 6.0])
    m = max(1, int(n * ratio))
    cls = []
    for _ in range(m):
        k = rng.choice([1, 2, 2, 3, 3, 3, 3, 4, 5])
        k = min(k, n)
        vs = rng.sample(range(1, n + 1), k)
        cls.append([v if rng.random() < 0.5 else -v for v in vs])
    return n, cls, 'rand n=%d m=%d' % (n, m)


def gen_structured(rng):
    kind = rng.choice(['php', 'tseitin', 'mchess', 'cliquecol', 'rand3'])
    if kind == 'php':
        h = rng.randint(2, 7); F = PigeonholePrinciple(h + 1, h); desc = 'php %d' % h
    elif kind == 'tseitin':
        n = rng.choice([4, 6, 8, 10, 12, 14]); G = nx.random_regular_graph(3, n, seed=rng.randint(0, 10**6))
        charges = [rng.random() < 0.5 for _ in range(n)]
        F = TseitinFormula(G, charges=charges); desc = 'tseitin n=%d parity=%d' % (n, sum(charges) % 2)
    elif kind == 'mchess':
        w = rng.randint(2, 6); h = rng.randint(2, 6); F = MutilatedChessboard(w, h); desc = 'mchess %dx%d' % (w, h)
    elif kind == 'cliquecol':
        n = rng.randint(4, 8); k = rng.randint(2, 4); c = rng.randint(1, 4); F = CliqueColoring(n, k, c); desc = 'cliquecol %d %d %d' % (n, k, c)
    else:
        n = rng.randint(10, 60); F = RandomKCNF(3, n, int(4.26 * n), seed=rng.randint(0, 10**6)); desc = 'rand3 n=%d' % n
    nv, cls = cnfgen_clauses(F)
    return nv, cls, desc


def run_case(idx, nv, cls, desc, modes=('sdcl', 'plain', 'unfiltered')):
    path = os.path.join(TMP, 'case%d.cnf' % idx)
    write_cnf(path, nv, cls)
    if any(len(c) == 0 for c in cls):
        ref = False                       # an empty clause: trivially UNSAT (PySAT rejects empty clauses)
    else:
        with Cadical195(bootstrap_with=cls) as s:
            ref = s.solve()
    problems = []
    for mode in modes:
        proof = os.path.join(TMP, 'case%d.%s.dpr' % (idx, mode))
        out = os.path.join(TMP, 'case%d.%s.out' % (idx, mode))
        t0 = time.time()
        p = subprocess.run([SDCL, '--mode=' + mode, '--proof=' + proof, '--time-limit=120', path], capture_output=True, text=True)
        dt = time.time() - t0
        open(out, 'w').write(p.stdout)
        status = None
        for line in p.stdout.splitlines():
            if line.startswith('s '):
                status = line.split()[1]
        if status == 'SATISFIABLE':
            if ref is not True:
                problems.append('%s: solver SAT but CaDiCaL UNSAT' % mode)
            m = subprocess.run([sys.executable, os.path.join(HERE, 'check_model.py'), path, out], capture_output=True, text=True)
            if m.returncode != 0:
                problems.append('%s: model check failed: %s' % (mode, m.stdout.strip()))
        elif status == 'UNSATISFIABLE':
            if ref is not False:
                problems.append('%s: solver UNSAT but CaDiCaL SAT' % mode)
            d = subprocess.run([DPRTRIM, path, proof], capture_output=True, text=True)
            if 's VERIFIED' not in d.stdout:
                problems.append('%s: dpr-trim did not verify: %s' % (mode, d.stdout.strip().splitlines()[-1:] ))
            c = subprocess.run([sys.executable, os.path.join(HERE, 'prcheck.py'), path, proof], capture_output=True, text=True)
            if not c.stdout.startswith('VERIFIED'):
                problems.append('%s: prcheck.py did not verify: %s' % (mode, c.stdout.strip()[:200]))
        else:
            problems.append('%s: status %s (rc=%d) after %.1fs' % (mode, status, p.returncode, dt))
    return problems


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 0
    count = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    rng = random.Random(seed)
    nbad = 0; nsat = nunsat = 0
    for i in range(count):
        if i % 3 == 2:
            nv, cls, desc = gen_structured(rng)
        else:
            nv, cls, desc = gen_random(rng)
        probs = run_case(i, nv, cls, desc)
        if any(len(c) == 0 for c in cls):
            nunsat += 1
        else:
            with Cadical195(bootstrap_with=cls) as s:
                if s.solve(): nsat += 1
                else: nunsat += 1
        if probs:
            nbad += 1
            print('CASE %d (%s): PROBLEMS' % (i, desc), probs, flush=True)
        elif i % 20 == 0:
            print('case %d ok (%s)' % (i, desc), flush=True)
    print('DONE seed=%d cases=%d bad=%d sat=%d unsat=%d' % (seed, count, nbad, nsat, nunsat))


if __name__ == '__main__':
    main()
