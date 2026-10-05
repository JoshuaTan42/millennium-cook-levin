"""Phase 4 instance generator (pre-registered families F1-F6, F8; F7 is handled by label_f7.py).
Writes DIMACS files under phase4/instances/<family>/ and a manifest (JSON lines) with SHA-256 hashes.
Python output is evidence, never proof."""
import os, sys, json, hashlib, math, random, re, shutil, glob
import networkx as nx
import sympy
from cnfgen import PigeonholePrinciple, TseitinFormula, CliqueColoring, RandomKCNF, MutilatedChessboard

HERE = os.path.dirname(os.path.abspath(__file__))
INST = os.path.normpath(os.path.join(HERE, '..', 'instances'))


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def write_clauses(path, nvars, clauses, comments=()):
    with open(path, 'w', newline='\n') as f:
        for c in comments:
            f.write('c ' + c + '\n')
        f.write('p cnf %d %d\n' % (nvars, len(clauses)))
        for cl in clauses:
            f.write(' '.join(str(l) for l in cl) + ' 0\n')


def write_cnfgen(path, F, comments=()):
    s = F.to_dimacs()
    if not s.endswith('\n'):
        s += '\n'
    with open(path, 'w', newline='\n') as f:
        for c in comments:
            f.write('c ' + c + '\n')
        f.write(s)


def header(path):
    with open(path) as f:
        for line in f:
            if line.startswith('p cnf'):
                _, _, n, m = line.split()
                return int(n), int(m)
    raise ValueError(path)


manifest = []


def record(family, name, path, label, params, size_key):
    n, m = header(path)
    manifest.append(dict(family=family, name=name, path=os.path.relpath(path, INST).replace('\\', '/'),
                         nvars=n, nclauses=m, sha256=sha256(path), label=label, params=params, size=size_key))


# ---------------- F1: random 3-SAT at m/n = 4.26 (CNFgen seeds 0-19) + SATLIB uf/uuf first 10 ----------------
SATLIB_M = {50: 218, 75: 325, 100: 430, 125: 538, 150: 645, 175: 753, 200: 860, 225: 960, 250: 1065}


def f1():
    d = os.path.join(INST, 'f1'); os.makedirs(d, exist_ok=True)
    for n in [50, 75, 100, 125, 150, 175, 200, 225, 250]:
        m = int(4.26 * n + 0.5)   # round half up
        for seed in range(20):
            F = RandomKCNF(3, n, m, seed=seed)
            p = os.path.join(d, 'rand426_n%d_s%d.cnf' % (n, seed))
            write_cnfgen(p, F, ['F1 random 3-CNF cnfgen RandomKCNF(3,%d,%d,seed=%d) m/n=4.26' % (n, m, seed)])
            record('F1', os.path.basename(p), p, 'cadical', dict(n=n, m=m, seed=seed, source='cnfgen'), n)
        # SATLIB: first 10 uf and first 10 uuf by numeric index
        for pref in ['uf', 'uuf']:
            files = glob.glob(os.path.join(INST, 'satlib', '%s%d-%d' % (pref, n, SATLIB_M[n]), '**', '*.cnf'), recursive=True)

            def idx(f):
                mm = re.search(r'-0*(\d+)\.cnf$', os.path.basename(f))
                return int(mm.group(1))
            files = sorted(files, key=idx)
            chosen = [f for f in files if 1 <= idx(f) <= 10]
            assert len(chosen) == 10, (pref, n, len(chosen))
            for f in chosen:
                p = os.path.join(d, '%s%d-%02d.cnf' % (pref, n, idx(f)))
                shutil.copyfile(f, p)
                record('F1', os.path.basename(p), p, 'cadical', dict(n=n, source='satlib', orig=os.path.basename(f)), n)


# ---------------- F2: random 3-SAT at m/n = 5.0 (seeds 0-9) ----------------
def f2():
    d = os.path.join(INST, 'f2'); os.makedirs(d, exist_ok=True)
    for n in [100, 150, 200, 250, 300, 350, 400]:
        m = 5 * n
        for seed in range(10):
            F = RandomKCNF(3, n, m, seed=seed)
            p = os.path.join(d, 'rand500_n%d_s%d.cnf' % (n, seed))
            write_cnfgen(p, F, ['F2 random 3-CNF cnfgen RandomKCNF(3,%d,%d,seed=%d) m/n=5.0' % (n, m, seed)])
            record('F2', os.path.basename(p), p, 'cadical', dict(n=n, m=m, seed=seed), n)


# ---------------- F3: PHP_{n+1}^n ----------------
def f3():
    d = os.path.join(INST, 'f3'); os.makedirs(d, exist_ok=True)
    for n in [8, 10, 12, 14, 16, 20, 25, 30, 40]:
        F = PigeonholePrinciple(n + 1, n)
        p = os.path.join(d, 'php_%d_%d.cnf' % (n + 1, n))
        write_cnfgen(p, F, ['F3 PHP %d pigeons %d holes, cnfgen PigeonholePrinciple(%d,%d)' % (n + 1, n, n + 1, n)])
        record('F3', os.path.basename(p), p, 'UNSAT', dict(n=n, pigeons=n + 1, holes=n), n)


# ---------------- F4: Tseitin on random 3-regular graphs, odd total charge ----------------
def f4():
    d = os.path.join(INST, 'f4'); os.makedirs(d, exist_ok=True)
    for n in [20, 40, 60, 80, 100, 150, 200, 300]:
        for seed in range(10):
            G = nx.random_regular_graph(3, n, seed=seed)
            conn = nx.is_connected(G)
            F = TseitinFormula(G)   # default: odd charge on first vertex only -> total charge odd
            p = os.path.join(d, 'tseitin_n%d_s%d.cnf' % (n, seed))
            write_cnfgen(p, F, ['F4 Tseitin on networkx random_regular_graph(3,%d,seed=%d), connected=%s, odd charge on vertex 1' % (n, seed, conn)])
            record('F4', os.path.basename(p), p, 'UNSAT', dict(n=n, seed=seed, connected=conn), n)


# ---------------- F5: clique-colouring, k = ceil(sqrt n), c = k-1 ----------------
def f5():
    d = os.path.join(INST, 'f5'); os.makedirs(d, exist_ok=True)
    for n in [8, 10, 12, 16, 20, 25, 30]:
        k = math.ceil(math.sqrt(n)); c = k - 1
        F = CliqueColoring(n, k, c)
        p = os.path.join(d, 'cliquecol_n%d_k%d_c%d.cnf' % (n, k, c))
        write_cnfgen(p, F, ['F5 clique-colouring cnfgen CliqueColoring(%d,%d,%d)' % (n, k, c)])
        record('F5', os.path.basename(p), p, 'UNSAT', dict(n=n, k=k, c=c), n)


# ---------------- F6: factoring, array multiplier, Tseitin encoding ----------------
def factoring_cnf(b, N):
    nv = 0
    clauses = []

    def new():
        nonlocal nv
        nv += 1
        return nv

    def AND(a, c):
        z = new(); clauses.extend([[-z, a], [-z, c], [z, -a, -c]]); return z

    def XOR2(x, y):
        s = new(); clauses.extend([[-s, x, y], [-s, -x, -y], [s, -x, y], [s, x, -y]]); return s

    def full_adder(x, y, ci):
        s = new(); co = new()
        for sx in (1, -1):
            for sy in (1, -1):
                for sc in (1, -1):
                    val = ((sx > 0) + (sy > 0) + (sc > 0)) % 2   # value of s when x=(sx>0), y=(sy>0), ci=(sc>0)
                    clauses.append([-sx * x, -sy * y, -sc * ci, s if val else -s])
        clauses.extend([[-x, -y, co], [-x, -ci, co], [-y, -ci, co], [x, y, -co], [x, ci, -co], [y, ci, -co]])
        return s, co

    def half_adder(x, y):
        return XOR2(x, y), AND(x, y)

    p = [new() for _ in range(b)]
    q = [new() for _ in range(b)]
    clauses.append([p[b - 1]]); clauses.append([q[b - 1]])    # leading bits 1
    rows = [[AND(p[i], q[j]) for i in range(b)] for j in range(b)]
    acc = list(rows[0])                       # positions 0..b-1
    for j in range(1, b):
        carry = None
        for i in range(b):
            pos = j + i
            if pos < len(acc):
                if carry is None:
                    acc[pos], carry = half_adder(acc[pos], rows[j][i])
                else:
                    acc[pos], carry = full_adder(acc[pos], rows[j][i], carry)
            else:
                assert pos == len(acc)        # new top position: only this row's bit plus the carry
                if carry is None:
                    acc.append(rows[j][i])
                else:
                    s_, carry = half_adder(rows[j][i], carry)
                    acc.append(s_)
        if carry is not None:
            acc.append(carry)                 # position b + j
    assert len(acc) == 2 * b
    for i in range(2 * b):
        clauses.append([acc[i]] if (N >> i) & 1 else [-acc[i]])
    return nv, clauses, p, q


def f6():
    d = os.path.join(INST, 'f6'); os.makedirs(d, exist_ok=True)
    for b in [6, 8, 10, 12, 14, 16, 18, 20]:
        for s in range(5):
            rng = random.Random(1000 * b + s)

            def rprime(lo, hi):
                while True:
                    x = rng.randrange(lo, hi)
                    if sympy.isprime(x):
                        return x
            # SAT: N = p*q, p,q distinct b-bit primes
            pp = rprime(1 << (b - 1), 1 << b)
            while True:
                qq = rprime(1 << (b - 1), 1 << b)
                if qq != pp:
                    break
            N = pp * qq
            nv, cls, _, _ = factoring_cnf(b, N)
            p = os.path.join(d, 'fact_b%d_sat_s%d.cnf' % (b, s))
            write_clauses(p, nv, cls, ['F6 factoring b=%d N=%d = %d * %d (SAT by construction)' % (b, N, pp, qq)])
            record('F6', os.path.basename(p), p, 'SAT', dict(b=b, seed=s, N=N, p=pp, q=qq), b)
            # UNSAT: N a 2b-bit prime
            Np = rprime(1 << (2 * b - 1), 1 << (2 * b))
            nv, cls, _, _ = factoring_cnf(b, Np)
            p = os.path.join(d, 'fact_b%d_unsat_s%d.cnf' % (b, s))
            write_clauses(p, nv, cls, ['F6 factoring b=%d N=%d prime (UNSAT by construction)' % (b, Np)])
            record('F6', os.path.basename(p), p, 'UNSAT', dict(b=b, seed=s, N=Np), b)


# ---------------- F8: mutilated chessboard ----------------
def mutilated_chessboard(s):
    removed = {(0, 0), (s - 1, s - 1)}
    cells = [(r, c) for r in range(s) for c in range(s) if (r, c) not in removed]
    cellset = set(cells)
    doms = []
    for (r, c) in cells:
        for (dr, dc) in ((0, 1), (1, 0)):
            if (r + dr, c + dc) in cellset:
                doms.append(((r, c), (r + dr, c + dc)))
    cover = {cell: [] for cell in cells}
    for i, (a, bb) in enumerate(doms):
        cover[a].append(i + 1); cover[bb].append(i + 1)
    clauses = []
    for cell in cells:
        vs = cover[cell]
        clauses.append(list(vs))
        for i in range(len(vs)):
            for j in range(i + 1, len(vs)):
                clauses.append([-vs[i], -vs[j]])
    return len(doms), clauses


def f8():
    d = os.path.join(INST, 'f8'); os.makedirs(d, exist_ok=True)
    for s in [6, 8, 10, 12, 14, 16]:
        nv, cls = mutilated_chessboard(s)
        C = MutilatedChessboard(s, s)
        chk = (C.number_of_variables(), C.number_of_clauses())
        p = os.path.join(d, 'mchess_%d.cnf' % s)
        write_clauses(p, nv, cls, ['F8 mutilated chessboard %dx%d, own encoding (one var per domino, exactly-one per cell, pairwise AMO); cnfgen MutilatedChessboard(%d,%d) has %d vars %d clauses' % (s, s, s, s, chk[0], chk[1])])
        record('F8', os.path.basename(p), p, 'UNSAT', dict(s=s, cnfgen_vars=chk[0], cnfgen_clauses=chk[1]), s)


if __name__ == '__main__':
    fams = sys.argv[1:] or ['f1', 'f2', 'f3', 'f4', 'f5', 'f6', 'f8']
    for fam in fams:
        globals()[fam]()
        print(fam, 'done', len(manifest), flush=True)
    with open(os.path.join(INST, 'MANIFEST.jsonl'), 'w') as f:
        for r in manifest:
            f.write(json.dumps(r) + '\n')
    from collections import Counter
    print(Counter(r['family'] for r in manifest))
