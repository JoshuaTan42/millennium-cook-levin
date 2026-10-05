"""F7 labelling: decompress the 90 GBD-listed SC2023 main-track instances (variables<=3000, clauses<=30000 per GBD),
verify the size bounds from the DIMACS header, run CaDiCaL 1.9.5 (PySAT) with a 60 s wall-clock limit, record everything."""
import os, sys, json, lzma, time, threading, hashlib, glob
from multiprocessing import Pool
from pysat.formula import CNF
from pysat.solvers import Cadical195

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.normpath(os.path.join(HERE, '..', 'instances', 'sc23'))
LIMIT = 60.0

def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()

def work(xz):
    cnfp = xz[:-3]
    if not os.path.exists(cnfp):
        with lzma.open(xz, 'rb') as fi, open(cnfp, 'wb') as fo:
            fo.write(fi.read())
    nv = nc = None
    with open(cnfp) as f:
        for line in f:
            if line.startswith('p cnf'):
                _, _, nv, nc = line.split(); nv, nc = int(nv), int(nc); break
    cnf = CNF(from_file=cnfp)
    s = Cadical195(bootstrap_with=cnf.clauses)
    t = threading.Timer(LIMIT, lambda: s.interrupt())
    t0 = time.time(); t.start()
    try:
        res = s.solve_limited(expect_interrupt=True)
    finally:
        t.cancel()
    dt = time.time() - t0
    model_ok = None
    if res is True:
        m = set(s.get_model())
        model_ok = all(any(l in m for l in cl) for cl in cnf.clauses)
    s.delete()
    return dict(hash=os.path.basename(xz)[:-7], cnf=os.path.basename(cnfp), nvars=nv, nclauses=nc, header_within_bounds=(nv <= 3000 and nc <= 30000),
                cadical=('SAT' if res is True else 'UNSAT' if res is False else 'TIMEOUT'), time=round(dt, 3), model_ok=model_ok, sha256=sha256(cnfp))

if __name__ == '__main__':
    xzs = sorted(glob.glob(os.path.join(D, '*.cnf.xz')))
    with Pool(8) as pool:
        rows = pool.map(work, xzs, chunksize=1)
    with open(os.path.join(D, 'f7_labels.jsonl'), 'w') as f:
        for r in rows:
            f.write(json.dumps(r) + '\n')
    from collections import Counter
    print(Counter(r['cadical'] for r in rows), 'within_bounds:', sum(r['header_within_bounds'] for r in rows), 'of', len(rows))
