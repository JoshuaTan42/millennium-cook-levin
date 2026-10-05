"""CaDiCaL labelling with HARD subprocess timeouts (PySAT's interrupt() does not stop CaDiCaL 1.9.5 on this machine).
  python label_all.py f7      -> decompress the 90 GBD-listed SC2023 instances, CaDiCaL with 60 s limit (pre-registered F7 selection)
  python label_all.py f12     -> CaDiCaL labels for F1 and F2 with a 1800 s limit
Writes <instances>/labels_<set>.jsonl (one JSON object per instance, every run recorded incl. timeouts)."""
import os, sys, json, lzma, time, glob, hashlib, subprocess
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
INST = os.path.normpath(os.path.join(HERE, '..', 'instances'))
ONE = os.path.join(HERE, 'cadical_one.py')


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


def header(path):
    with open(path) as f:
        for line in f:
            if line.startswith('p cnf'):
                _, _, nv, nc = line.split(); return int(nv), int(nc)
    return None, None


def run_one(path, limit):
    t0 = time.time()
    try:
        p = subprocess.run([sys.executable, ONE, path], capture_output=True, text=True, timeout=limit)
        dt = time.time() - t0
        if p.returncode != 0:
            return dict(cadical='ERROR', time=round(dt, 3), err=p.stderr[-300:])
        d = json.loads(p.stdout.strip().splitlines()[-1])
        return dict(cadical=d['result'], time=d['time'], model_ok=d['model_ok'], wall=round(dt, 3))
    except subprocess.TimeoutExpired:
        return dict(cadical='TIMEOUT', time=round(time.time() - t0, 3), limit=limit)


def f7():
    D = os.path.join(INST, 'sc23')
    names = {}
    for line in open(os.path.join(D, 'gbd_filenames.txt')):
        h, fn = line.split()
        names[h] = fn
    xzs = sorted(glob.glob(os.path.join(D, '*.cnf.xz')))
    jobs = []
    for xz in xzs:
        cnfp = xz[:-3]
        if not os.path.exists(cnfp):
            with lzma.open(xz, 'rb') as fi, open(cnfp, 'wb') as fo:
                fo.write(fi.read())
        jobs.append(cnfp)

    def work(cnfp):
        h = os.path.basename(cnfp)[:-4]
        nv, nc = header(cnfp)
        r = run_one(cnfp, 60)
        r.update(workers=workers, hash=h, gbd_name=names.get(h, '?'), path=os.path.relpath(cnfp, INST).replace('\\', '/'), nvars=nv, nclauses=nc,
                 within_bounds=(nv <= 3000 and nc <= 30000), sha256=sha256(cnfp))
        print(json.dumps(r), flush=True)
        return r
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    with ThreadPoolExecutor(workers) as ex:
        rows = list(ex.map(work, jobs))
    with open(os.path.join(D, 'labels_f7.jsonl'), 'w') as f:
        for r in rows:
            f.write(json.dumps(r) + '\n')
    from collections import Counter
    print('SUMMARY', Counter(r['cadical'] for r in rows), 'within_bounds', sum(r['within_bounds'] for r in rows), 'of', len(rows))


def f12():
    rows_in = [json.loads(l) for l in open(os.path.join(INST, 'MANIFEST.jsonl'))]
    jobs = [r for r in rows_in if r['family'] in ('F1', 'F2')]
    jobs.sort(key=lambda r: (r['nvars'], r['name']))

    def work(r):
        res = run_one(os.path.join(INST, r['path']), 1800)
        res.update(family=r['family'], name=r['name'], path=r['path'], size=r['size'])
        print(json.dumps(res), flush=True)
        return res
    with ThreadPoolExecutor(6) as ex:
        rows = list(ex.map(work, jobs))
    with open(os.path.join(INST, 'labels_f12.jsonl'), 'w') as f:
        for r in rows:
            f.write(json.dumps(r) + '\n')
    from collections import Counter
    print('SUMMARY', Counter((r['family'], r['cadical']) for r in rows))


if __name__ == '__main__':
    globals()[sys.argv[1]]()
