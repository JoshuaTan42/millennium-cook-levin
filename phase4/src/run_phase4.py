"""Phase 4 driver: runs every (instance, mode) job of the pre-registered plan, records every run (including timeouts
and crashes), verifies every answer (SAT: independent evaluator; UNSAT: dpr-trim, plus prcheck.py on small proofs),
and appends one JSON line per run to results/runs.jsonl.  Resumable: finished jobs are skipped.

  python run_phase4.py [--workers N] [--modes sdcl,plain,unfiltered] [--families F1,F2,...] [--max-size-index K]

Modes: sdcl = SDCL* (filtered positive reduct, primary); plain = ablation (i); unfiltered = ablation (ii).
Cap: 3600 s per run (solver's own --time-limit), hard kill at 3700 s.  Python output is evidence, never proof.
"""
import os, sys, json, time, subprocess, argparse, threading
from concurrent.futures import ThreadPoolExecutor, as_completed

HERE = os.path.dirname(os.path.abspath(__file__))
INST = os.path.normpath(os.path.join(HERE, '..', 'instances'))
RES = os.path.normpath(os.path.join(HERE, '..', 'results'))
SDCL = os.path.join(HERE, 'sdcl.exe')
DPRTRIM = os.path.normpath(os.path.join(HERE, '..', 'tools', 'dpr-trim', 'dpr-trim.exe'))
CAP = 3600.0
HARD = 3700.0
KEEP_PROOF_BYTES = 20 * 1024 * 1024
PRCHECK_MAX_BYTES = 3 * 1024 * 1024
PRCHECK_TIMEOUT = 900
DPRTRIM_TIMEOUT = 3600

lock = threading.Lock()


def load_jobs(families, modes, max_size_index):
    rows = [json.loads(l) for l in open(os.path.join(INST, 'MANIFEST.jsonl'))]
    f7p = os.path.join(INST, 'sc23', 'labels_f7.jsonl')
    if os.path.exists(f7p):
        for l in open(f7p):
            r = json.loads(l)
            if r['within_bounds'] and r['cadical'] in ('SAT', 'UNSAT'):
                rows.append(dict(family='F7', name=r['hash'] + '.cnf', path=r['path'], nvars=r['nvars'], nclauses=r['nclauses'],
                                 sha256=r['sha256'], label=r['cadical'], params=dict(gbd_name=r['gbd_name'], cadical_time=r['time']), size=0))
    # size index within family (0 = smallest listed size)
    sizes = {}
    for r in rows:
        sizes.setdefault(r['family'], set()).add(r['size'])
    sidx = {f: {s: i for i, s in enumerate(sorted(ss))} for f, ss in sizes.items()}
    jobs = []
    mode_prio = {'sdcl': 0, 'plain': 1, 'unfiltered': 2}
    for r in rows:
        if r['family'] not in families:
            continue
        si = sidx[r['family']][r['size']]
        if max_size_index is not None and si > max_size_index:
            continue
        for m in modes:
            jobs.append((si, mode_prio[m], r['family'], r['name'], m, r))
    # all SDCL* and plain-CDCL jobs first (by size index), then the unfiltered ablation (the most expensive variant)
    # F7 (no size series; feeds only K1/K5) runs after the sized families within each mode group
    # Staged priority order (set 2026-10-06 01:30 after two checkpoints showed one 13-job batch per hour at the cap, i.e. ~85 h for
    # the full plan).  Nothing about the configuration or the instances changes; only the execution order:
    #   stage 0: F3 F4 F5 F8 (home turf; K2/K5), SDCL* and plain
    #   stage 1: F1 instances labelled UNSAT at n in {200,225,250} (K4), SDCL* and plain
    #   stage 2: F6 F2 F7, SDCL* and plain
    #   stage 3: unfiltered ablation at the smallest listed size of every family
    #   stage 4: the rest of F1, SDCL* and plain
    #   stage 5: the rest of the unfiltered ablation
    labels = {}
    lp = os.path.join(INST, 'labels_f12.jsonl')
    if os.path.exists(lp):
        for l in open(lp):
            d = json.loads(l); labels[(d['family'], d['name'])] = d['cadical']
    def stage(j):
        si, mp, fam, name, m, r = j
        if m == 'unfiltered':
            return 3 if si == 0 else 5
        if fam in ('F3', 'F4', 'F5', 'F8'):
            return 0
        if fam == 'F1':
            return 1 if (r['size'] in (200, 225, 250) and labels.get((fam, name)) == 'UNSAT') else 4
        return 2
    # Breadth-first rounds (set 2026-10-06 02:45): within stage groups, the first instance of every (family, size, label, mode) group runs
    # before the second instance of any group, so every size has data at any stopping point.  Order only; nothing else changes.
    def lab(j):
        si, mp, fam, name, m, r = j
        return labels.get((fam, name), r['label']) if r['label'] == 'cadical' else r['label']
    groups = {}
    for j in jobs:
        groups.setdefault((j[2], j[5]['size'], lab(j), j[4]), []).append(j[3])
    rnd = {}
    for k, names in groups.items():
        for i, n in enumerate(sorted(names)):
            rnd[(k, n)] = i
    def key(j):
        st = stage(j)
        sg = 0 if st <= 2 else (1 if st == 3 else (2 if st == 4 else 3))
        return (sg, rnd[((j[2], j[5]['size'], lab(j), j[4]), j[3])], st, j[0], j[1], j[2], j[3])
    jobs.sort(key=key)
    return jobs


def parse_out(text):
    d = {'status': None}
    for line in text.splitlines():
        if line.startswith('s '):
            d['status'] = line.split()[1]
        elif line.startswith('c stat '):
            _, _, k, v = line.split()
            d[k] = float(v) if '.' in v else int(v)
    return d


def run_job(job):
    si, mp, fam, name, mode, r = job
    inst = os.path.join(INST, r['path'])
    outdir = os.path.join(RES, 'out', fam); os.makedirs(outdir, exist_ok=True)
    proofdir = os.path.join(RES, 'proofs', fam); os.makedirs(proofdir, exist_ok=True)
    base = name[:-4] if name.endswith('.cnf') else name
    outp = os.path.join(outdir, '%s.%s.out' % (base, mode))
    proofp = os.path.join(proofdir, '%s.%s.dpr' % (base, mode))
    rec = dict(family=fam, name=name, size=r['size'], size_index=si, mode=mode, nvars=r['nvars'], nclauses=r['nclauses'],
               label=r['label'], sha256=r['sha256'], started=time.strftime('%Y-%m-%d %H:%M:%S'))
    t0 = time.time()
    try:
        p = subprocess.run([SDCL, '--mode=' + mode, '--proof=' + proofp, '--time-limit=%d' % int(CAP), inst],
                           capture_output=True, text=True, timeout=HARD)
        wall = time.time() - t0
        open(outp, 'w').write(p.stdout + ('\n' + p.stderr if p.stderr else ''))
        d = parse_out(p.stdout)
        rec.update(d); rec['rc'] = p.returncode; rec['wall'] = round(wall, 3)
        if p.returncode not in (0, 10, 20) or d['status'] is None:
            rec['status'] = 'CRASH'; rec['stderr'] = p.stderr[-500:]
        elif d['status'] == 'UNKNOWN':
            rec['status'] = 'TIMEOUT'
    except subprocess.TimeoutExpired:
        rec['status'] = 'TIMEOUT-HARDKILL'; rec['wall'] = round(time.time() - t0, 3)
    # ---- verification ----
    try:
        if rec['status'] == 'SATISFIABLE':
            m = subprocess.run([sys.executable, os.path.join(HERE, 'check_model.py'), inst, outp], capture_output=True, text=True, timeout=600)
            rec['model_check'] = m.stdout.strip()[:200]; rec['model_ok'] = (m.returncode == 0)
        elif rec['status'] == 'UNSATISFIABLE':
            size = os.path.getsize(proofp) if os.path.exists(proofp) else -1
            rec['proof_bytes'] = size
            t1 = time.time()
            try:
                dd = subprocess.run([DPRTRIM, inst, proofp, '-t', str(DPRTRIM_TIMEOUT)], capture_output=True, text=True, timeout=DPRTRIM_TIMEOUT + 120)
                rec['dprtrim'] = 'VERIFIED' if 's VERIFIED' in dd.stdout else ('NOT-VERIFIED: ' + (dd.stdout.strip().splitlines() or [''])[-1][:150])
            except subprocess.TimeoutExpired:
                rec['dprtrim'] = 'TIMEOUT'
            rec['dprtrim_time'] = round(time.time() - t1, 2)
            if 0 <= size <= PRCHECK_MAX_BYTES:
                t1 = time.time()
                try:
                    c = subprocess.run([sys.executable, os.path.join(HERE, 'prcheck.py'), inst, proofp], capture_output=True, text=True, timeout=PRCHECK_TIMEOUT)
                    rec['prcheck'] = c.stdout.strip()[:150]
                except subprocess.TimeoutExpired:
                    rec['prcheck'] = 'TIMEOUT'
                rec['prcheck_time'] = round(time.time() - t1, 2)
    except Exception as e:  # noqa
        rec['verify_error'] = repr(e)[:300]
    if os.path.exists(proofp):
        if rec.get('status') != 'UNSATISFIABLE' or os.path.getsize(proofp) > KEEP_PROOF_BYTES:
            try:
                os.remove(proofp)
            except OSError:
                pass
    rec['finished'] = time.strftime('%Y-%m-%d %H:%M:%S')
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--workers', type=int, default=13)
    ap.add_argument('--modes', default='sdcl,plain,unfiltered')
    ap.add_argument('--families', default='F1,F2,F3,F4,F5,F6,F7,F8')
    ap.add_argument('--max-size-index', type=int, default=None)
    ap.add_argument('--results', default=os.path.join(RES, 'runs.jsonl'))
    a = ap.parse_args()
    modes = a.modes.split(','); fams = a.families.split(',')
    jobs = load_jobs(fams, modes, a.max_size_index)
    done = set()
    if os.path.exists(a.results):
        for l in open(a.results):
            try:
                d = json.loads(l); done.add((d['family'], d['name'], d['mode']))
            except Exception:
                pass
    todo = [j for j in jobs if (j[2], j[3], j[4]) not in done]
    print('jobs total %d, done %d, todo %d' % (len(jobs), len(done), len(todo)), flush=True)
    with open(a.results, 'a') as outf, ThreadPoolExecutor(a.workers) as ex:
        futs = {ex.submit(run_job, j): j for j in todo}
        n = 0
        for fut in as_completed(futs):
            rec = fut.result()
            with lock:
                outf.write(json.dumps(rec) + '\n'); outf.flush()
            n += 1
            print('[%d/%d] %s %s %s -> %s cost=%s wall=%s' % (n, len(todo), rec['family'], rec['name'], rec['mode'], rec.get('status'),
                                                              rec.get('cost'), rec.get('wall')), flush=True)
    print('ALL DONE', flush=True)


if __name__ == '__main__':
    main()
