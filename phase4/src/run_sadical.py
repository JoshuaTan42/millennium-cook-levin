"""Supplementary reference runs with the ORIGINAL SaDiCaL (Heule, Kiesl, Biere; fmv.jku.at/sadical, built under WSL Ubuntu 22.04).
Not part of the pre-registered kill criteria (SaDiCaL's configuration differs from SDCL*; see NOTES.md).  Records every run.
  python run_sadical.py F3,F4,F5,F8 [cap_seconds]
Proofs (text DPR, --no-binary) are checked with dpr-trim.  Python output is evidence, never proof."""
import os, sys, json, time, subprocess, re
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
INST = os.path.normpath(os.path.join(HERE, '..', 'instances'))
RES = os.path.normpath(os.path.join(HERE, '..', 'results'))
DPRTRIM = os.path.normpath(os.path.join(HERE, '..', 'tools', 'dpr-trim', 'dpr-trim.exe'))
WSL_SAD = '/mnt/d/PvsNP/phase4/tools/sadical/sadical/sadical'


def to_wsl(p):
    p = os.path.abspath(p).replace('\\', '/')
    return '/mnt/' + p[0].lower() + p[2:]


def run(r, cap):
    inst = os.path.join(INST, r['path'])
    pdir = os.path.join(RES, 'proofs_sadical', r['family']); os.makedirs(pdir, exist_ok=True)
    proof = os.path.join(pdir, r['name'][:-4] + '.sadical.dpr')
    if os.path.exists(proof):
        os.remove(proof)
    cmd = ['wsl', '-d', 'Ubuntu-22.04', '--', 'bash', '-lc',
           'timeout %d %s %s %s --no-binary -n -f; echo RC=$?' % (int(cap), WSL_SAD, to_wsl(inst), to_wsl(proof))]
    t0 = time.time()
    try:
        p = subprocess.run(cmd, capture_output=True, text=True, timeout=cap + 120)
        out = p.stdout.replace('\x00', '')
    except subprocess.TimeoutExpired:
        subprocess.run(['wsl', '-d', 'Ubuntu-22.04', '--', 'bash', '-lc', 'pkill -f "sadical %s"' % to_wsl(inst)], capture_output=True)
        out = 'RC=124\n'
    wall = time.time() - t0
    rec = dict(family=r['family'], name=r['name'], size=r['size'], solver='sadical', wall=round(wall, 3), label=r['label'])
    m = re.search(r'RC=(\d+)', out); rec['rc'] = int(m.group(1)) if m else None
    rec['status'] = 'SATISFIABLE' if 's SATISFIABLE' in out else 'UNSATISFIABLE' if 's UNSATISFIABLE' in out else ('TIMEOUT' if rec['rc'] == 124 else 'UNKNOWN')
    for key, pat in [('conflicts', r'c conflicts:\s+(\d+)'), ('decisions', r'c decisions:\s+(\d+)'), ('pruned', r'c pruned:\s+(\d+)'),
                     ('reducts', r'c generated reducts:\s+(\d+)'), ('lookahead', r'c look-ahead:\s+(\d+)'), ('time', r'c total process time:\s+([\d.]+)')]:
        m = re.search(pat, out); rec[key] = (float(m.group(1)) if key == 'time' else int(m.group(1))) if m else None
    if rec['status'] == 'UNSATISFIABLE' and os.path.exists(proof):
        d = subprocess.run([DPRTRIM, inst, proof], capture_output=True, text=True, timeout=3600)
        rec['dprtrim'] = 'VERIFIED' if 's VERIFIED' in d.stdout else 'NOT-VERIFIED: ' + (d.stdout.strip().splitlines() or [''])[-1][:100]
        rec['proof_bytes'] = os.path.getsize(proof)
    open(os.path.join(RES, 'out', 'sadical_%s_%s.out' % (r['family'], r['name'])), 'w').write(out)
    return rec


def main():
    fams = sys.argv[1].split(',')
    cap = float(sys.argv[2]) if len(sys.argv) > 2 else 3600
    rows = [json.loads(l) for l in open(os.path.join(INST, 'MANIFEST.jsonl')) if json.loads(l)['family'] in fams]
    rows.sort(key=lambda r: (r['size'], r['name']))
    os.makedirs(os.path.join(RES, 'out'), exist_ok=True)
    outp = os.path.join(RES, 'runs_sadical.jsonl')
    done = set()
    if os.path.exists(outp):
        for l in open(outp):
            d = json.loads(l); done.add((d['family'], d['name']))
    rows = [r for r in rows if (r['family'], r['name']) not in done]
    with open(outp, 'a') as f, ThreadPoolExecutor(2) as ex:
        for rec in ex.map(lambda r: run(r, cap), rows):
            f.write(json.dumps(rec) + '\n'); f.flush()
            print(rec['family'], rec['name'], rec['status'], 'conflicts', rec['conflicts'], 'pruned', rec['pruned'], 'wall', rec['wall'], rec.get('dprtrim'), flush=True)


if __name__ == '__main__':
    main()
