"""Re-run CaDiCaL with a longer hard timeout on instances whose first labelling pass timed out.
  python label_retry.py labels_f12.jsonl 7200   -> writes labels_retry.jsonl (F1/F2 names), 4 parallel"""
import os, sys, json, time, subprocess
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
INST = os.path.normpath(os.path.join(HERE, '..', 'instances'))
ONE = os.path.join(HERE, 'cadical_one.py')
src = os.path.join(INST, sys.argv[1]); limit = int(sys.argv[2])
rows = [json.loads(l) for l in open(src)]
todo = [r for r in rows if r['cadical'] == 'TIMEOUT']


def work(r):
    t0 = time.time()
    try:
        p = subprocess.run([sys.executable, ONE, os.path.join(INST, r['path'])], capture_output=True, text=True, timeout=limit)
        d = json.loads(p.stdout.strip().splitlines()[-1])
        res = dict(cadical=d['result'], time=d['time'], model_ok=d['model_ok'])
    except subprocess.TimeoutExpired:
        res = dict(cadical='TIMEOUT', time=round(time.time() - t0, 3))
    res.update(family=r['family'], name=r['name'], path=r['path'], size=r['size'], limit=limit)
    print(json.dumps(res), flush=True)
    return res


with ThreadPoolExecutor(4) as ex:
    out = list(ex.map(work, todo))
with open(os.path.join(INST, 'labels_retry.jsonl'), 'a') as f:
    for r in out:
        f.write(json.dumps(r) + '\n')
print('RETRY DONE', len(out))
