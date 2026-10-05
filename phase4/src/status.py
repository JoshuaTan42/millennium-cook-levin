"""Quick progress summary of results/runs.jsonl: counts by family x mode x status, plus the last few records."""
import os, sys, json
from collections import Counter, defaultdict
HERE = os.path.dirname(os.path.abspath(__file__))
args = [a for a in sys.argv[1:] if not a.startswith('-')]
p = os.path.join(HERE, '..', 'results', args[0] if args else 'runs.jsonl')
rows = []
for l in open(p):
    try:
        rows.append(json.loads(l))
    except Exception:
        pass
c = Counter((r['family'], r['mode'], r.get('status')) for r in rows)
fams = sorted(set(r['family'] for r in rows))
for f in fams:
    for m in ('sdcl', 'plain', 'unfiltered'):
        parts = ['%s=%d' % (st, n) for (ff, mm, st), n in sorted(c.items(), key=lambda x: str(x)) if ff == f and mm == m]
        if parts:
            print('%-3s %-10s %s' % (f, m, '  '.join(parts)))
bad = [r for r in rows if (r.get('status') == 'SATISFIABLE' and not r.get('model_ok')) or (r.get('status') == 'UNSATISFIABLE' and r.get('dprtrim') != 'VERIFIED') or r.get('status') == 'CRASH']
print('records', len(rows), '| unverified/crash', len(bad))
for r in bad[:10]:
    print('  !!', r['family'], r['name'], r['mode'], r.get('status'), r.get('dprtrim'), r.get('model_check'), r.get('stderr', '')[:80])
if '-v' in sys.argv:
    for r in rows[-8:]:
        print(r['family'], r['name'], r['mode'], r.get('status'), 'cost', r.get('cost'), 'wall', r.get('wall'), 'pr', r.get('pr_learnt'))
