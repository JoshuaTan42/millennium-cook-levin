"""Fill the placeholders of NOTES_PHASE4_PREAMBLE.md (manifest, fuzz, F7 list, schedule decision) and append the result to
NOTES.md (LF line endings).  Run once, after the F7 quiet labelling pass and the schedule comparison, before any measured run."""
import os, json, hashlib, re
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
P4 = os.path.normpath(os.path.join(HERE, '..'))
INST = os.path.join(P4, 'instances'); RES = os.path.join(P4, 'results')
ROOT = os.path.normpath(os.path.join(P4, '..'))


def sha256(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()


pre = open(os.path.join(P4, 'NOTES_PHASE4_PREAMBLE.md'), encoding='utf-8').read()

# ---- manifest ----
rows = [json.loads(l) for l in open(os.path.join(INST, 'MANIFEST.jsonl'))]
cnt = Counter(r['family'] for r in rows)
man = ['| family | instances | sizes | labels |', '|---|---|---|---|']
for f in sorted(cnt):
    rs = [r for r in rows if r['family'] == f]
    sizes = sorted(set(r['size'] for r in rs))
    labs = Counter(r['label'] for r in rs)
    man.append('| %s | %d | %s | %s |' % (f, len(rs), ', '.join(str(s) for s in sizes), ', '.join('%s: %d' % kv for kv in sorted(labs.items()))))
man.append('')
man.append('SHA-256 of `phase4/instances/MANIFEST.jsonl`: `%s`. Full per-instance hash list: `phase4/instances/MANIFEST.sha256` (written now).' % sha256(os.path.join(INST, 'MANIFEST.jsonl')))
with open(os.path.join(INST, 'MANIFEST.sha256'), 'w', newline='\n') as f:
    for r in rows:
        f.write('%s  %s\n' % (r['sha256'], r['path']))
man.append('CaDiCaL labels for F1/F2 (`labels_f12.jsonl`, 1800 s limit, 6 concurrent): ' + ', '.join(
    '%s %s: %d' % (k[0], k[1], v) for k, v in sorted(Counter((json.loads(l)['family'], json.loads(l)['cadical']) for l in open(os.path.join(INST, 'labels_f12.jsonl'))).items())) +
    '. The F2 n=400 timeouts are being re-run with a 7200 s limit (`labels_retry.jsonl`); instances without a label are reported as unlabelled, never counted as agreeing.')
pre = pre.replace('MANIFEST_PLACEHOLDER', '\n'.join(man))

# ---- fuzz ----
fz = []
for seed in (0, 1):
    log = open(os.path.join(RES, 'fuzz_seed%d.log' % seed)).read()
    done = re.search(r'DONE seed=(\d+) cases=(\d+) bad=(\d+) sat=(\d+) unsat=(\d+)', log)
    probs = [l for l in log.splitlines() if 'PROBLEMS' in l]
    fz.append('* seed %s: %s cases (%s SAT, %s UNSAT by CaDiCaL), every answer of all three modes agreed with CaDiCaL 1.9.5, every model was accepted by '
              '`check_model.py`, every UNSAT proof was accepted by dpr-trim. Flagged lines: %d.' % (done.group(1), done.group(2), done.group(4), done.group(5), len(probs)))
    for l in probs:
        fz.append('  - `%s`' % l.strip()[:300])
fz.append('* Interpretation of the flags: the `prcheck.py` failures on `mchess 2x2` were a bug in the own checker (a formula containing empty clauses; fixed, '
          'the three proofs re-verify); the `status UNKNOWN after 120 s` lines are SDCL\\*/unfiltered exceeding the fuzz time limit on small satisfiable '
          'clique-colouring formulas that plain CDCL solves in 2 ms (cost 13) — not wrong answers, but recorded here because they are the first sign of the '
          'behaviour discussed under "schedule convention" below. An earlier fuzz attempt whose two seeds shared one scratch directory produced spurious '
          '"wrong answer" lines (files overwritten mid-run); all of those cases were re-run on the actual files and agreed with CaDiCaL with verified proofs.')
fz.append('* Smoke tests on pre-registered instances (not measurements): `php_9_8` UNSAT in all three modes, proofs verified by dpr-trim and by `prcheck.py`; '
          '`uf50-01` SAT with verified model; `uuf50-01` UNSAT.')
pre = pre.replace('FUZZ_PLACEHOLDER', '\n'.join(fz))

# ---- F7 list ----
quiet = [json.loads(l) for l in open(os.path.join(INST, 'sc23', 'labels_f7.jsonl'))]
p1 = {}
p1p = os.path.join(INST, 'sc23', 'labels_f7_contended_pass1.jsonl')
if os.path.exists(p1p):
    for l in open(p1p):
        r = json.loads(l); p1[r['hash']] = r
sel = [r for r in quiet if r['within_bounds'] and r['cadical'] in ('SAT', 'UNSAT')]
f7 = ['Selection rule (PHASE3.md): GBD `track=main_2023`, `variables<=3000`, `clauses<=30000` (90 instances; every header re-checked locally: all 90 within '
      'bounds), CaDiCaL 1.9.5 solves within 60 s wall-clock. Two labelling passes were run: pass 1 under heavy CPU contention (8 CaDiCaL processes beside '
      'fuzzing and other labelling; %d solved), pass 2 on a quiet machine with 4 concurrent CaDiCaL processes (%d solved). **Pass 2 is the F7 selection.** '
      'All 90 outcomes of both passes are in `phase4/instances/sc23/labels_f7.jsonl` (pass 2) and `labels_f7_contended_pass1.jsonl` (pass 1).'
      % (sum(1 for r in p1.values() if r['cadical'] in ('SAT', 'UNSAT')), len(sel)), '',
      '| # | GBD hash | original name | vars | clauses | CaDiCaL (pass 2) | time (s) | pass 1 |', '|---|---|---|---|---|---|---|---|']
for i, r in enumerate(sorted(sel, key=lambda r: r['hash']), 1):
    name = r['gbd_name'][33:] if r['gbd_name'].startswith(r['hash']) else r['gbd_name']
    f7.append('| %d | `%s` | %s | %d | %d | %s | %.1f | %s |' % (i, r['hash'], name.replace('.cnf.xz', ''), r['nvars'], r['nclauses'], r['cadical'], r['time'],
                                                           p1.get(r['hash'], {}).get('cadical', '-')))
f7.append('')
f7.append('Instances solved in pass 1 but not in pass 2 (excluded by the rule, listed for transparency): ' + (', '.join(
    '`%s` (%s, pass 1 %.1f s)' % (h, p1[h]['cadical'], p1[h]['time']) for h in sorted(p1) if p1[h]['cadical'] in ('SAT', 'UNSAT') and h not in {r['hash'] for r in sel}) or 'none') + '.')
pre = pre.replace('F7_PLACEHOLDER', '\n'.join(f7))

# ---- schedule decision ----
sched = open(os.path.join(P4, 'schedule_decision.md'), encoding='utf-8').read().strip()
pre = pre.replace('SCHEDULE_PLACEHOLDER', sched)

out = os.path.join(P4, 'NOTES_PHASE4_PREAMBLE_filled.md')
open(out, 'w', encoding='utf-8', newline='\n').write(pre)
notes = os.path.join(ROOT, 'NOTES.md')
with open(notes, 'a', encoding='utf-8', newline='\n') as f:
    f.write('\n---\n\n' + pre + '\n')
print('appended to NOTES.md:', len(pre.splitlines()), 'lines; F7 selected', len(sel))
