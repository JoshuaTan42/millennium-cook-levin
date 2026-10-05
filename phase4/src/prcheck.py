"""Independent DPR proof checker in pure Python (unit propagation only; shares no code with the solver or with dpr-trim).

Proof format (text DPR as written by sdcl.cpp):
  RUP line:   l1 l2 ... lk 0
  PR line:    l1 l2 ... lk l1 w1 w2 ... 0     (first literal repeated marks the start of the witness, which begins with l1)
  deletion:   d l1 ... lk 0
  empty:      0
Checks every RUP clause by unit propagation, every PR clause by the PR condition
   omega satisfies C  and  for every D in F touched but not satisfied by omega:  F|alpha  /\  not(D|omega)  |-1  conflict,
where alpha = not C, and finally that the empty clause is RUP.  Prints VERIFIED or FAIL with the offending line.
Usage: python prcheck.py formula.cnf proof.dpr
"""
import sys
from collections import defaultdict


def read_cnf(path):
    nv = None
    clauses = []
    cur = []
    with open(path) as f:
        for line in f:
            if line.startswith('%'):
                break                      # SATLIB end-of-file marker
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


class Formula:
    def __init__(self, clauses):
        self.clauses = {}             # id -> tuple of lits
        self.occ = defaultdict(set)   # literal -> set of clause ids containing it
        self.key = defaultdict(list)  # sorted tuple -> list of ids (multiset for deletion)
        self.next_id = 0
        self.asg = {}                 # current assignment: var -> bool
        self.trail = []
        self.units = set()            # ids of unit clauses (they must seed every propagation)
        self.empties = 0              # number of empty clauses in F (everything is implied while > 0)
        for c in clauses:
            self.add(c)

    def add(self, lits):
        t = tuple(lits)
        i = self.next_id; self.next_id += 1
        self.clauses[i] = t
        for l in t:
            self.occ[l].add(i)
        self.key[tuple(sorted(set(t)))].append(i)
        if len(t) == 1:
            self.units.add(i)
        if len(t) == 0:
            self.empties += 1
        return i

    def delete(self, lits):
        k = tuple(sorted(set(lits)))
        ids = self.key.get(k)
        if not ids:
            return False
        i = ids.pop()
        t = self.clauses.pop(i)
        for l in t:
            self.occ[l].discard(i)
        self.units.discard(i)
        if len(t) == 0:
            self.empties -= 1
        return True

    def seed_units(self):
        """Assign every unit clause of F; returns False on conflict."""
        for i in self.units:
            if not self.assign(self.clauses[i][0]):
                return False
        return True

    # ---- trail-based assignment with undo ----
    def assign(self, l):
        """Returns False on immediate inconsistency."""
        v = abs(l)
        a = self.asg.get(v)
        if a is not None:
            return a == (l > 0)
        self.asg[v] = (l > 0); self.trail.append(v)
        return True

    def undo_to(self, mark):
        while len(self.trail) > mark:
            v = self.trail.pop(); del self.asg[v]

    def propagate(self, start):
        """Unit propagation from trail position `start`; returns True on conflict."""
        qi = start
        asg = self.asg
        while qi < len(self.trail):
            v = self.trail[qi]; qi += 1
            fl = -v if asg[v] else v          # the literal that became false
            for cid in list(self.occ.get(fl, ())):
                cl = self.clauses.get(cid)
                if cl is None:
                    continue
                unassigned = None; nun = 0; sat = False
                for x in cl:
                    a = asg.get(abs(x))
                    if a is None:
                        nun += 1; unassigned = x
                        if nun > 1:
                            break
                    elif a == (x > 0):
                        sat = True; break
                if sat or nun > 1:
                    continue
                if nun == 0:
                    return True
                asg[abs(unassigned)] = (unassigned > 0); self.trail.append(abs(unassigned))
        return False

    def implied(self, assumptions):
        """F /\\ assumptions |-1 conflict ?  (assignment is restored afterwards)"""
        if self.empties > 0:
            return True
        mark = len(self.trail)
        if not self.seed_units():
            self.undo_to(mark); return True
        for l in assumptions:
            if not self.assign(l):
                self.undo_to(mark); return True
        res = self.propagate(mark)
        self.undo_to(mark)
        return res

    def rup(self, lits):
        return self.implied([-l for l in lits])

    def pr(self, lits, witness):
        wmap = {}
        for w in witness:
            if abs(w) in wmap and wmap[abs(w)] != (w > 0):
                return False, 'inconsistent witness'
            wmap[abs(w)] = (w > 0)
        if not any(wmap.get(abs(l)) == (l > 0) for l in lits):
            return False, 'witness does not satisfy the clause'
        if self.empties > 0:
            return True, 'F contains the empty clause'
        mark = len(self.trail)
        if not self.seed_units():
            self.undo_to(mark); return True, 'F has conflicting units (RUP)'
        # tau = unit propagation of F /\ alpha, alpha = not C
        for l in lits:
            if not self.assign(-l):
                self.undo_to(mark); return True, 'alpha inconsistent (RUP)'
        if self.propagate(mark):
            self.undo_to(mark); return True, 'RUP'
        tau_mark = len(self.trail)
        touched_ids = set()
        for w in witness:
            touched_ids |= self.occ.get(w, set()); touched_ids |= self.occ.get(-w, set())
        for cid in touched_ids:
            cl = self.clauses.get(cid)
            if cl is None:
                continue
            if any(wmap.get(abs(x)) == (x > 0) for x in cl):
                continue                         # satisfied by omega
            reduced = [x for x in cl if abs(x) not in wmap]   # D|omega (falsified literals removed)
            # need: F /\ tau /\ not(D|omega) |-1 conflict
            ok = False
            for x in reduced:
                if not self.assign(-x):           # x already true under tau -> D|omega satisfied under tau -> implied
                    ok = True; break
            if not ok:
                ok = self.propagate(tau_mark)
            self.undo_to(tau_mark)
            if not ok:
                self.undo_to(mark)
                return False, 'clause %s not implied under witness' % (cl,)
        self.undo_to(mark)
        return True, ''


def parse_line(line):
    toks = [int(t) for t in line.split()]
    assert toks and toks[-1] == 0
    toks = toks[:-1]
    if not toks:
        return [], None
    first = toks[0]
    for i in range(1, len(toks)):
        if toks[i] == first:
            return toks[:i], toks[i:]
    return toks, None


def main():
    nv, clauses = read_cnf(sys.argv[1])
    F = Formula(clauses)
    n_rup = n_pr = n_del = 0
    with open(sys.argv[2]) as f:
        for ln, line in enumerate(f, 1):
            line = line.strip()
            if not line or line.startswith('c'):
                continue
            if line.startswith('d '):
                lits, _ = parse_line(line[2:])
                if not F.delete(lits):
                    print('WARNING line %d: deleting a clause not in the formula %s' % (ln, lits))
                n_del += 1
                continue
            lits, witness = parse_line(line)
            if not lits:
                if F.rup([]):
                    print('VERIFIED empty clause at line %d after %d RUP, %d PR, %d deletions' % (ln, n_rup, n_pr, n_del))
                    return 0
                print('FAIL line %d: empty clause not RUP' % ln); return 1
            if witness is None:
                if not F.rup(lits):
                    print('FAIL line %d: clause %s is not RUP' % (ln, lits)); return 1
                n_rup += 1
            else:
                ok, why = F.pr(lits, witness)
                if not ok:
                    print('FAIL line %d: clause %s with witness is not PR (%s)' % (ln, lits, why)); return 1
                n_pr += 1
            F.add(lits)
    print('INCOMPLETE: no empty clause (%d RUP, %d PR, %d deletions)' % (n_rup, n_pr, n_del))
    return 2


if __name__ == '__main__':
    sys.exit(main())
