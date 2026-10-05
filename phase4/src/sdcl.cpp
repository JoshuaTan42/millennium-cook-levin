// sdcl.cpp -- SDCL* exactly as pre-registered in PHASE3.md section 2.3.2 (Phase 4, 2026-10-05).
//
// Modes:
//   --mode=sdcl        SDCL* primary: filtered positive reduct before every decision at level >= 1,
//                      inner plain-CDCL call limited to 100 conflicts, learn negation of decisions as PR clause.
//   --mode=plain       ablation (i): same code with the SDCL step disabled (plain CDCL).
//   --mode=unfiltered  ablation (ii): original positive reduct instead of the filtered one.
//
// Base CDCL (both outer and inner solver): two watched literals; VSIDS with decay 0.95 and phase saving;
// Luby restarts with unit 100 conflicts; 1-UIP learning with recursive clause minimisation; learned-clause
// database reduction every 2,000 conflicts keeping clauses of LBD <= 2 and the most active half of the rest;
// no preprocessing (parsing only removes duplicate literals and tautological clauses).
//
// Proof output (DPR text format, checkable with dpr-trim): every 1-UIP clause as a RUP line, every PR clause
// as "pivot rest... pivot witness... 0", deletions as "d ... 0", final empty clause "0".
//
// Python output is evidence, never proof; this program's output is evidence, never proof.

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cmath>
#include <cstdint>
#include <vector>
#include <string>
#include <algorithm>
#include <chrono>

using namespace std;

typedef int Lit;                                   // variable v (0-based) -> literal 2v (positive), 2v+1 (negative)
static inline int lvar(Lit l) { return l >> 1; }
static inline Lit lneg(Lit l) { return l ^ 1; }
static inline Lit fromDimacs(int d) { int v = (d > 0 ? d : -d) - 1; return d > 0 ? 2 * v : 2 * v + 1; }
static inline int toDimacs(Lit l) { return (l & 1) ? -(lvar(l) + 1) : (lvar(l) + 1); }

struct Clause {
    vector<Lit> lits;
    bool learnt = false, deleted = false, pr = false;
    int lbd = 0;
    double activity = 0.0;
};

struct Watch { Clause* c; Lit blocker; };

enum Result { R_UNKNOWN = 0, R_SAT = 10, R_UNSAT = 20 };

struct Stats {
    long long conflicts = 0, decisions = 0, propagations = 0, restarts = 0, reductions = 0;
    long long learnt_clauses = 0, removed_clauses = 0;
    long long reduct_checks = 0, reduct_sat = 0, reduct_unsat = 0, reduct_limit = 0;
    long long inner_conflicts = 0, inner_decisions = 0, inner_propagations = 0, pr_learnt = 0;
    long long filter_tests = 0, filtered_clauses = 0, reduct_clauses = 0, reduct_lits = 0, filter_propagations = 0;
    long long max_reduct_vars = 0, pr_lits = 0;
    double time_reduct_build = 0.0, time_inner = 0.0;
};

static double luby(double y, int x) {
    int size, seq;
    for (size = 1, seq = 0; size < x + 1; seq++, size = 2 * size + 1);
    while (size - 1 != x) { size = (size - 1) >> 1; seq--; x = x % size; }
    return pow(y, seq);
}

struct VarHeap {
    vector<int> heap, idx;
    const vector<double>* act = nullptr;
    void init(const vector<double>* a, int n) { act = a; idx.assign(n, -1); heap.clear(); }
    bool lt(int a, int b) const { return (*act)[a] > (*act)[b]; }
    bool empty() const { return heap.empty(); }
    void up(int i) {
        int x = heap[i];
        while (i > 0) { int p = (i - 1) >> 1; if (!lt(x, heap[p])) break; heap[i] = heap[p]; idx[heap[i]] = i; i = p; }
        heap[i] = x; idx[x] = i;
    }
    void down(int i) {
        int x = heap[i]; int n = (int)heap.size();
        while (true) {
            int l = 2 * i + 1, r = l + 1; if (l >= n) break;
            int c = (r < n && lt(heap[r], heap[l])) ? r : l;
            if (!lt(heap[c], x)) break;
            heap[i] = heap[c]; idx[heap[i]] = i; i = c;
        }
        heap[i] = x; idx[x] = i;
    }
    void insert(int v) { if (idx[v] >= 0) return; idx[v] = (int)heap.size(); heap.push_back(v); up(idx[v]); }
    void increased(int v) { if (idx[v] >= 0) up(idx[v]); }
    int removeMin() {
        int x = heap[0]; int last = heap.back(); heap.pop_back(); idx[x] = -1;
        if (!heap.empty()) { heap[0] = last; idx[last] = 0; down(0); }
        return x;
    }
};

struct Solver {
    int nvars = 0;
    bool ok = true;
    vector<Clause*> clauses;                 // every clause of the current formula (original + learnt, incl. units)
    vector<vector<Watch>> watches;           // watches[l]: clauses watching literal l
    vector<int8_t> val;                      // per literal: 1 true, -1 false, 0 unassigned
    vector<int> level;
    vector<Clause*> reason;
    vector<Lit> trail;
    vector<int> trail_lim;
    size_t qhead = 0;
    vector<double> activity; double var_inc = 1.0; const double var_decay = 0.95;
    VarHeap heap;
    vector<int8_t> polarity; bool save_phases = true;
    double cla_inc = 1.0; const double cla_decay = 0.999;
    // configuration
    bool sdcl = false, filtered = true; long long inner_limit = 100; long long conflict_limit = -1; double time_limit = -1;
    bool is_inner = false;
    FILE* proof = nullptr;
    Stats st;
    // analysis scratch
    vector<int8_t> seen; vector<Lit> analyze_stack, analyze_toclear, learnt_tmp; vector<int> lbd_stamp; int lbd_counter = 0;
    vector<int> vmap;
    vector<int> memo_stamp; vector<int8_t> memo_val; int memo_counter = 0;   // per-reduct memo of single-literal filter tests
    chrono::steady_clock::time_point t_start;
    long long next_reduce = 2000;

    ~Solver() { for (Clause* c : clauses) delete c; }

    double elapsed() const { return chrono::duration<double>(chrono::steady_clock::now() - t_start).count(); }
    int decisionLevel() const { return (int)trail_lim.size(); }
    // Schedule counter for restarts and database reduction.  Literal reading of PHASE3.md 2.3.2: "conflicts" are
    // real conflicts; a successful prune (PR learn) is not a conflict.  (SaDiCaL instead counts prunes as conflicts;
    // that alternative was tried on the smoke test only and is recorded in NOTES.md, not used.)
    bool prunes_as_conflicts = false;      // --prunes-as-conflicts: SaDiCaL's convention for the schedules
    long long schedCount() const { return prunes_as_conflicts ? st.conflicts + st.pr_learnt : st.conflicts; }

    void init(int n) {
        nvars = n; val.assign(2 * n, 0); level.assign(n, 0); reason.assign(n, nullptr); activity.assign(n, 0.0);
        polarity.assign(n, 0); seen.assign(n, 0); watches.assign(2 * n, vector<Watch>()); lbd_stamp.assign(n + 2, 0);
        vmap.assign(n, -1); memo_stamp.assign(2 * n, 0); memo_val.assign(2 * n, 0);
        heap.init(&activity, n); for (int v = 0; v < n; v++) heap.insert(v);
        t_start = chrono::steady_clock::now();
    }

    void enqueue(Lit p, Clause* from) {
        val[p] = 1; val[lneg(p)] = -1; level[lvar(p)] = decisionLevel(); reason[lvar(p)] = from; trail.push_back(p);
    }

    void attach(Clause* c) {
        watches[c->lits[0]].push_back(Watch{c, c->lits[1]});
        watches[c->lits[1]].push_back(Watch{c, c->lits[0]});
    }

    void cancelUntil(int lvl) {
        if (decisionLevel() > lvl) {
            for (int i = (int)trail.size() - 1; i >= trail_lim[lvl]; i--) {
                Lit p = trail[i]; int v = lvar(p);
                val[p] = 0; val[lneg(p)] = 0; reason[v] = nullptr;
                if (save_phases) polarity[v] = (int8_t)((p & 1) ? 0 : 1);
                heap.insert(v);
            }
            trail.resize(trail_lim[lvl]); trail_lim.resize(lvl); qhead = trail.size();
        }
    }

    // ---- proof logging ----
    void logLits(const vector<Lit>& lits) { for (Lit l : lits) fprintf(proof, "%d ", toDimacs(l)); fputs("0\n", proof); }
    void logClause(const vector<Lit>& lits) { if (proof) logLits(lits); }
    void logDelete(const vector<Lit>& lits) { if (proof) { fputs("d ", proof); logLits(lits); } }
    void logEmpty() { if (proof) fputs("0\n", proof); }

    // ---- adding original clauses ----
    bool addClause(vector<Lit> lits) {
        if (!ok) return false;
        sort(lits.begin(), lits.end());
        lits.erase(unique(lits.begin(), lits.end()), lits.end());
        for (size_t i = 0; i + 1 < lits.size(); i++) if (lits[i + 1] == lneg(lits[i])) return true;   // tautology: drop
        Clause* c = new Clause; c->lits = lits; clauses.push_back(c);
        if (lits.empty()) { ok = false; }
        else if (lits.size() == 1) { if (val[lits[0]] == -1) ok = false; else if (val[lits[0]] == 0) enqueue(lits[0], nullptr); }
        else attach(c);
        return ok;
    }

    // ---- propagation (two watched literals with blockers) ----
    Clause* propagate() {
        Clause* confl = nullptr;
        while (qhead < trail.size()) {
            Lit p = trail[qhead++];
            Lit falseLit = lneg(p);
            vector<Watch>& ws = watches[falseLit];
            size_t i = 0, j = 0, n = ws.size();
            st.propagations++;
            while (i < n) {
                Watch w = ws[i++];
                if (w.c->deleted) continue;
                if (val[w.blocker] == 1) { ws[j++] = w; continue; }
                Clause& c = *w.c;
                if (c.lits[0] == falseLit) { c.lits[0] = c.lits[1]; c.lits[1] = falseLit; }
                Lit first = c.lits[0];
                Watch nw{w.c, first};
                if (first != w.blocker && val[first] == 1) { ws[j++] = nw; continue; }
                bool found = false;
                for (size_t k = 2; k < c.lits.size(); k++) {
                    if (val[c.lits[k]] != -1) {
                        c.lits[1] = c.lits[k]; c.lits[k] = falseLit;
                        watches[c.lits[1]].push_back(nw); found = true; break;
                    }
                }
                if (found) continue;
                ws[j++] = nw;
                if (val[first] == -1) { confl = w.c; qhead = trail.size(); while (i < n) ws[j++] = ws[i++]; }
                else enqueue(first, w.c);
            }
            ws.resize(j);
        }
        return confl;
    }

    // ---- VSIDS / clause activity ----
    void varBumpActivity(int v) {
        if ((activity[v] += var_inc) > 1e100) { for (int i = 0; i < nvars; i++) activity[i] *= 1e-100; var_inc *= 1e-100; }
        heap.increased(v);
    }
    void varDecayActivity() { var_inc /= var_decay; }
    void claBumpActivity(Clause& c) {
        if ((c.activity += cla_inc) > 1e20) { for (Clause* d : clauses) if (d->learnt) d->activity *= 1e-20; cla_inc *= 1e-20; }
    }
    void claDecayActivity() { cla_inc /= cla_decay; }

    uint32_t abstractLevel(int v) const { return 1u << (level[v] & 31); }

    bool litRedundant(Lit p, uint32_t abstract_levels) {
        analyze_stack.clear(); analyze_stack.push_back(p);
        size_t top = analyze_toclear.size();
        while (!analyze_stack.empty()) {
            Clause& c = *reason[lvar(analyze_stack.back())]; analyze_stack.pop_back();
            for (size_t i = 1; i < c.lits.size(); i++) {
                Lit q = c.lits[i]; int v = lvar(q);
                if (!seen[v] && level[v] > 0) {
                    if (reason[v] != nullptr && (abstractLevel(v) & abstract_levels) != 0) {
                        seen[v] = 1; analyze_stack.push_back(q); analyze_toclear.push_back(q);
                    } else {
                        for (size_t j = top; j < analyze_toclear.size(); j++) seen[lvar(analyze_toclear[j])] = 0;
                        analyze_toclear.resize(top);
                        return false;
                    }
                }
            }
        }
        return true;
    }

    // 1-UIP conflict analysis with recursive minimisation; out_learnt[0] is the asserting literal.
    void analyze(Clause* confl, vector<Lit>& out_learnt, int& out_btlevel, int& out_lbd) {
        int pathC = 0; Lit p = -1;
        out_learnt.clear(); out_learnt.push_back(-1);
        int index = (int)trail.size() - 1;
        do {
            Clause& c = *confl;
            if (c.learnt) claBumpActivity(c);
            for (size_t j = (p == -1) ? 0 : 1; j < c.lits.size(); j++) {
                Lit q = c.lits[j]; int v = lvar(q);
                if (!seen[v] && level[v] > 0) {
                    varBumpActivity(v); seen[v] = 1;
                    if (level[v] >= decisionLevel()) pathC++; else out_learnt.push_back(q);
                }
            }
            while (!seen[lvar(trail[index--])]);
            p = trail[index + 1]; confl = reason[lvar(p)]; seen[lvar(p)] = 0; pathC--;
        } while (pathC > 0);
        out_learnt[0] = lneg(p);
        analyze_toclear = out_learnt;
        uint32_t abstract_levels = 0;
        for (size_t i = 1; i < out_learnt.size(); i++) abstract_levels |= abstractLevel(lvar(out_learnt[i]));
        size_t j = 1;
        for (size_t i = 1; i < out_learnt.size(); i++)
            if (reason[lvar(out_learnt[i])] == nullptr || !litRedundant(out_learnt[i], abstract_levels)) out_learnt[j++] = out_learnt[i];
        out_learnt.resize(j);
        if (out_learnt.size() == 1) out_btlevel = 0;
        else {
            size_t max_i = 1;
            for (size_t i = 2; i < out_learnt.size(); i++) if (level[lvar(out_learnt[i])] > level[lvar(out_learnt[max_i])]) max_i = i;
            swap(out_learnt[1], out_learnt[max_i]);
            out_btlevel = level[lvar(out_learnt[1])];
        }
        lbd_counter++; out_lbd = 0;
        for (Lit l : out_learnt) { int lv = level[lvar(l)]; if (lbd_stamp[lv] != lbd_counter) { lbd_stamp[lv] = lbd_counter; out_lbd++; } }
        for (Lit l : analyze_toclear) seen[lvar(l)] = 0;
    }

    bool locked(Clause* c) const { return reason[lvar(c->lits[0])] == c && val[c->lits[0]] == 1; }

    // every 2,000 conflicts: keep LBD <= 2 and the most active half of the rest
    void reduceDB() {
        st.reductions++;
        vector<Clause*> cands;
        for (Clause* c : clauses) if (c->learnt && !c->deleted && c->lbd > 2 && c->lits.size() > 1 && !locked(c)) cands.push_back(c);
        sort(cands.begin(), cands.end(), [](Clause* a, Clause* b) { return a->activity > b->activity; });
        for (size_t i = (cands.size() + 1) / 2; i < cands.size(); i++) { cands[i]->deleted = true; st.removed_clauses++; logDelete(cands[i]->lits); }
        for (auto& ws : watches) { size_t j = 0; for (auto& w : ws) if (!w.c->deleted) ws[j++] = w; ws.resize(j); }
        size_t j = 0;
        for (Clause* c : clauses) { if (c->deleted) delete c; else clauses[j++] = c; }
        clauses.resize(j);
    }

    Lit pickBranchLit() {
        int v = -1;
        while (v == -1 || val[2 * v] != 0) { if (heap.empty()) return -1; v = heap.removeMin(); }
        return polarity[v] ? 2 * v : 2 * v + 1;
    }

    // F|alpha |-1 (l1 v ... v lk)?  i.e. does assuming the negations of the (unassigned) lits yield a conflict by unit propagation
    bool impliedByUP(const vector<Lit>& lits) {
        int lvl = decisionLevel();
        trail_lim.push_back((int)trail.size());
        bool saved = save_phases; save_phases = false;
        for (Lit l : lits) if (val[l] == 0) enqueue(lneg(l), nullptr);
        long long p0 = st.propagations;
        Clause* confl = propagate();
        st.filter_propagations += st.propagations - p0; st.propagations = p0;
        cancelUntil(lvl);
        save_phases = saved;
        return confl != nullptr;
    }

    // The SDCL step: build the (filtered) positive reduct of the current formula w.r.t. the full trail alpha,
    // solve it with an inner plain CDCL limited to inner_limit conflicts; on SAT learn the negation of the decisions.
    bool sdclStep() {
        st.reduct_checks++;
        auto t0 = chrono::steady_clock::now();
        int d = decisionLevel();
        size_t m = trail.size();
        memo_counter++;
        for (size_t i = 0; i < m; i++) vmap[lvar(trail[i])] = (int)i;
        vector<vector<Lit>> red; red.reserve(clauses.size() + 1);
        vector<Lit> touched, untouched;
        for (Clause* c : clauses) {
            if (c->deleted) continue;
            bool sat = false;
            for (Lit l : c->lits) if (val[l] == 1) { sat = true; break; }
            if (!sat) continue;
            touched.clear(); untouched.clear();
            for (Lit l : c->lits) { if (val[l] == 0) untouched.push_back(l); else touched.push_back(l); }
            if (filtered && !untouched.empty()) {
                bool implied;
                if (untouched.size() == 1) {
                    // exact memoisation: same alpha, same formula, same untouched literal => same answer
                    Lit u = untouched[0];
                    if (memo_stamp[u] == memo_counter) implied = memo_val[u] != 0;
                    else { st.filter_tests++; implied = impliedByUP(untouched); memo_stamp[u] = memo_counter; memo_val[u] = implied ? 1 : 0; }
                } else { st.filter_tests++; implied = impliedByUP(untouched); }
                if (implied) { st.filtered_clauses++; continue; }
            }
            vector<Lit> mapped; mapped.reserve(touched.size());
            for (Lit l : touched) mapped.push_back(2 * vmap[lvar(l)] + (l & 1));
            red.push_back(std::move(mapped));
        }
        {
            vector<Lit> blk; blk.reserve(m);
            for (size_t i = 0; i < m; i++) { Lit l = trail[i]; blk.push_back(2 * vmap[lvar(l)] + ((l & 1) ^ 1)); }
            red.push_back(std::move(blk));
        }
        st.reduct_clauses += (long long)red.size();
        for (auto& cl : red) st.reduct_lits += (long long)cl.size();
        if ((long long)m > st.max_reduct_vars) st.max_reduct_vars = (long long)m;
        auto t1 = chrono::steady_clock::now();
        st.time_reduct_build += chrono::duration<double>(t1 - t0).count();

        Solver inner; inner.is_inner = true; inner.sdcl = false; inner.conflict_limit = inner_limit; inner.init((int)m);
        for (auto& cl : red) inner.addClause(cl);
        Result r = inner.solve();
        st.inner_conflicts += inner.st.conflicts; st.inner_decisions += inner.st.decisions; st.inner_propagations += inner.st.propagations;
        st.time_inner += chrono::duration<double>(chrono::steady_clock::now() - t1).count();
        if (r != R_SAT) { if (r == R_UNSAT) st.reduct_unsat++; else st.reduct_limit++; return false; }
        st.reduct_sat++;

        // learnt clause: negation of the decision literals, last decision first
        vector<Lit> C; C.reserve(d);
        for (int k = d; k >= 1; k--) C.push_back(lneg(trail[trail_lim[k - 1]]));
        int piv = -1;
        for (size_t i = 0; i < C.size(); i++) {
            Lit l = C[i]; Lit il = 2 * vmap[lvar(l)] + (l & 1);
            if (inner.val[il] == 1) { piv = (int)i; break; }
        }
        if (piv < 0) { fprintf(stderr, "c INTERNAL ERROR: reduct witness agrees with every decision literal\n"); exit(3); }
        if (proof) {
            fprintf(proof, "%d ", toDimacs(C[piv]));
            for (size_t i = 0; i < C.size(); i++) if ((int)i != piv) fprintf(proof, "%d ", toDimacs(C[i]));
            fprintf(proof, "%d ", toDimacs(C[piv]));
            int pv = lvar(C[piv]);
            for (size_t i = 0; i < m; i++) {
                int v = lvar(trail[i]); if (v == pv) continue;
                Lit wl = (inner.val[2 * (int)i] == 1) ? 2 * v : 2 * v + 1;
                fprintf(proof, "%d ", toDimacs(wl));
            }
            fputs("0\n", proof);
        }
        st.pr_learnt++; st.learnt_clauses++; st.pr_lits += (long long)C.size();
        cancelUntil(d - 1);
        Clause* c = new Clause; c->lits = C; c->learnt = true; c->pr = true; c->lbd = (int)C.size(); clauses.push_back(c);
        if (C.size() == 1) enqueue(C[0], nullptr);
        else { attach(c); claBumpActivity(*c); enqueue(C[0], c); }
        return true;
    }

    Result solve() {
        if (!ok) { logEmpty(); return R_UNSAT; }
        int restart_count = 0; long long conflicts_at_restart = 0; double restart_limit = 100.0 * luby(2, 0);
        while (true) {
            Clause* confl = propagate();
            if (confl) {
                st.conflicts++;
                if (decisionLevel() == 0) { logEmpty(); return R_UNSAT; }
                int bt, lbd;
                analyze(confl, learnt_tmp, bt, lbd);
                cancelUntil(bt);
                Clause* c = new Clause; c->lits = learnt_tmp; c->learnt = true; c->lbd = lbd; clauses.push_back(c); st.learnt_clauses++;
                logClause(learnt_tmp);
                if (learnt_tmp.size() == 1) enqueue(learnt_tmp[0], nullptr);
                else { attach(c); claBumpActivity(*c); enqueue(learnt_tmp[0], c); }
                varDecayActivity(); claDecayActivity();
                if (!is_inner && schedCount() >= next_reduce) { reduceDB(); next_reduce += 2000; }
                if (conflict_limit >= 0 && st.conflicts >= conflict_limit) return R_UNKNOWN;
                if (time_limit > 0 && (st.conflicts & 63) == 0 && elapsed() > time_limit) return R_UNKNOWN;
            } else {
                if ((double)(schedCount() - conflicts_at_restart) >= restart_limit) {
                    restart_count++; st.restarts++; cancelUntil(0); conflicts_at_restart = schedCount();
                    restart_limit = 100.0 * luby(2, restart_count); continue;
                }
                if ((int)trail.size() == nvars) return R_SAT;
                if (sdcl && decisionLevel() >= 1) {
                    if (time_limit > 0 && elapsed() > time_limit) return R_UNKNOWN;
                    if (sdclStep()) {
                        varDecayActivity(); claDecayActivity();
                        if (!is_inner && schedCount() >= next_reduce) { reduceDB(); next_reduce += 2000; }
                        continue;
                    }
                }
                Lit next = pickBranchLit();
                if (next < 0) return R_SAT;
                st.decisions++; trail_lim.push_back((int)trail.size()); enqueue(next, nullptr);
            }
        }
    }
};

static bool parseDimacs(const char* path, Solver& S, int& nv, int& nc) {
    FILE* f = fopen(path, "rb");
    if (!f) { fprintf(stderr, "c cannot open %s\n", path); return false; }
    vector<char> buf; { fseek(f, 0, SEEK_END); long sz = ftell(f); fseek(f, 0, SEEK_SET); buf.resize(sz + 1); size_t rd = fread(buf.data(), 1, sz, f); buf[rd] = 0; }
    fclose(f);
    char* p = buf.data();
    nv = nc = -1;
    vector<Lit> cl; bool inited = false; int count = 0;
    while (*p) {
        while (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n') p++;
        if (!*p) break;
        if (*p == 'c') { while (*p && *p != '\n') p++; continue; }
        if (*p == '%') break;                                  // SATLIB end-of-file marker ("%\n0\n")
        if (*p == 'p') {
            if (sscanf(p, "p cnf %d %d", &nv, &nc) != 2) { fprintf(stderr, "c bad header\n"); return false; }
            S.init(nv); inited = true; while (*p && *p != '\n') p++; continue;
        }
        char* e; long v = strtol(p, &e, 10);
        if (e == p) { fprintf(stderr, "c parse error near '%.20s'\n", p); return false; }
        p = e;
        if (!inited) { fprintf(stderr, "c clause before header\n"); return false; }
        if (v == 0) { S.addClause(cl); cl.clear(); count++; }
        else {
            if (labs(v) > nv) { fprintf(stderr, "c variable %ld out of range\n", v); return false; }
            cl.push_back(fromDimacs((int)v));
        }
    }
    if (!cl.empty()) { S.addClause(cl); count++; }
    return true;
}

int main(int argc, char** argv) {
    const char* input = nullptr; const char* proofPath = nullptr; string mode = "sdcl"; double tlim = -1; bool printModel = true;
    long long innerLimit = 100; bool prunesAsConflicts = false;
    for (int i = 1; i < argc; i++) {
        if (!strncmp(argv[i], "--mode=", 7)) mode = argv[i] + 7;
        else if (!strncmp(argv[i], "--proof=", 8)) proofPath = argv[i] + 8;
        else if (!strncmp(argv[i], "--time-limit=", 13)) tlim = atof(argv[i] + 13);
        else if (!strncmp(argv[i], "--inner-limit=", 14)) innerLimit = atoll(argv[i] + 14);
        else if (!strcmp(argv[i], "--no-model")) printModel = false;
        else if (!strcmp(argv[i], "--prunes-as-conflicts")) prunesAsConflicts = true;
        else if (argv[i][0] == '-') { fprintf(stderr, "unknown option %s\n", argv[i]); return 1; }
        else input = argv[i];
    }
    if (!input) { fprintf(stderr, "usage: sdcl [--mode=sdcl|plain|unfiltered] [--proof=FILE] [--time-limit=SEC] [--no-model] input.cnf\n"); return 1; }
    Solver S;
    if (mode == "sdcl") { S.sdcl = true; S.filtered = true; }
    else if (mode == "plain") { S.sdcl = false; }
    else if (mode == "unfiltered") { S.sdcl = true; S.filtered = false; }
    else { fprintf(stderr, "bad mode\n"); return 1; }
    S.inner_limit = innerLimit; S.time_limit = tlim; S.prunes_as_conflicts = prunesAsConflicts;
    if (proofPath) { S.proof = fopen(proofPath, "w"); if (!S.proof) { fprintf(stderr, "cannot write proof\n"); return 1; } }
    auto t0 = chrono::steady_clock::now();
    int nv, nc;
    if (!parseDimacs(input, S, nv, nc)) return 1;
    S.t_start = chrono::steady_clock::now();
    Result r = S.solve();
    double total = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    if (S.proof) fclose(S.proof);
    printf("c mode %s\nc vars %d clauses %d\nc prunes_as_conflicts %d\n", mode.c_str(), nv, nc, (int)prunesAsConflicts);
    const Stats& s = S.st;
    printf("c stat conflicts %lld\nc stat decisions %lld\nc stat propagations %lld\nc stat restarts %lld\nc stat reductions %lld\n",
           s.conflicts, s.decisions, s.propagations, s.restarts, s.reductions);
    printf("c stat learnt_clauses %lld\nc stat removed_clauses %lld\n", s.learnt_clauses, s.removed_clauses);
    printf("c stat reduct_checks %lld\nc stat reduct_sat %lld\nc stat reduct_unsat %lld\nc stat reduct_limit %lld\n",
           s.reduct_checks, s.reduct_sat, s.reduct_unsat, s.reduct_limit);
    printf("c stat inner_conflicts %lld\nc stat inner_decisions %lld\nc stat inner_propagations %lld\nc stat pr_learnt %lld\nc stat pr_lits %lld\n",
           s.inner_conflicts, s.inner_decisions, s.inner_propagations, s.pr_learnt, s.pr_lits);
    printf("c stat filter_tests %lld\nc stat filtered_clauses %lld\nc stat reduct_clauses %lld\nc stat reduct_lits %lld\nc stat filter_propagations %lld\nc stat max_reduct_vars %lld\n",
           s.filter_tests, s.filtered_clauses, s.reduct_clauses, s.reduct_lits, s.filter_propagations, s.max_reduct_vars);
    printf("c stat cost %lld\n", s.conflicts + s.inner_conflicts + s.reduct_checks);
    printf("c stat time_reduct_build %.3f\nc stat time_inner %.3f\nc stat time_total %.3f\n", s.time_reduct_build, s.time_inner, total);
    if (r == R_SAT) {
        puts("s SATISFIABLE");
        if (printModel) {
            printf("v");
            for (int v = 0; v < nv; v++) printf(" %d", S.val[2 * v] == 1 ? v + 1 : -(v + 1));
            puts(" 0");
        }
        return 10;
    } else if (r == R_UNSAT) { puts("s UNSATISFIABLE"); return 20; }
    else { puts("s UNKNOWN"); return 0; }
}
