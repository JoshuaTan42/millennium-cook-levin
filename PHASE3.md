# PHASE3.md — SAT ∈ P: barrier survey, candidate screen, pre-registered falsification plans

Written 2026-10-05 (Phase 3 session: no Lean run, no Python run, no edits to `SatInP.lean` or any
proved file; nothing committed). Project status: **NOT PROVED**. The only open lemma is
`PvsNP.sat_in_p` (SatInP.lean).

Conventions. A bracketed key such as [Hak85] is a citation (list at the end). **[derived here]** marks
a claim that is mine; its proof is in an appendix. Where I am unsure of a technical detail I say so
inline rather than smoothing it over.

---

## 0. Summary

**Target.** `PvsNP.sat_in_p : InPolynomialTime (fin_encoding_string Bool) SAT`, where `SAT` is dense
CNF-SAT over `List Bool` (NOTES.md, "SAT: concrete definition"): a CNF with `m` clauses over `n`
variables is a word of `2m(n+1)` bits. "Polynomial time" therefore means polynomial in `m·n`, so any
algorithm with running time polynomial in `n` and `m` qualifies once it is implemented as a `FinTM2`
machine. By Phase 2 standards the machine construction would be routine engineering; the entire
difficulty is the algorithm and the proof that it is correct and polynomial. This document works at
the level of algorithms.

**Method.** §1 collects what any polynomial-time SAT algorithm must get past. §2 proposes three
candidates, each specific enough to implement, and runs the paper checks of §1.6 on each. §3 is the
kill log. §4 ranks the survivors. §5 is the overall assessment.

| Candidate | One-line description | Verdict |
|---|---|---|
| C1 | Static degree-`d` hierarchy: degree-`d` sum-of-squares (Lasserre level `d`) over ℝ plus degree-`d` polynomial calculus over GF(p), `d` fixed | **KILLED** on paper: degree lower bounds on random 3-CNF for both components (and it produces wrong answers) |
| C2 | LP-based branch-and-cut: simplex relaxation + Gomory–Chvátal cuts + branching on variables | **KILLED** on paper: its runs are cutting-planes refutations (deduction lemma, Appendix A); cutting planes has exponential lower bounds on clique-colouring and on random Θ(log n)-CNF |
| C3 | Satisfaction-driven clause learning: CDCL that learns propagation-redundant (PR) clauses found by solving positive reducts | **SURVIVES the paper screen by default**: its runs are PR⁻ proofs (⊆ extended resolution), for which no superpolynomial lower bounds are known. There is no positive evidence either. |

**Recommendation.** Run Phase 4 on C3 with the plan fixed in §2.3.8. My estimate that C3 survives that
plan is below 1 in 1000. The most likely kill: exponential scaling on unsatisfiable random 3-SAT near
ratio 4.26 at `n ≤ 250`, with no separation from the plain-CDCL ablation.

**Assessment.** Everything in this document is consistent with P ≠ NP and nothing in it is evidence
for P = NP (§5).

---

## 1. What any polynomial-time SAT algorithm must get past

### 1.1 The transcript observation: an algorithm is a proof system

Let `A` be a deterministic algorithm deciding SAT in time `p(|φ|)`. Define the proof system `P_A`:
a "proof" that `φ` is unsatisfiable is `φ` itself, and the verifier runs `A`. **[derived here;
folklore]**

* `P_A` is a Cook–Reckhow proof system for UNSAT [CR79]: sound, complete, polynomial-time verifiable.
* `P_A` is polynomially bounded (every unsatisfiable `φ` has a proof of size `|φ|`), so NP = coNP.
* If P = NP then every proof system is automatizable (finding a proof of size ≤ s is an NP search
  problem), in particular the systems of §1.3.4 whose automatization is known to be hard.

**Proposition 1.2 (how lower bounds kill algorithms).** Suppose that on every unsatisfiable input `φ`
the run of `A` can be translated, with polynomial blow-up, into a refutation of `φ` in a proof system
`S`. If an explicit family `{φ_n}` requires `S`-refutations of superpolynomial size, then `A` runs in
superpolynomial time on `{φ_n}`. Proof: the translated refutation has size at least the `S`-lower
bound and at most a polynomial in the run length. ∎ **[derived here]**

So for every candidate the decisive question is: **what is the weakest known proof system `S` into
which the candidate's UNSAT runs translate with polynomial blow-up?** If `S` has known
superpolynomial lower bounds the candidate is dead, and the hard family is an explicit kill instance.
If no lower bounds are known for `S`, the candidate is not killed, but note what that means: nobody
knows a lower bound, and nobody knows an upper bound either (whether random 3-CNFs have
polynomial-size Frege proofs is open).

Two caveats.

1. The identification of `S` must cover the whole implementation, including preprocessing. Bounded
   variable elimination is resolution; bounded variable addition [MHB12] and other re-encodings
   introduce extension variables, which moves the transcript from resolution to extended resolution.
   A solver stack is as strong as its strongest component, so the screen must be applied to the stack.
2. Randomized algorithms. A run of a randomized algorithm on an UNSAT input is not a proof. The
   observation still constrains them: NP ⊆ BPP implies NP = RP [Ko82] and PH = BPP; if the algorithm
   emits any checkable certificate on UNSAT inputs, the screen applies to that certificate; [PS10]
   develop the general relation between algorithms and proof systems ("effective simulations"). None
   of the candidates below uses randomness essentially.

### 1.2 Barriers

**Relativization [BGS75].** There are oracles `A`, `B` with `P^A = NP^A` and `P^B ≠ NP^B`, so no
proof of either direction relativizes. For an algorithmic proof of SAT ∈ P the content is this: if
the correctness-and-time proof used the formula only as a black box (queries "does assignment `a`
satisfy `φ`?"), it would go through verbatim for SAT with oracle gates relative to `B` and give
`P^B = NP^B`. Hence the proof of the core lemma must use the explicit syntactic structure of clauses
(which variables occur where, unit propagation, counting, linear algebra on clauses). Every candidate
below does use syntax; the barrier check for each therefore reduces to naming the step where syntax
is used essentially and confirming that nothing else is a black-box argument.

**Algebrization [AW09].** Aaronson and Wigderson show that P vs NP needs non-algebrizing techniques
in both directions; the direction relevant here is that there exist an oracle `A` and a low-degree
extension `Ã` with `NP^A ⊄ P^Ã`. So a proof whose use of the formula factors through its
arithmetization (evaluating the low-degree extension of the clause-satisfaction function at field
points, as in sum-check or IP = PSPACE) cannot work either. The non-algebrizing content must be
Boolean and discrete: unit propagation, integrality and rounding, case splitting, redundancy checks.
Each candidate's check names that step.

**Natural proofs [RR97]** constrain proofs of circuit lower bounds, i.e., the P ≠ NP direction; the
same holds for geometric complexity theory. Neither constrains an algorithm for SAT. There is no
theorem that excludes every algorithmic approach; the operative filter for the P = NP direction is
§1.1 together with the lower bounds of §1.3 and the automatizability results of §1.3.4.

### 1.3 Proof complexity: what is known to be hard where

Families. **PHP** = pigeonhole principle `PHP_{n+1}^n`. **Tseitin** = Tseitin contradictions on
bounded-degree expanders (3-CNF after clausification). **R3** = random 3-CNF with `Δn` clauses,
`Δ` a constant above the threshold (UNSAT w.h.p.: for `Δ > 5.19` by the first-moment bound
`2^n (7/8)^{Δn} → 0`, for `Δ > 4.49` by [DKMP09]). **CC** = clique-colouring tautologies
("`G` has a `k`-clique and is `(k−1)`-colourable").

E = polynomial-size proofs known; H = superpolynomial lower bound known; ? = open to my knowledge.

| Proof system | PHP | Tseitin | R3 | CC | Notes |
|---|---|---|---|---|---|
| Tree-like resolution, DPLL | H | H | H | H | subsumed by the resolution row |
| Resolution (= CDCL, §1.4a) | H [Hak85] | H [Urq87] | H [CS88] | H [Kra97, Pud97] | width–size relation [BW01] |
| Cutting planes (CP) | **E** [CCT87] | quasi-polynomial upper bound [DT20, FGIPRTW], so no superpolynomial lower bound exists | ? (H for random Θ(log n)-CNF [FPPR17, HP17]) | H [Pud97]; small coefficients [BPR97] | |
| Nullstellensatz (NS) | H [BIKPP96] | H [Gri98] | H (via PC) | ? | NS degree ≥ PC degree |
| Polynomial calculus (PC, PCR), any field | H, degree ≥ n/2+1 [Raz98] | H for char ≠ 2 [BGIP01]; **E** for char 2 (Gaussian elimination) | H: char 2 [AR03], char ≠ 2 [BI99]; exposition [MN15] | ? | size ≥ exp(Ω(deg²/n)) [IPS99] |
| Sherali–Adams (SA) | ? (not needed here) | H (via SoS) | H (via SoS) | ? | SoS ≥ SA at equal degree [Lau03] |
| Sum-of-squares, static degree (Lasserre) | **E**, degree ≤ 4 with the linear clause encoding (Appendix B) | H, degree Ω(n) [Gri01] | H, degree Ω(n) [Sch08] | ? | size ≥ exp(Ω(deg²/n)) [AH19] |
| Lovász–Schrijver LS, LS+, LS^d (dynamic) | rank bounds known; dag-like size **open** [BPS07] | LS^d has short proofs [GHP02] | ? | short proofs [GHP02] | not an algorithm; see §2.1.4 |
| Bounded-depth Frege | H [Ajt94, KPW95, PBI93, Hås23] | H [BS02, PRST16, Hås21] | **?** (only Ω(n^{1+ε}) [GT24]) | ? | |
| AC⁰[p]-Frege | ? | ? | ? | ? | no lower bounds known for any family [GK18] |
| Frege; extended Frege (EF) = extended resolution (ER) | E [Bus87]; ER: [Coo76] | E (ER simulates Gaussian elimination) | **?** | E (via PHP [Bus87]) | no lower bounds known |
| Res(⊕) (resolution over GF(2)-linear clauses) | tree-like H [IS20]; dag-like ? | E | ? | ? | dag-like size open; regular Res(⊕) has exponential lower bounds [EGI24]; depth-bounded lower bounds [EI25] |
| OBDD(∧, weakening), fixed order | H [TSZ10] (for OBDD(∧)) | ? | ? | H [Kra08, Seg08] | reordering strictly stronger [BIKS18]; tree-like with reorders H [IKRS20] |
| Resolution + symmetry rules (SR-I, local SR) | E [Urq99] | ? | H in effect (Appendix D) | E [AU00] | exponential lower bounds for the local symmetry rule [Urq99] |
| PR⁻, SPR⁻ (propagation redundancy, no new variables) | E | E | ? | E | all E: [BT21]; RAT⁻ H [BT21]; SBC⁻ H [Yol24]; PR⁻/SPR⁻ lower bounds open; PR⁻ ⊆ ER [HB18, KRH18] |
| Ideal proof system (IPS) | E | E | ? | E | lower bounds would give VP ≠ VNP [GP18] |

Three structural facts used below.

* **Size–degree.** Resolution [BW01], PC [IPS99] and SoS [AH19] satisfy size ≥ exp(Ω(degree²/n)), so a
  degree-Ω(n) lower bound is an exp(Ω(n)) size lower bound. "The algorithm only uses bounded degree"
  is fatal wherever degree lower bounds exist.
* **PHP is easy for SoS and for CP.** A plan that tests only PHP cannot kill an SDP- or IP-based
  candidate. The right kill families there are R3 and Tseitin (SoS) and CC (CP).
* **R3 has the broadest known hardness** (resolution, PC over every field, SoS, hence SA and LS+
  rank) and no known polynomial-size proofs in any system. Any working candidate must do something on
  R3 that no analysed proof system does.

#### 1.3.4 Automatizability (consistent with P = NP, but it fixes a mandatory consequence)

Finding short proofs is itself hard: resolution [AM20], cutting planes [GKMP20] and NS/PC/SA
[dRGNPRS21] are NP-hard to automate; resolution is not automatizable unless W[P] is tractable
[AR08]; bounded-depth Frege [BDGMP04] and Frege [BPR00] are not automatizable unless factoring
(Diffie–Hellman) is easy; EF is not weakly automatizable if RSA is secure [KP98]. None of these
kills a candidate (P = NP makes every system automatizable), but together they say: a working
candidate factors integers in polynomial time. Factoring-to-SAT is therefore a compulsory test
family, not an optional one.

#### 1.3.5 Escape hatches

Systems with no known lower bounds and an algorithmic counterpart: ER/EF (ER-CDCL with extension
heuristics [AKS10], structured re-encoding [MHB12]); PR⁻/SPR⁻ (SDCL [HKSB17, HKB19], PR
preprocessing [RHB22]); dag-like Res(⊕) (CDCL with linear-form splitting [IS20]). Systems with no
known lower bounds and no proof-search algorithm: AC⁰[p]-Frege, Frege, IPS. A candidate that lands
here is unkilled, not supported.

### 1.4 Known dead ends

**(a) DPLL/CDCL ≡ resolution.** CDCL proofs are resolution proofs (learned clauses are resolvents);
with restarts and suitable choices CDCL p-simulates resolution [BKS04, PD11, AFT11]; with concrete
heuristics (VSIDS, VMTF, CHB, LRB) it is strictly weaker on some formulas [Vin20]. Killed by PHP
[Hak85], Tseitin [Urq87] and R3 [CS88]; exponential growth on R3 is also the standard experimental
fact since [MSL92]. Gaussian elimination on syntactically detected XOR constraints adds nothing on R3
(there are none w.h.p., Appendix D); symmetry breaking adds nothing on R3 either (Appendix D).

**(b) Compact LP/SDP extended formulations.** The "one polytope for all instances of size `n`"
route is closed: the TSP and stable-set polytopes need 2^{Ω(√n)} and the cut polytope 2^{Ω(n)}
inequalities in any extended formulation [FMPTW15]; matching, hence TSP, needs 2^{Ω(n)} [Rot17];
symmetric LPs already in [Yan91]; SDPs need size 2^{n^δ} [LRS15]. The "LP/SDP hierarchy" route is
closed by degree lower bounds (C1): polynomial-size LP relaxations of CSPs are no stronger than
constant-degree Sherali–Adams [CLRS16], weakly-exponential size no stronger than degree n^{Ω(1)}
[KMR17], polynomial-size SDPs no stronger than constant-degree SoS [LRS15]. The instance-dependent
route ("compute a tailored LP from `φ` in polynomial time") is not closed by these results, but it is
empty: it is an arbitrary polynomial-time algorithm whose last step happens to be an LP, and the screen
applies to the whole transcript. Recurrent error: the all-½ point satisfies every clause inequality
`Σℓ ≥ 1` with at least two literals, so the natural LP relaxation of a CNF decides nothing;
infeasibility only ever comes from cuts, branching or lifting, i.e., from one of the systems in §1.3.

**(c) Integer programming / branch-and-cut.** Screened as candidate C2: killed.

**(d) Local search and message passing.** Incomplete by construction (they never certify UNSAT), so
irrelevant to the NO side of the decision problem. On the YES side they fail well below the
threshold even on average: WalkSAT fails for `m/n > c·2^k ln²k / k` [CHH17]; survey-propagation
guided decimation fails at `(1+o(1)) 2^k ln k / k` [Het16]; low-degree polynomial algorithms have a
sharp transition near `κ* 2^k ln k / k`, `κ* ≈ 4.911` [BH22]; the structural reasons are shattering
[ACO08] and the overlap gap property [Gam21]; the best proven algorithmic threshold is [CO10]; the
original message-passing proposal is [MPZ02]. For `k = 3` none of these asymptotics bites directly,
but no polynomial-time method is known to find assignments at ratio 4.26 w.h.p. for large `n`.

**(e) OBDD / knowledge compilation.** [Kra08, Seg08, TSZ10, IKRS20, BIKS18] in the table.

**(f) Treewidth / dynamic programming.** Variable elimination along an ordering of width `w` is
ordered resolution with clauses of width ≤ `w`; random 3-CNF has treewidth Θ(n) because its incidence
graph is an expander [GM09]; killed by (a).

**(g) Symmetry.** Appendix D; theorem-level kill: exponential lower bounds for the local symmetry
rule [Urq99].

**(h) Recurring error patterns in Woeginger's list [Woe]** (my summary of the entries, not quotations):
1. an algorithm with no correctness proof, validated on small instances;
2. a reduction in the wrong direction, or from a tractable special case (2-SAT, Horn, bounded
   treewidth, planar) presented as the general problem;
3. a hidden exponential object: an LP with exponentially many constraints and no separation oracle,
   "symbolic" enumeration, or integers with exponentially many bits at unit cost;
4. an LP relaxation asserted to be integral (the Swart-type TSP formulations, closed by [Yan91,
   FMPTW15]);
5. a resolution/DPLL variant asserted polynomial, refuted by [Hak85, Urq87, CS88];
6. an encoding into another NP-hard problem (Hamiltonian cycle, isomorphism-like problems) that moves
   the hardness instead of removing it;
7. a heuristic with an empirical scaling argument;
8. a probabilistic or quantum argument that is not an algorithm.

The screen catches 1, 5 and 7 by §1.1 and the pre-registered plans; 2 and 6 by the statement check
(DEFINITIONS.md) plus the demand for one concrete algorithm for the whole language; 3 and 4 by the
cost accounting and by (b).

### 1.5 Mandatory consequences of SAT ∈ P (sanity constraints on any candidate)

1. Factoring in polynomial time (factoring ∈ NP ∩ coNP). Test family F6.
2. NP = coNP: the candidate's transcript is a polynomial-size proof of every unsatisfiable formula,
   in particular of R3, for which no polynomial-size proofs are known in any studied system.
3. Every proof system is automatizable; for EF this breaks RSA-type assumptions [KP98] (consistent
   with 1).
4. P = BPP (PH collapses to P and BPP ⊆ Σ₂).

None is a kill. They are what a surviving candidate must visibly deliver.

### 1.6 Checklist applied to every candidate

1. Algorithm specification (deterministic, every parameter fixed) and claimed time bound.
2. Core lemma, stated so that its truth implies `sat_in_p`.
3. Barrier check: name the syntactic step; confirm no black-box or arithmetization-only argument.
4. Proof-complexity check: name the weakest known `S` with `P_A ≤_p S`; look `S` up in §1.3.
5. Dead-end screen against §1.4.
6. Mandatory consequences, §1.5.
7. Pre-registered falsification plan: families, sizes, cost measure, kill criteria, predictions.

---

## 2. Candidates

### 2.1 C1 — static degree-d hierarchy (SoS over ℝ + PC over GF(p))

**2.1.1 Algorithm A1(d), `d` fixed.** Input: CNF `φ` with variables `x_1..x_n` and clauses
`C_1..C_m`.

(i) Real component. Constraints `x_i² − x_i = 0`; for each clause `C`, `Σ_{ℓ∈C} ℓ − 1 ≥ 0` with
`x ↦ x`, `¬x ↦ 1 − x` (linear clause encoding; every clause has degree 1, the most generous choice
for the candidate). Decide whether a degree-`d` SoS refutation exists:
`−1 = Σ_j s_j g_j + Σ_i h_i (x_i² − x_i)` with the `s_j` sums of squares and every term of degree
≤ `d`. This is an SDP of size `n^{O(d)}`, solvable in polynomial time for fixed `d` up to the
bit-complexity caveat [OD17, RW17]; the caveat can only weaken the candidate.

(ii) Finite-field components. For each prime `p ≤ n`: clause `C ↦ Π_{ℓ∈C}(1 − ℓ) = 0` (product
encoding, degree = width; clauses wider than `d` are dropped, which only weakens the candidate);
field equations `x_i² − x_i = 0`; decide whether 1 lies in the degree-`d` truncation of the ideal
(degree-`d` polynomial calculus) by linear algebra over the polynomials of degree ≤ `d`: `n^{O(d)}`
time.

Output UNSAT if any component refutes; otherwise output SAT and extract an assignment by
self-reduction (fix `x_1`, rerun, and so on; if the self-reduction ever fails to extend, that is a
wrong answer). Claimed time: `n^{O(d)} · poly(m)`.

**2.1.2 Core lemma L1.** There is a constant `d` such that for every unsatisfiable CNF `φ`, either
degree-`d` SoS refutes `φ` (linear clause encoding) or degree-`d` PC over some GF(p), `p ≤ n`,
refutes `φ`. Then `sat_in_p` follows by implementing A1(d) as a `FinTM2`.

**2.1.3 Proof-complexity check: FAIL.** L1 is false. Take R3 with `Δ = 5.5` (UNSAT w.h.p. by the
first-moment bound). For these formulas, degree-Ω(n) SoS is required w.h.p. [Sch08] (random k-SAT,
`k ≥ 3`, any constant density), and degree-Ω(n) PC is required w.h.p. over every field ([AR03] for
characteristic 2, [BI99] for characteristic ≠ 2). So for any fixed `d` (indeed any `d = o(n)`) both
components fail on almost all such formulas and A1(d) answers SAT on an unsatisfiable input. This is a
proof-complexity kill and a wrong-answer kill at once. Secondary kills: Tseitin on expanders kills
(i) [Gri01] and every (ii) with `p ≠ 2` [BGIP01]; only `p = 2` handles it, which is why the kill family
must be R3 rather than Tseitin. PHP does not kill C1 at all (Appendix B), which is why PHP is not a
kill family here.

**2.1.4 Why there is no rescue.** Raising `d` to Θ(n) gives time `n^{Θ(n)}`. Replacing the static
degree-`d` relaxation by a dynamic bounded-degree system (LS^d, Positivstellensatz calculus; dag-like
size lower bounds are open [BPS07], and these systems do have short proofs of Tseitin, PHP and CC
[GHP02]) turns the problem into proof search in that system, which is a different candidate with no
known search procedure; what an algorithm can compute in polynomial time is the rank-`r` closure, and
rank is bounded by degree, so the same degree bounds apply. Adding definitional variables
`y = x_i x_j …` for all tuples up to size `k` is degree-`2k` static SoS in disguise. Adding arbitrary
circuit-defined extension variables (the IPS direction) has no lower bounds but also no algorithm.

**2.1.5 Barrier check: moot** (the lemma is false). For the record: the SoS and PC steps act on
explicit polynomial encodings of clauses, so a proof of L1 would have been non-relativizing; the SoS
positivity reasoning is semialgebraic rather than an evaluation of a low-degree extension, so
non-algebrizing. The PC-over-GF(p) component is the one closest to the arithmetization style, and it
is exactly the component killed by [Raz98, BGIP01, AR03, BI99].

**2.1.6 Dead-end screen: FAIL.** C1 is the LP/SDP-hierarchy class of §1.4(b) [CLRS16, KMR17, LRS15].

**2.1.7 Falsification plan** (pre-registered; not to be run, the candidate is dead on paper).
Implementation: `d ∈ {2, 4}`; SDP via an off-the-shelf solver with tolerance 10⁻⁸ (inexact; any
discrepancy with the exact answer is logged as such); GF(2) and GF(3) components by Gaussian
elimination over monomials of degree ≤ `d`. Families and sizes: F4 Tseitin on random 3-regular
graphs, `10 ≤ n ≤ 60` vertices; F1 random 3-SAT at ratio 4.26, UNSAT instances only (labelled by
CaDiCaL), `20 ≤ n ≤ 100`; F3 PHP, `n ≤ 10` (expected to pass; control). Kill criterion: K1 (any
wrong answer). Prediction: K1 fires on F4 at `n ≤ 30` and on F1 at `n ≤ 60` for `d = 4`.

**Verdict: KILLED** (proof-complexity check; wrong answers).

### 2.2 C2 — LP-based branch-and-cut with Gomory–Chvátal cuts

**2.2.1 Algorithm BC.** Encode `φ` as the 0/1 system `S(φ)`: for each clause `Σ_{ℓ∈C} ℓ ≥ 1`;
bounds `0 ≤ x_i ≤ 1`. Depth-first branch-and-cut. At each node (a set of fixed variables): solve the
LP relaxation with objective minimise `Σ_i x_i` (exact rational simplex, or HiGHS with a verified
Farkas certificate on infeasibility); if infeasible, close the node; if the optimum is integral, output
SAT with that assignment; otherwise perform up to `r = 10` rounds of Gomory fractional cuts (each a
Chvátal–Gomory cut read off the optimal tableau) and re-solve; if still fractional, branch on the most
fractional variable (`x_i ≤ 0` first, then `x_i ≥ 1`). Output UNSAT when the root is closed. Every
parameter is fixed. Claimed time: polynomial in `n + m` (number of nodes times a polynomial per node).

**2.2.2 Core lemma L2.** There is `c` such that for every CNF `φ` with `n` variables and `m`
clauses, BC(`φ`) expands at most `(n+m)^c` nodes. Correctness of BC is unconditional (it is a
complete method); only the bound is in question.

**2.2.3 Proof-complexity check: FAIL.** The run of BC on an unsatisfiable `φ` translates into a
cutting-planes refutation with polynomial blow-up **[derived here, Appendix A]**: an LP infeasibility
is a Farkas combination, i.e., a CP linear-combination step after scaling to integers; a Gomory cut is
a CP step; and branching on a variable is removed by the deduction lemma (Appendix A): if
`S ∪ {x ≤ 0}` has a CP refutation with `s` lines then `S ⊢_CP x ≥ 1` in `O(s)` lines with polynomial
bit-size, after which the refutation of the `x ≥ 1` branch applies. By induction on the tree, a run
with `N` nodes yields a CP refutation of size `O(N · r · poly)`. CP has superpolynomial lower bounds:
clique-colouring needs size `exp(n^{Ω(1)})` [Pud97] (and [BPR97] for small coefficients), random
Θ(log n)-CNF needs exponential size [FPPR17, HP17]. Hence L2 is false: BC expands superpolynomially
many nodes on CC. Variants: branching on general linear forms with bounded coefficients is Stabbing
Planes with bounded coefficients (SP*), which CP simulates with quasi-polynomial blow-up [FGIPRTW]
(the abstract states the bounded-coefficient case; I have not verified the exact blow-up in the body);
this still converts exponential CP lower bounds into superpolynomial ones. Split and MIR cuts are
covered the same way. Families that do **not** kill C2, and therefore are not kill families here: PHP
has polynomial CP proofs [CCT87]; Tseitin has quasi-polynomial CP proofs [DT20]; R3 is open for CP.

**2.2.4 Barrier check: moot** (lemma false). For the record, the non-relativizing and
non-algebrizing step would have been integrality (rounding), a discrete operation on explicit
inequalities.

**2.2.5 Dead-end screen: FAIL.** §1.4(b)–(c): the root LP is never infeasible for a CNF whose
clauses have at least two literals, so all the power is in cuts and branching, i.e., in CP; Woeginger
pattern 4.

**2.2.6 Falsification plan** (pre-registered; not to be run). Families: F5 clique-colouring with
`k = ⌈√n⌉`, `8 ≤ n ≤ 40`; F2' random k-CNF with `k = ⌈log₂ n⌉` at density just above the
first-moment threshold, `40 ≤ n ≤ 160`; F1 random 3-SAT at 4.26, `50 ≤ n ≤ 200`; control F3 PHP
(easy for CP; a scaling failure there would indict the search, not CP). Cost: number of LP solves.
Kill: K1; K3 of §2.3.8 on F5 or F2'. Prediction: K3 fires on F5 by `n = 30` and on F1 by `n = 150`.

**Verdict: KILLED** (proof-complexity check via Appendix A).

### 2.3 C3 — satisfaction-driven clause learning (SDCL, PR learning)

**2.3.1 Background.** For a CNF `F` and a clause `C`, let `α = ¬C` be the assignment falsifying `C`.
`C` is *propagation redundant* (PR) with respect to `F` if there is a witness assignment `ω`
satisfying `C` such that every clause of `F|ω` is implied by unit propagation from `F|α`
(`F|α ⊢₁ F|ω`) [HKB17]. Adding a PR clause preserves satisfiability but not equivalence. PR with the
witness restricted to `var(α)` is SPR [HKB17, BT21]. Checking "`C` is PR w.r.t. `F` with witness `ω`"
is polynomial (unit propagation). PR⁻ is the proof system whose lines are PR clauses over the original
variables, ending in the empty clause; DPR⁻ allows deletion. Known: SPR⁻ has polynomial-size proofs
of PHP, bit-PHP, the parity principle, Tseitin, CC, or-/xor-ification and index-lifted formulas
[BT21]; DPR⁻ = DRAT⁻ = DSPR⁻ = DBC⁻ [BT21]; PR proofs translate into DRAT with new variables [HB18]
and into ER [KRH18]; no superpolynomial lower bounds are known for PR⁻ or SPR⁻ (lower bounds are
known for RAT⁻ [BT21] and SBC⁻ [Yol24]). SDCL [HKSB17, HKB19] is CDCL that, before branching, tries
to prove the current branch prunable by solving a positive reduct; [HKB19] report automatically found
short PR proofs of PHP and, with the filtered reduct, of Tseitin formulas and mutilated chessboards,
and only modest effects on other benchmarks.

Positive reduct [HKSB17] **[restated and re-derived here]**: for a partial assignment `α` that
falsifies no clause of `F`,

    p(F, α) = { D ∩ lit(var α) : D ∈ F, α satisfies D } ∪ { ¬α }.

If `ω` (over `var α`) satisfies `p(F, α)`, then `¬α` is SPR w.r.t. `F` with witness `ω`: a clause `D`
satisfied by `α` is satisfied by `ω` (its restriction is in `p`), and a clause `D` not satisfied by
`α` has all its `var(α)`-literals falsified by `α`, so `D|ω ⊇ D|α` and `D|ω` is subsumed by a clause
of `F|α`. Filtered positive reduct (as I understand [HKB19]; the implementer must check this
definition against the paper and log any discrepancy in NOTES.md before experiments start): drop
from `p(F, α)` the clauses `D` whose untouched part `D \ lit(var α)` is already unit-implied by `F|α`,
because then `F|α ⊢₁ D|ω` holds regardless of `ω`. Both reducts are sound by the argument above.

**2.3.2 Algorithm SDCL\*.** All parameters fixed now.

* Base CDCL: two watched literals; VSIDS with decay 0.95 and phase saving; Luby restarts with unit
  100 conflicts; 1-UIP learning with clause minimisation; learned-clause database reduction every
  2,000 conflicts keeping clauses of LBD ≤ 2 and the most active half of the rest; **no
  preprocessing** (no bounded variable elimination, no bounded variable addition: the candidate must
  not be confounded with ER).
* SDCL step: whenever unit propagation is complete and consistent at decision level ≥ 1, immediately
  before the next decision, build the filtered positive reduct `f(F, α)` (primary) and solve it with
  an inner plain-CDCL call (same base configuration, no SDCL) limited to `R = 100` conflicts. If it is
  satisfiable with model `ω`: learn the clause `¬α` as a PR clause with witness `ω`, append `(¬α, ω)`
  to the proof log, backjump to the asserting level, continue. If unsatisfiable or the limit is hit:
  make the next decision.
* Ablations, fixed now: (i) the same code with the SDCL step disabled (plain CDCL, resolution-bounded);
  (ii) the original positive reduct instead of the filtered one.
* Output: SAT with the model, checked by an independent evaluator; UNSAT with the proof log, checked by
  a separate PR checker (unit propagation only), never by trusting the solver.

Claimed time: polynomial in `n + m`.

**2.3.3 Core lemma L3.** There is `c` such that for every CNF `φ` with `n` variables and `m` clauses,
SDCL\*(`φ`) terminates within `(n+m)^c` conflicts (outer plus inner). Correctness is unconditional
(CDCL completeness; PR clauses preserve satisfiability; UNSAT answers are PR-checked). L3 implies
`sat_in_p` via a `FinTM2` implementation of SDCL\*.

**2.3.4 Barrier check: incomplete by necessity.** The step that must carry the non-relativizing and
non-algebrizing content is L3 itself; no proof exists, so the check can only say what a proof would
have to look like. The syntactic ingredients are unit propagation and the redundancy check
`F|α ⊢₁ F|ω`; both read clauses literally and have no meaning for oracle gates or for a low-degree
extension, so a proof of L3 that used them essentially would be non-relativizing and non-algebrizing.
Conversely, any argument for L3 that uses `φ` only through satisfaction queries or through its
arithmetization is necessarily wrong (§1.2). Status: not failed, not completed.

**2.3.5 Proof-complexity check: PASS by default.** The UNSAT transcript is a DPR⁻ proof (every
learned clause is either a resolvent, hence RUP, or a PR clause with an explicit witness; deletions
are allowed). Weakest known simulating systems: DPR⁻ (= DRAT⁻ = DSPR⁻ = DBC⁻ [BT21]) ⊆ ER [HB18,
KRH18] ⊆ EF. No superpolynomial lower bounds are known for any of these. The known lower bounds for
RAT⁻ and SBC⁻ do not apply (the learned clauses are PR and deletion is used). On the kill families:
PHP, Tseitin, CC, bit-PHP and the parity principle all have polynomial SPR⁻ proofs [BT21]; R3 is open.
So the paper screen cannot kill C3. This is a statement about missing lower-bound technology, not
about C3's strength: the ER/EF frontier is where lower bounds have been open since [CR79].

Constraints that do apply. (1) The inner reduct solver is resolution-bounded (`R = 100` conflicts),
so each learned PR clause is one the solver can *find* cheaply; the PR proof system is strong, but the
search is a fixed polynomial-time heuristic with no guarantee. (2) By §1.3.4, L3 would make EF
automatizable, so SDCL\* must factor; F6 is compulsory. (3) The positive reduct of a random 3-CNF under
a partial assignment is itself a random-like CNF over `var(α)` plus the clause `¬α`; nothing known
suggests it is satisfiable for branches large enough to matter. I expect this to be where C3 fails,
but that is a prediction, not a proof.

**2.3.6 Dead-end screen: PASS.** Not resolution (the separations on PHP, Tseitin and CC are theorems
[BT21] and experiments [HKB19]); not an LP/SDP; not local search; no Woeginger pattern applies because
C3 claims nothing before the test, which is the point of Phase 4.

**2.3.7 Mandatory consequences:** must factor (F6), must refute R3 (F1, F2), must be polynomial on
every family (F7). Recorded; no mechanism is known for any of them.

**2.3.8 Pre-registered falsification plan for Phase 4** (fixed now; shared infrastructure in
Appendix C).

Families and sizes:

| Family | Generator | Sizes | Instances per size | Labels |
|---|---|---|---|---|
| F1 | random 3-SAT, `m/n = 4.26` | `n ∈ {50, 75, 100, 125, 150, 175, 200, 225, 250}` | 20 (seeds 0–19), plus the first 10 SATLIB `uf`/`uuf` files per size [SATLIB] | CaDiCaL |
| F2 | random 3-SAT, `m/n = 5.0` (UNSAT w.h.p.) | `n ∈ {100, 150, 200, 250, 300, 350, 400}` | 10 | CaDiCaL |
| F3 | `PHP_{n+1}^n` | `n ∈ {8, 10, 12, 14, 16, 20, 25, 30, 40}` | 1 | UNSAT |
| F4 | Tseitin, random 3-regular graph, odd total charge | `n ∈ {20, 40, 60, 80, 100, 150, 200, 300}` vertices | 10 | UNSAT |
| F5 | clique-colouring, `k = ⌈√n⌉` | `n ∈ {8, 10, 12, 16, 20, 25, 30}` | 1 | UNSAT |
| F6 | factoring: `N = p·q`, `p, q` b-bit (leading bit 1), array-multiplier Tseitin encoding | `b ∈ {6, 8, 10, 12, 14, 16, 18, 20}` | 5 SAT (`N` a semiprime with two b-bit prime factors) + 5 UNSAT (`N` a 2b-bit prime) | known |
| F7 | SAT Competition 2023 main track [SC23] | all instances with ≤ 3,000 variables and ≤ 30,000 clauses that CaDiCaL solves within 60 s; the list is written to NOTES.md before any run of SDCL\* | CaDiCaL |
| F8 | mutilated chessboard | side `6 ≤ s ≤ 16`, even | 1 | UNSAT |

Cost measure: `conflicts_outer + conflicts_inner + number of reduct checks` (deterministic for the
fixed configuration); wall-clock recorded as secondary; cap 1 hour per instance.

Kill criteria (any one kills):

* **K1.** Any wrong answer: UNSAT on an instance CaDiCaL labels SAT; SAT with a model that fails the
  independent evaluator; or a proof log rejected by the independent PR checker.
* **K2.** Home-turf exponential signature: on F3, F4, F5 (polynomial SPR⁻ proofs exist [BT21]) and
  F8 (short PR proofs found in [HKB19]), the local exponent
  `e_k = ln(T_{k+1}/T_k) / ln(n_{k+1}/n_k)` of the median cost exceeds 8 at two consecutive sizes,
  or the cap is hit at any size up to the second-largest listed. Interpretation: the search does not
  find the short proofs its own system has.
* **K3.** Scaling: for any family with at least 5 fully solved sizes, least-squares fits of `ln T` on
  `ln n` (polynomial model) and of `ln T` on `n` (exponential model; for F6 use `b`) over all fully
  solved sizes; kill if the exponential model has the smaller residual sum of squares and the
  polynomial model's fitted exponent exceeds 6.
* **K4.** No separation from resolution where resolution is exponential: on the UNSAT instances of F1
  at `n ∈ {200, 225, 250}`, the median cost of SDCL\* is at least 0.5 times the median cost of the
  plain-CDCL ablation.
* **K5.** Budget: more than 10% of the instances of any family at a size up to the second-largest
  listed hit the 1-hour cap.

These are proxies. "Polynomial time" is not finitely falsifiable, and a polynomial with astronomical
constants would fail them; they are fixed now so that nothing can be adjusted after seeing results.
Passing all of them would not be evidence for P = NP; it would be a reason to look for a proof of L3,
for which there is currently no idea.

Predictions, recorded now: F3 and F8 solved with `e_k ≤ 3` (consistent with [HKB19]); F4 solved by the
filtered variant with `e_k ≤ 4`; F5 uncertain (polynomial proofs exist [BT21], SDCL may not find
them); F1 and F2: K3 and K4 fire at `n ≤ 250`; F6: K3 fires by `b = 16`; F7: mixed, with the plain
ablation at least as fast on most instances.

**Verdict: SURVIVES the paper screen** (by absence of lower bounds); recommended for Phase 4.

**2.3.9 Alternates in the same escape hatch** (recorded for completeness; not separate candidates).
(a) ER-CDCL with the extension heuristic of [AKS10] or structured re-encoding [MHB12]: same paper
status (ER), weaker known behaviour (no reports of automatically found short PHP proofs). (b) CDCL
with linear-form splitting and linear-clause learning, i.e., dag-like Res(⊕): no dag-like lower
bounds, but tree-like [IS20] and regular [EGI24] fragments have exponential lower bounds, and proofs of
depth at most `N^{2−ε}` need size `exp(N^{Ω(1)})` [EI25], so a polynomial-time version must produce
deep, irregular proofs, which CDCL-style search does not naturally do; PHP in dag-like Res(⊕) is open,
Tseitin is easy, CC is open. Ranked below C3 for lack of upper bounds. (c) Gröbner bases with heuristic
extension variables: no implementation or analysis exists.

---

## 3. Kill log

| # | Candidate | Check | Result | Instance / theorem |
|---|---|---|---|---|
| 1 | C1 | Proof complexity, SoS component | FAIL | R3 (`Δ = 5.5`): degree Ω(n) required w.h.p. [Sch08]; Tseitin: [Gri01] |
| 2 | C1 | Proof complexity, PC components (all `p`) | FAIL | R3: degree Ω(n) over every field [AR03, BI99]; PHP: degree ≥ n/2+1 [Raz98]; Tseitin for `p ≠ 2`: [BGIP01] |
| 3 | C1 | Correctness | FAIL | A1(d) answers SAT on the formulas of rows 1–2 |
| 4 | C1 | Dead-end screen | FAIL | §1.4(b): [CLRS16, KMR17, LRS15] |
| 5 | C1 | Barrier | moot | lemma L1 is false |
| 6 | C2 | Proof complexity | FAIL | runs ⊆ CP with polynomial blow-up (Appendix A); CC: [Pud97]; random Θ(log n)-CNF: [FPPR17, HP17] |
| 7 | C2 | Dead-end screen | FAIL | §1.4(b)–(c); Woeginger pattern 4 |
| 8 | C2 | Barrier | moot | lemma L2 is false |
| 9 | C3 | Proof complexity | PASS (default) | DPR⁻ ⊆ ER: no lower bounds known [BT21, HB18, KRH18] |
| 10 | C3 | Dead-end screen | PASS | separations from resolution on PHP, Tseitin, CC [BT21, HKB19] |
| 11 | C3 | Barrier | incomplete | no proof of L3 exists; the syntactic step is named in §2.3.4 |
| 12 | C3 | Mandatory consequences | open | must factor (F6), must refute R3 (F1, F2); no mechanism known |

No candidate was rescued by weakening its claim: C1 and C2 are dead as stated, and C3's claim (L3) is
the full polynomial bound for a fully specified algorithm.

---

## 4. Ranking and recommendation

Only C3 survives. Recommendation: run Phase 4 on C3 exactly as specified in §2.3.2 and §2.3.8, with
the ablations, the independent checkers and the pre-written F7 instance list.

**Honest estimate.** Probability that C3 survives the Phase 4 plan: below 1 in 1000. Reasons, in
order of weight: (1) the field's prior that P ≠ NP, which this document's survey reinforces; (2)
conditional on P = NP, the chance that a fixed heuristic chosen for its performance on three crafted
families is a polynomial-time algorithm is small; (3) the specific mechanism of C3, pruning by
witnessed redundancy, exploits symmetry and counting structure that random formulas lack, and
[HKB19] report only modest effects outside the crafted families; (4) C3 must factor (§1.5), and
nothing in PR learning addresses multiplier circuits. The most likely kill is K3/K4 on F1 at
`n ≤ 250`; the second most likely is K3 on F6 by `b = 16`.

**What Phase 4 delivers even on failure.** A Python SDCL with an independent PR checker, a measured
scaling table per family (instance size against cost, with correctness), and a NOTES.md entry that
records the kill instance and criterion. Those are reusable for screening any later CDCL-type
candidate.

**If C3 is killed.** Return to Phase 3. The next candidate must land outside every system with known
lower bounds (§1.3.5) *and* come with a mechanism for R3 and for factoring; §5 explains why I do not
expect one. The alternative use of effort is the formal deliverable that already exists: run
lean4checker on the proved parts (a)–(c) and do the Phase 6 red-team, which are owed regardless.

---

## 5. Overall assessment and what the failures have in common

1. **Every killed candidate is bounded in a static measure** (degree, rank, cut rank, width), and the
   families that kill it are those whose unsatisfiability has no local witness: random 3-CNF (every
   small subformula is satisfiable, by expansion), Tseitin (locally satisfiable, globally parity-
   inconsistent), clique-colouring (hard by interpolation from monotone circuit lower bounds). Every
   polynomial method known works by exploiting a global structure (counting for PHP, linear algebra for
   Tseitin, the PHP substitution for CC); random instances have no such structure, and no proof system
   is known to have polynomial-size refutations of them.
2. **The survivors survive for a negative reason.** Lower-bound methods (restrictions, interpolation,
   lifting) stop at ER/EF, AC⁰[p]-Frege and PR⁻; no upper bound on R3 is known in any of these
   systems. A working C3 would be the first polynomial-size proof system for random 3-CNFs, found by a
   heuristic that was never designed with random formulas in mind.
3. **Automatizability closes the loop.** A working algorithm must find EF-strength proofs in
   polynomial time, hence factor integers (§1.3.4). No candidate, and no known technique, has a
   mechanism for that.

Taken together: the landscape is the one expected if P ≠ NP and NP ≠ coNP. I put the probability that
any of the three candidates, or any approach of the kinds screened in §1.4, yields `sat_in_p` at
essentially zero. The value of Phase 4 on C3 is a documented, measured negative result and reusable
tooling, not a realistic chance at the theorem. If the user prefers, Phase 4 can be skipped in favour
of lean4checker and the Phase 6 red-team of the proved parts; that would not change the status line.

**Single most promising next step (as asked):** Phase 4 on C3 per §2.3.8, expecting the kill at F1.

---

## Appendix A — Cutting planes simulates branching on a variable **[derived here]**

Cutting planes (CP) operates on integer linear inequalities `a·x ≥ b` over variables with axioms
`x_i ≥ 0` and `−x_i ≥ −1`. Rules: (R1) add two lines with nonnegative integer multipliers; (R2)
division: from `c·a·x ≥ b` with `c` dividing every coefficient of `a`, derive `a·x ≥ ⌈b/c⌉`. A
refutation ends in `0 ≥ 1`.

**Lemma A.1.** Let `S` be a set of inequalities over 0/1 variables. If `S ∪ {−x ≥ 0}` (i.e., `x ≤ 0`)
has a CP refutation `L_1, …, L_s`, then `S ⊢_CP x ≥ 1` with at most `2s + 1` lines, and the bit-size of
the new proof is polynomial in the bit-size of the old one.

*Proof.* Write each `L_i` as `a_i·x ≥ b_i` (the vector `a_i` may already contain a coefficient for
`x`). We construct lines `L'_i` of the form `a_i·x + M_i x ≥ b_i` with integers `M_i ≥ 0`, derivable
from `S`, by induction on `i`.

* `L_i` an axiom of `S` or a Boolean axiom: `L'_i := L_i`, `M_i = 0`.
* `L_i` the hypothesis `−x ≥ 0`: `L'_i := x ≥ 0` (a Boolean axiom), which is `−x + 2x ≥ 0`, so
  `M_i = 2`.
* `L_k = α L_i + β L_j` (R1): `L'_k := α L'_i + β L'_j`, `M_k = α M_i + β M_j`.
* `L_k` from `L_i` by division by `c` (R2): first add `(c − (M_i mod c)) mod c` copies of the axiom
  `x ≥ 0` to `L'_i` (one R1 step), obtaining `a_i·x + M'_i x ≥ b_i` with `c | M'_i`; since `c` divides
  every coefficient of `a_i`, R2 applies and gives `L'_k := (a_i/c)·x + (M'_i/c) x ≥ ⌈b_i/c⌉`,
  `M_k = M'_i/c`.

The last line `L_s = (0 ≥ 1)` becomes `L'_s = (M_s x ≥ 1)`. If `M_s = 0` we have refuted `S` directly
(then `x ≥ 1` follows trivially from `0 ≥ 1`). Otherwise R2 with `c = M_s` gives `x ≥ ⌈1/M_s⌉ = 1`.
Each original step became at most two steps. For the bit-size: `M_i` is at most twice the product of
the multipliers along any derivation path plus the padding, so its bit-length is bounded by the total
bit-length of the multipliers in the original proof plus `O(s log s)`; the padding multipliers are
bounded by the divisors `c`, which appear in the original proof. ∎

**Corollary A.2 (branch-and-cut is cutting planes).** A branch-and-cut run on `S(φ)` with `N` nodes,
each performing at most `r` rounds of Chvátal–Gomory cuts, LP infeasibility certified by Farkas
multipliers, and branching on single variables, translates into a CP refutation of `S(φ)` with
`O(N · (r + 1) · poly(n, m))` lines of polynomial bit-size.

*Proof.* Induction on the branch-and-cut tree. A leaf closed by LP infeasibility: the rational Farkas
multipliers, scaled to integers, give an R1 derivation of `0 ≥ k` with `k ≥ 1`, and R2 gives `0 ≥ 1`;
Gomory cuts generated at the node are R1+R2 steps from the node's inequalities. An internal node
branching on `x` with refuted children: apply Lemma A.1 to the `x ≤ 0` child to derive `x ≥ 1` from
the node's inequalities, then append the `x ≥ 1` child's refutation. A branch-and-cut run on an
unsatisfiable `φ` has no leaf with an integral LP solution, so every leaf is closed by infeasibility.
∎

Consequently every superpolynomial CP lower bound (clique-colouring [Pud97], random Θ(log n)-CNF
[FPPR17, HP17]) is a superpolynomial lower bound on the number of branch-and-cut nodes.

---

## Appendix B — PHP has a sum-of-squares refutation of degree 4 **[derived here]**

Variables `x_{ij}`, pigeon `i ∈ [n+1]`, hole `j ∈ [n]`. Axioms with the linear clause encoding:
`P_i : Σ_j x_{ij} − 1 ≥ 0`; `H_{ikj} : 1 − x_{ij} − x_{kj} ≥ 0` for `i < k`; Boolean
`x_{ij}² − x_{ij} = 0`. (With the product encoding of the hole clauses, `x_{ij} x_{kj} = 0` is an
axiom and Step 1 is unnecessary; the degree is then 2.)

*Step 1 (degree 4).* Multiply `H_{ikj}` by the square `x_{ij}²`: `x_{ij}²(1 − x_{ij} − x_{kj}) ≥ 0`.
Modulo the Boolean axioms (`x² ≡ x`, `x³ ≡ x`), the left side is `−x_{ij} x_{kj}`. So
`−x_{ij} x_{kj} ≥ 0` is a degree-4 SoS consequence. Also `x_{ij} x_{kj} = (x_{ij} x_{kj})² ≥ 0`
modulo Boolean axioms. Hence `x_{ij} x_{kj} = 0` in the SoS sense.

*Step 2 (degree ≤ 4).* For each hole `j` put `s_j = Σ_i x_{ij}`. The polynomial identity
`1 − s_j = (1 − s_j)² + (s_j − s_j²)` holds, and
`s_j − s_j² = Σ_i (x_{ij} − x_{ij}²) − 2 Σ_{i<k} x_{ij} x_{kj}`, whose first sum is a combination of
Boolean axioms and whose second sum is, by Step 1, a nonnegative combination of derived
inequalities. So `1 − s_j ≥ 0` has a degree-4 certificate.

*Step 3 (degree 1).* `Σ_j (1 − s_j) + Σ_i P_i = n − Σ_{ij} x_{ij} + Σ_{ij} x_{ij} − (n+1) = −1`, so
`−1 ≥ 0`: a degree-4 SoS refutation. ∎

Consequence for the plans: PHP cannot kill any SoS- or CP-based candidate (CP: [CCT87]); R3 and
Tseitin kill SoS, CC kills CP.

---

## Appendix C — Shared Phase 4 infrastructure (pre-registered)

* **Generators.** PHP, Tseitin (random 3-regular graphs, odd total charge), clique-colouring and
  random k-CNF from CNFgen [CNFgen] with the seeds listed in §2.3.8; factoring and mutilated
  chessboard from our own scripts (array multiplier with Tseitin encoding; standard chessboard
  encoding). All instances are written as DIMACS files; a manifest with SHA-256 hashes is written to
  NOTES.md before any candidate run.
* **Labels.** CaDiCaL via PySAT for every instance whose status is not known by construction. For F1
  the SATLIB files (`uf`/`uuf`, sizes 50–250) are used as a public fixed subset.
* **Independent checks.** A model evaluator (evaluates the CNF on the model, no solver code shared);
  a PR checker that re-verifies every learned PR clause by unit propagation from the witness, and
  every learned resolvent by RUP.
* **Cost.** As in §2.3.8; medians over the instances of a size; sizes with any cap hit are excluded
  from the fits but counted for K5.
* **Fits.** Ordinary least squares of `ln(median cost)` on `ln n` and on `n` (`b` for F6). The
  polynomial exponent is the slope of the first fit. Both residual sums of squares are reported.
* **No-change rule.** Any change to SDCL\* (parameters, reduct definition, inner limit, heuristics)
  after the first measured run is a new candidate requiring a new pre-registration in this file. The
  ablations are fixed in §2.3.2.
* **Reporting.** Per family: size, instances, correct answers, median cost, maximum cost, median
  wall-clock, cap hits; plus the fits and the kill criterion that fired, if any. Logged in NOTES.md
  with the instance that caused the kill.

---

## Appendix D — Random 3-CNFs have no XOR substructure and no useful symmetry w.h.p. **[derived here, sketch]**

*XOR constraints.* Solvers that extract XOR constraints syntactically need, for a 3-XOR, all four
clauses with a fixed parity pattern on the same variable triple. In a random 3-CNF with `m = Δn`
clauses the probability that a given clause lands on a given triple with a given sign pattern is
`1/(8·C(n,3))`; the expected number of triples carrying four clauses with the four required patterns
is at most `C(n,3) · C(m,4) · 4! · (1/(8·C(n,3)))⁴ = Θ(n⁴/n⁹) → 0`. So w.h.p. there is no XOR
constraint (and no two clauses on the same triple at all), and Gaussian elimination is vacuous.

*Symmetries.* A symmetry of the clause set is a signed permutation of the variables that maps the
clause set to itself. In a random 3-CNF at constant density the expected number of pairs of variables
that could be swapped by a non-identity symmetry acting only on low-degree variables is tiny in the
experimental range (two variables of degree 1 sharing their only clause with equal signs: expected
count about `m · (3 · P[deg = 1])² ≈ 5·10⁻⁶` at `n = 250`), and any such symmetry maps clauses to
clauses already present, so the symmetry rule derives nothing new. I do not claim the automorphism
group is trivial asymptotically; the theorem-level kill of symmetry methods is the exponential lower
bound for the local symmetry rule in [Urq99].

---

## References

* [ACO08] D. Achlioptas, A. Coja-Oghlan. Algorithmic barriers from phase transitions. FOCS 2008.
* [AFT11] A. Atserias, J. K. Fichte, M. Thurley. Clause-learning algorithms with many restarts and bounded-width resolution. JAIR 40:353–373, 2011.
* [AH19] A. Atserias, T. Hakoniemi. Size-degree trade-offs for sums-of-squares and Positivstellensatz proofs. CCC 2019 (LIPIcs 137, 24:1–24:20).
* [Ajt94] M. Ajtai. The complexity of the pigeonhole principle. Combinatorica 14(4):417–433, 1994 (FOCS 1988).
* [AKS10] G. Audemard, G. Katsirelos, L. Simon. A restriction of extended resolution for clause learning SAT solvers. AAAI 2010.
* [Ale04] M. Alekhnovich. Mutilated chessboard problem is exponentially hard for resolution. TCS 310(1–3):513–525, 2004.
* [AM20] A. Atserias, M. Müller. Automating resolution is NP-hard. JACM 67(5), 2020 (FOCS 2019).
* [AR03] M. Alekhnovich, A. Razborov. Lower bounds for polynomial calculus: non-binomial case. Proc. Steklov Inst. Math. 242:18–35, 2003 (FOCS 2001).
* [AR08] M. Alekhnovich, A. Razborov. Resolution is not automatizable unless W[P] is tractable. SIAM J. Comput. 38(4):1347–1363, 2008.
* [AU00] N. H. Arai, A. Urquhart. Local symmetries in propositional logic. TABLEAUX 2000.
* [AW09] S. Aaronson, A. Wigderson. Algebrization: a new barrier in complexity theory. ACM Trans. Comput. Theory 1(1), Art. 2, 2009 (STOC 2008).
* [BDGMP04] M. L. Bonet, C. Domingo, R. Gavaldà, A. Maciel, T. Pitassi. Non-automatizability of bounded-depth Frege proofs. Computational Complexity 13:47–68, 2004.
* [BFIKPPR18] P. Beame, N. Fleming, R. Impagliazzo, A. Kolokolova, D. Pankratov, T. Pitassi, R. Robere. Stabbing planes. ITCS 2018.
* [BGIP01] S. Buss, D. Grigoriev, R. Impagliazzo, T. Pitassi. Linear gaps between degrees for the polynomial calculus modulo distinct primes. JCSS 62(2):267–289, 2001.
* [BGS75] T. Baker, J. Gill, R. Solovay. Relativizations of the P =? NP question. SIAM J. Comput. 4(4):431–442, 1975.
* [BH22] G. Bresler, B. Huang. The algorithmic phase transition of random k-SAT for low degree polynomials. FOCS 2021.
* [BI99] E. Ben-Sasson, R. Impagliazzo. Random CNF's are hard for the polynomial calculus. FOCS 1999; Computational Complexity 19(4):501–519, 2010.
* [BIKPP96] P. Beame, R. Impagliazzo, J. Krajíček, T. Pitassi, P. Pudlák. Lower bounds on Hilbert's Nullstellensatz and propositional proofs. Proc. London Math. Soc. 73(3):1–26, 1996.
* [BIKS18] S. Buss, D. Itsykson, A. Knop, D. Sokolov. Reordering rule makes OBDD proof systems stronger. CCC 2018.
* [BKS04] P. Beame, H. Kautz, A. Sabharwal. Towards understanding and harnessing the potential of clause learning. JAIR 22:319–351, 2004.
* [BPR97] M. L. Bonet, T. Pitassi, R. Raz. Lower bounds for cutting planes proofs with small coefficients. JSL 62(3):708–728, 1997.
* [BPR00] M. L. Bonet, T. Pitassi, R. Raz. On interpolation and automatization for Frege systems. SIAM J. Comput. 29(6):1939–1967, 2000.
* [BPS07] P. Beame, T. Pitassi, N. Segerlind. Lower bounds for Lovász–Schrijver systems and beyond follow from multiparty communication complexity. SIAM J. Comput. 37(3):845–869, 2007.
* [BS02] E. Ben-Sasson. Hard examples for the bounded depth Frege proof system. Computational Complexity 11:109–136, 2002.
* [BT21] S. Buss, N. Thapen. DRAT and propagation redundancy proofs without new variables. Logical Methods in Computer Science 17(2), 2021 (SAT 2019).
* [Bus87] S. Buss. Polynomial size proofs of the propositional pigeonhole principle. JSL 52(4):916–927, 1987.
* [BW01] E. Ben-Sasson, A. Wigderson. Short proofs are narrow — resolution made simple. JACM 48(2):149–169, 2001.
* [CCT87] W. Cook, C. R. Coullard, G. Turán. On the complexity of cutting-plane proofs. Discrete Applied Mathematics 18(1):25–38, 1987.
* [CHH17] A. Coja-Oghlan, A. Haqshenas, S. Hetterich. Walksat stalls well below satisfiability. SIAM J. Discrete Math. 31(2):1160–1173, 2017.
* [CLRS16] S. O. Chan, J. R. Lee, P. Raghavendra, D. Steurer. Approximate constraint satisfaction requires large LP relaxations. JACM 63(4), 2016 (FOCS 2013).
* [CNFgen] M. Lauria, J. Elffers, J. Nordström, M. Vinyals. CNFgen: a generator of crafted benchmarks. SAT 2017.
* [CO10] A. Coja-Oghlan. A better algorithm for random k-SAT. SIAM J. Comput. 39(7):2823–2864, 2010.
* [Coo76] S. A. Cook. A short proof of the pigeon hole principle using extended resolution. SIGACT News 8(4):28–32, 1976.
* [CR79] S. A. Cook, R. A. Reckhow. The relative efficiency of propositional proof systems. JSL 44(1):36–50, 1979.
* [CS88] V. Chvátal, E. Szemerédi. Many hard examples for resolution. JACM 35(4):759–768, 1988.
* [DKMP09] J. Díaz, L. Kirousis, D. Mitsche, X. Pérez-Giménez. On the satisfiability threshold of formulas with three literals per clause. TCS 410(30–32):2920–2934, 2009.
* [dRGNPRS21] S. F. de Rezende, M. Göös, J. Nordström, T. Pitassi, R. Robere, D. Sokolov. Automating algebraic proof systems is NP-hard. STOC 2021.
* [DT20] D. Dadush, S. Tiwari. On the complexity of branching proofs. CCC 2020.
* [EGI24] K. Efremenko, M. Garlík, D. Itsykson. Lower bounds for regular resolution over parities. STOC 2024.
* [EI25] K. Efremenko, D. Itsykson. Amortized closure and its applications in lifting for resolution over parities. CCC 2025; extended version arXiv:2507.23008 (depth up to N^{2−ε}).
* [FGIPRTW] N. Fleming, M. Göös, R. Impagliazzo, T. Pitassi, R. Robere, L.-Y. Tan, A. Wigderson. On the power and limitations of branch and cut. CCC 2021; Theory of Computing 22, 2026.
* [FMPTW15] S. Fiorini, S. Massar, S. Pokutta, H. R. Tiwary, R. de Wolf. Exponential lower bounds for polytopes in combinatorial optimization. JACM 62(2), 2015 (STOC 2012).
* [FPPR17] N. Fleming, D. Pankratov, T. Pitassi, R. Robere. Random Θ(log n)-CNFs are hard for cutting planes. FOCS 2017 (JACM 69(3), 2022).
* [Gam21] D. Gamarnik. The overlap gap property: a topological barrier to optimizing over random structures. PNAS 118(41), 2021.
* [GHP02] D. Grigoriev, E. A. Hirsch, D. V. Pasechnik. Complexity of semi-algebraic proofs. STACS 2002; Moscow Math. J. 2(4):647–679, 2002.
* [GK18] M. Garlík, L. A. Kołodziejczyk. Some subsystems of constant-depth Frege with parity. ACM Trans. Comput. Logic 19(4), 2018.
* [GKMP20] M. Göös, S. Koroth, I. Mertz, T. Pitassi. Automating cutting planes is NP-hard. STOC 2020.
* [GM09] M. Grohe, D. Marx. On tree width, bramble size, and expansion. J. Combin. Theory Ser. B 99(1):218–228, 2009.
* [GP18] J. A. Grochow, T. Pitassi. Circuit complexity, proof complexity, and polynomial identity testing: the ideal proof system. JACM 65(6), 2018.
* [Gri98] D. Grigoriev. Tseitin's tautologies and lower bounds for Nullstellensatz proofs. FOCS 1998.
* [Gri01] D. Grigoriev. Linear lower bound on degree of Positivstellensatz calculus proofs for the parity. TCS 259(1–2):613–622, 2001.
* [GT24] S. Gryaznov, N. Talebanfard. Bounded-depth Frege lower bounds for random 3-CNFs via deterministic restrictions. arXiv:2403.02275, 2024.
* [Hak85] A. Haken. The intractability of resolution. TCS 39:297–308, 1985.
* [Hås21] J. Håstad. On small-depth Frege proofs for Tseitin for grids. JACM 68(1), 2021 (FOCS 2017).
* [Hås23] J. Håstad. On small-depth Frege proofs for PHP. FOCS 2023.
* [HB18] M. J. H. Heule, A. Biere. What a difference a variable makes. TACAS 2018.
* [Het16] S. Hetterich. Analysing survey propagation guided decimation on random formulas. ICALP 2016.
* [HKB17] M. J. H. Heule, B. Kiesl, A. Biere. Short proofs without new variables. CADE 2017 (journal version: Strong extension-free proof systems, J. Automated Reasoning 64, 2020).
* [HKB19] M. J. H. Heule, B. Kiesl, A. Biere. Encoding redundancy for satisfaction-driven clause learning. TACAS 2019.
* [HKSB17] M. J. H. Heule, B. Kiesl, M. Seidl, A. Biere. PRuning through satisfaction. HVC 2017.
* [HP17] P. Hrubeš, P. Pudlák. Random formulas, monotone circuits, and interpolation. FOCS 2017.
* [IKRS20] D. Itsykson, A. Knop, A. Romashchenko, D. Sokolov. On OBDD-based algorithms and proof systems that dynamically change the order of variables. JSL 85(2), 2020 (STACS 2017).
* [IPS99] R. Impagliazzo, P. Pudlák, J. Sgall. Lower bounds for the polynomial calculus and the Gröbner basis algorithm. Computational Complexity 8(2):127–144, 1999.
* [IS20] D. Itsykson, D. Sokolov. Resolution over linear equations modulo two. Annals of Pure and Applied Logic 171(1), 2020 (MFCS 2014).
* [KMR17] P. K. Kothari, R. Meka, P. Raghavendra. Approximating rectangles by juntas and weakly-exponential lower bounds for LP relaxations of CSPs. STOC 2017.
* [Ko82] K.-I. Ko. Some observations on the probabilistic algorithms and NP-hard problems. Information Processing Letters 14(1):39–43, 1982.
* [KP98] J. Krajíček, P. Pudlák. Some consequences of cryptographical conjectures for S¹₂ and EF. Information and Computation 140(1):82–94, 1998.
* [KPW95] J. Krajíček, P. Pudlák, A. Woods. An exponential lower bound to the size of bounded depth Frege proofs of the pigeonhole principle. Random Structures & Algorithms 7(1):15–39, 1995.
* [Kra97] J. Krajíček. Interpolation theorems, lower bounds for proof systems, and independence results for bounded arithmetic. JSL 62(2):457–486, 1997.
* [Kra08] J. Krajíček. An exponential lower bound for a constraint propagation proof system based on ordered binary decision diagrams. JSL 73(1):227–237, 2008.
* [KRH18] B. Kiesl, A. Rebola-Pardo, M. J. H. Heule. Extended resolution simulates DRAT. IJCAR 2018.
* [Lau03] M. Laurent. A comparison of the Sherali–Adams, Lovász–Schrijver, and Lasserre relaxations for 0–1 programming. Math. Oper. Res. 28(3):470–496, 2003.
* [LRS15] J. R. Lee, P. Raghavendra, D. Steurer. Lower bounds on the size of semidefinite programming relaxations. STOC 2015.
* [MHB12] N. Manthey, M. J. H. Heule, A. Biere. Automated reencoding of Boolean formulas. HVC 2012.
* [MN15] M. Mikša, J. Nordström. A generalized method for proving polynomial calculus degree lower bounds. CCC 2015.
* [MPZ02] M. Mézard, G. Parisi, R. Zecchina. Analytic and algorithmic solution of random satisfiability problems. Science 297:812–815, 2002.
* [MSL92] D. Mitchell, B. Selman, H. Levesque. Hard and easy distributions of SAT problems. AAAI 1992.
* [OD17] R. O'Donnell. SOS is not obviously automatizable, even approximately. ITCS 2017.
* [PBI93] T. Pitassi, P. Beame, R. Impagliazzo. Exponential lower bounds for the pigeonhole principle. Computational Complexity 3:97–140, 1993.
* [PD11] K. Pipatsrisawat, A. Darwiche. On the power of clause-learning SAT solvers as resolution engines. Artificial Intelligence 175(2):512–525, 2011.
* [PRST16] T. Pitassi, B. Rossman, R. A. Servedio, L.-Y. Tan. Poly-logarithmic Frege depth lower bounds via an expander switching lemma. STOC 2016.
* [PS10] T. Pitassi, R. Santhanam. Effectively polynomial simulations. ICS 2010.
* [Pud97] P. Pudlák. Lower bounds for resolution and cutting plane proofs and monotone computations. JSL 62(3):981–998, 1997.
* [Raz98] A. A. Razborov. Lower bounds for the polynomial calculus. Computational Complexity 7(4):291–324, 1998.
* [RHB22] J. E. Reeves, M. J. H. Heule, R. E. Bryant. Preprocessing of propagation redundant clauses. IJCAR 2022.
* [Rot17] T. Rothvoss. The matching polytope has exponential extension complexity. JACM 64(6), 2017 (STOC 2014).
* [RR97] A. A. Razborov, S. Rudich. Natural proofs. JCSS 55(1):24–35, 1997.
* [RW17] P. Raghavendra, B. Weitz. On the bit complexity of sum-of-squares proofs. ICALP 2017.
* [SATLIB] H. H. Hoos, T. Stützle. SATLIB: an online resource for research on SAT. SAT 2000. https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html
* [SC23] SAT Competition 2023, main track benchmarks. https://satcompetition.github.io/2023/ (Zenodo record 11426992).
* [Sch08] G. Schoenebeck. Linear level Lasserre lower bounds for certain k-CSPs. FOCS 2008.
* [Seg08] N. Segerlind. On the relative efficiency of resolution-like proofs and ordered binary decision diagram proofs. CCC 2008.
* [TSZ10] O. Tveretina, C. Sinz, H. Zantema. Ordered binary decision diagrams, pigeonhole formulas and beyond. J. Satisfiability, Boolean Modeling and Computation 7:35–58, 2010.
* [Urq87] A. Urquhart. Hard examples for resolution. JACM 34(1):209–219, 1987.
* [Urq99] A. Urquhart. The symmetry rule in propositional logic. Discrete Applied Mathematics 96–97:177–193, 1999.
* [Vin20] M. Vinyals. Hard examples for common variable decision heuristics. AAAI 2020.
* [Woe] G. J. Woeginger. The P-versus-NP page. https://www.win.tue.nl/~wscor/woeginger/P-versus-NP.htm (formerly ~gwoegi/P-versus-NP.htm).
* [Yan91] M. Yannakakis. Expressing combinatorial optimization problems by linear programs. JCSS 43(3):441–466, 1991.
* [Yol24] E. Yolcu. Lower bounds for set-blocked clauses proofs. arXiv:2401.11266, 2024.
