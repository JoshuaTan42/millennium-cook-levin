import Problems.PVersusNP.Millennium
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Linarith

/-!
# SAT and the Cook–Levin theorem

* **Part 1 (done here):** a concrete CNF-SAT language `SAT : Language (List Bool)`, its
  semantics, sanity checks, and `sat_in_np : InNondeterministicPolynomialTime … SAT` via an
  explicit `FinTM2` verifier.
* **Part 2:** NP-hardness, `cook_levin`: proved in Pkg.lean (it needs the reduction chain, which imports this file).

Encoding (see `NOTES.md`, "SAT: concrete definition"): a CNF is a list of *dense* clauses; a
clause is a list of slots `Option Bool` (`none` = variable absent, `some b` = literal `x_j = b`).
Bits are read in pairs: `00` end of clause, `01` absent, `10` positive, `11` negative.
-/

namespace PvsNP

open Millennium

namespace SATDef

/-- A clause as a dense row: slot `j` says how variable `x_j` occurs
(`none`: absent, `some true`: `x_j`, `some false`: `¬x_j`). -/
abbrev Clause := List (Option Bool)

/-- A CNF formula: the conjunction of its clauses. -/
abbrev CNF := List Clause

/-- `a` satisfies clause `c`: some slot `j` holds a literal `x_j = b` and `a[j] = b`.
Variables at indices `≥ a.length` are unassigned and satisfy no literal. -/
def clauseSat (c : Clause) (a : List Bool) : Prop :=
  ∃ (j : ℕ) (b : Bool), c[j]? = some (some b) ∧ a[j]? = some b

/-- `a` satisfies every clause of `φ`. -/
def cnfSat (φ : CNF) (a : List Bool) : Prop :=
  ∀ c ∈ φ, clauseSat c a

/-- Decoding with the current (reversed) unfinished clause as accumulator. A trailing unterminated
clause and a dangling odd bit are ignored, so decoding is total. -/
def decodeAux : List Bool → Clause → CNF
  | false :: false :: r, cur => cur.reverse :: decodeAux r []
  | false :: true :: r, cur => decodeAux r (none :: cur)
  | true :: s :: r, cur => decodeAux r (some (!s) :: cur)
  | _, _ => []

/-- Decode a bit string into a CNF formula. -/
def decodeCNF (w : List Bool) : CNF := decodeAux w []

/-- Two bits per slot: `none ↦ 01`, `some true ↦ 10`, `some false ↦ 11`. -/
def encodeSlot : Option Bool → List Bool
  | none => [false, true]
  | some b => [true, !b]

/-- A clause is its slots followed by the terminator `00`. -/
def encodeClause (c : Clause) : List Bool := c.flatMap encodeSlot ++ [false, false]

/-- Encode a CNF formula as a bit string. -/
def encodeCNF (φ : CNF) : List Bool := φ.flatMap encodeClause

theorem decodeAux_slots (c : Clause) (rest : List Bool) (cur : Clause) :
    decodeAux (c.flatMap encodeSlot ++ rest) cur = decodeAux rest (c.reverse ++ cur) := by
  induction c generalizing cur with
  | nil => rfl
  | cons x c ih =>
      cases x with
      | none => simp [encodeSlot, decodeAux, ih]
      | some b => simp [encodeSlot, decodeAux, ih]

/-- Sanity: every CNF is represented, and decodes back to itself. -/
theorem decodeCNF_encodeCNF (φ : CNF) : decodeCNF (encodeCNF φ) = φ := by
  unfold decodeCNF encodeCNF
  induction φ with
  | nil => rfl
  | cons c φ ih =>
      rw [List.flatMap_cons, encodeClause, List.append_assoc, decodeAux_slots]
      simp [decodeAux, ih]

end SATDef

open SATDef

/-- **CNF-SAT** over binary strings: the decoded formula has a satisfying assignment. -/
def SAT : Language (List Bool) := fun w => ∃ a : List Bool, cnfSat (decodeCNF w) a

namespace SATDef

/-! ### Sanity checks: the language is neither trivial nor empty -/

/-- `00` is the single empty clause. -/
example : decodeCNF [false, false] = [[]] := rfl

/-- `10 00 11 00` is `x₀ ∧ ¬x₀`. -/
example : decodeCNF [true, false, false, false, true, true, false, false] =
    [[some true], [some false]] := rfl

/-- The empty clause is unsatisfiable. -/
example : ¬ SAT [false, false] := by
  rintro ⟨a, h⟩
  obtain ⟨j, b, hj, -⟩ := h [] (by simp [decodeCNF, decodeAux])
  simp at hj

/-- `x₀ ∧ ¬x₀` is unsatisfiable. -/
example : ¬ SAT [true, false, false, false, true, true, false, false] := by
  rintro ⟨a, h⟩
  obtain ⟨j₁, b₁, hj₁, ha₁⟩ := h [some true] (by simp [decodeCNF, decodeAux])
  obtain ⟨j₂, b₂, hj₂, ha₂⟩ := h [some false] (by simp [decodeCNF, decodeAux])
  rcases j₁ with _ | j₁ <;> rcases j₂ with _ | j₂ <;> simp at hj₁ hj₂
  subst hj₁ hj₂
  rw [ha₁] at ha₂
  simp at ha₂

/-- `x₀ ∧ (¬x₀ ∨ x₁)` (`10 00 11 10 00`) is satisfiable, by `[true, true]`. -/
example : SAT [true, false, false, false, true, true, true, false, false, false] := by
  refine ⟨[true, true], ?_⟩
  intro c hc
  simp only [decodeCNF, decodeAux, Bool.not_false, Bool.not_true, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl
  · exact ⟨0, true, rfl, rfl⟩
  · exact ⟨1, true, rfl, rfl⟩

/-! ### The verifier's scan, and its correctness -/

/-- One left-to-right pass over the formula bits, mirroring the verifier machine exactly:
`bs` = assignment bits not yet used by the current clause, `as` = those used (reversed),
`fl` = current clause already satisfied. -/
def evalCNF : List Bool → List Bool → List Bool → Bool → Bool
  | false :: false :: r, bs, as, fl => fl && evalCNF r (as.reverse ++ bs) [] false
  | false :: true :: r, [], as, fl => evalCNF r [] as fl
  | false :: true :: r, x :: bs, as, fl => evalCNF r bs (x :: as) fl
  | true :: _ :: r, [], as, fl => evalCNF r [] as fl
  | true :: s :: r, x :: bs, as, fl => evalCNF r bs (x :: as) (fl || x == !s)
  | _, _, _, _ => true

/-- The same scan with an explicit position `j` in the current clause. -/
def evalIdx : List Bool → List Bool → ℕ → Bool → Bool
  | false :: false :: r, a, _, fl => fl && evalIdx r a 0 false
  | false :: true :: r, a, j, fl => evalIdx r a (j + 1) fl
  | true :: s :: r, a, j, fl => evalIdx r a (j + 1) (fl || a[j]? == some (!s))
  | _, _, _, _ => true

theorem evalCNF_eq_evalIdx (r a : List Bool) (j : ℕ) (fl : Bool) :
    evalCNF r (a.drop j) (a.take j).reverse fl = evalIdx r a j fl := by
  induction r, a, j, fl using evalIdx.induct with
  | case1 r a j fl ih =>
      simp [evalCNF, evalIdx, ← ih]
  | case2 r a j fl ih =>
      rw [evalIdx, ← ih]
      rcases h : a[j]? with _ | x
      · rw [List.getElem?_eq_none_iff] at h
        rw [List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (by omega),
          List.take_of_length_le h, List.take_of_length_le (by omega), evalCNF]
      · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 h
        have ht : (a.take (j + 1)).reverse = a[j] :: (a.take j).reverse := by
          rw [List.take_add_one, h]; simp
        rw [List.drop_eq_getElem_cons hj, evalCNF, ht]
  | case3 s r a j fl ih =>
      rw [evalIdx, ← ih]
      rcases h : a[j]? with _ | x
      · rw [List.getElem?_eq_none_iff] at h
        rw [List.drop_eq_nil_of_le h, List.drop_eq_nil_of_le (by omega),
          List.take_of_length_le h, List.take_of_length_le (by omega), evalCNF]
        simp
      · obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.1 h
        have ht : (a.take (j + 1)).reverse = a[j] :: (a.take j).reverse := by
          rw [List.take_add_one, h]; simp
        rw [List.drop_eq_getElem_cons hj, evalCNF, ht]
        simp
  | case4 r a j fl h1 h2 h3 =>
      rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [evalCNF, evalIdx]

theorem clauseSat_nil (a : List Bool) : ¬ clauseSat [] a := by
  rintro ⟨j, b, h, -⟩; simp at h

theorem clauseSat_append_none (c : Clause) (a : List Bool) :
    clauseSat (c ++ [none]) a ↔ clauseSat c a := by
  constructor
  · rintro ⟨j, b, hj, ha⟩
    refine ⟨j, b, ?_, ha⟩
    rw [List.getElem?_append] at hj
    split_ifs at hj with h
    · exact hj
    · rcases hk : j - c.length with _ | k <;> simp [hk] at hj
  · rintro ⟨j, b, hj, ha⟩
    refine ⟨j, b, ?_, ha⟩
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1, hj]

theorem clauseSat_append_some (c : Clause) (a : List Bool) (b : Bool) :
    clauseSat (c ++ [some b]) a ↔ clauseSat c a ∨ a[c.length]? = some b := by
  constructor
  · rintro ⟨j, b', hj, ha⟩
    rw [List.getElem?_append] at hj
    split_ifs at hj with h
    · exact Or.inl ⟨j, b', hj, ha⟩
    · rcases hk : j - c.length with _ | k <;> simp [hk] at hj
      subst hj
      right
      rwa [show j = c.length by omega] at ha
  · rintro (⟨j, b', hj, ha⟩ | h)
    · refine ⟨j, b', ?_, ha⟩
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hj).1, hj]
    · exact ⟨c.length, b, by simp, h⟩

theorem evalIdx_iff (r : List Bool) (cur : Clause) (a : List Bool) (fl : Bool)
    (hfl : fl = true ↔ clauseSat cur.reverse a) :
    evalIdx r a cur.length fl = true ↔ cnfSat (decodeAux r cur) a := by
  induction r, cur using decodeAux.induct generalizing fl with
  | case1 r cur ih =>
      have := ih false (by simp [clauseSat_nil])
      simp only [evalIdx, decodeAux, Bool.and_eq_true, cnfSat, List.mem_cons,
        forall_eq_or_imp] at this ⊢
      rw [List.length_nil] at this
      rw [this, hfl]
  | case2 r cur ih =>
      rw [evalIdx, decodeAux, ← ih fl (by rw [hfl, List.reverse_cons, clauseSat_append_none])]
      rfl
  | case3 s r cur ih =>
      rw [evalIdx, decodeAux]
      refine (Eq.to_iff rfl).trans (ih _ ?_)
      rw [List.reverse_cons, clauseSat_append_some, List.length_reverse, Bool.or_eq_true, hfl,
        beq_iff_eq]
  | case4 r cur h1 h2 h3 =>
      have hd : decodeAux r cur = [] := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [decodeAux]
      have he : evalIdx r a cur.length fl = true := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [evalIdx]
      simp [hd, he, cnfSat]

/-- The checking relation. -/
def check (w y : List Bool) : Bool := evalCNF w y [] false

theorem check_iff (w y : List Bool) : check w y = true ↔ cnfSat (decodeCNF w) y := by
  have h := evalCNF_eq_evalIdx w y 0 false
  simp only [List.drop_zero, List.take_zero, List.reverse_nil] at h
  rw [check, h]
  exact evalIdx_iff w [] y false (by simp [clauseSat_nil])

/-- Every decoded clause is no wider than the input. -/
theorem length_le_of_mem_decodeAux (r : List Bool) (cur : Clause) :
    ∀ c ∈ decodeAux r cur, c.length ≤ cur.length + r.length := by
  induction r, cur using decodeAux.induct with
  | case1 r cur ih =>
      intro c hc
      simp only [decodeAux, List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp
      · have := ih c hc; simp at this ⊢; omega
  | case2 r cur ih =>
      intro c hc; have := ih c hc; simp at this ⊢; omega
  | case3 s r cur ih =>
      intro c hc; have := ih c hc; simp at this ⊢; omega
  | case4 r cur h1 h2 h3 =>
      have hd : decodeAux r cur = [] := by
        rcases r with _ | ⟨_ | _, _ | ⟨_ | _, r⟩⟩ <;> simp_all [decodeAux]
      simp [hd]

/-- Truncating a satisfying assignment to the input length keeps it satisfying. -/
theorem cnfSat_take (w a : List Bool) (h : cnfSat (decodeCNF w) a) :
    cnfSat (decodeCNF w) (a.take w.length) := by
  intro c hc
  obtain ⟨j, b, hj, ha⟩ := h c hc
  have hlen := length_le_of_mem_decodeAux w [] c hc
  have hjc := (List.getElem?_eq_some_iff.1 hj).1
  refine ⟨j, b, hj, ?_⟩
  rw [List.getElem?_take_of_lt (by simp at hlen; omega), ha]

/-- `SAT` is exactly "there is a short certificate accepted by `check`". -/
theorem sat_iff_check (w : List Bool) :
    SAT w ↔ ∃ y : List Bool, y.length ≤ w.length ^ 1 ∧ check w y = true := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a.take w.length, by simp, (check_iff _ _).2 (cnfSat_take w a ha)⟩
  · rintro ⟨y, -, hy⟩
    exact ⟨y, (check_iff _ _).1 hy⟩

end SATDef

/-! ## The verifier machine -/

namespace Verifier

open Turing Function

/-- Work stacks: the input stack, a stash for the formula, and two stacks for the assignment. -/
inductive W | inp | F | A | B
  deriving DecidableEq, Fintype

/-- Work alphabet = the pair alphabet `Bool ⊕ Option Bool` (`inr none` is the separator `#`).
Formula and assignment bits are stored as `inl b`. -/
abbrev G := Bool ⊕ Option Bool

/-- Stack alphabets: `none` is the output stack (alphabet `Bool`), `some w` a work stack. -/
@[reducible] def Γ : Option W → Type
  | none => Bool
  | some _ => G

/-- Labels. `c0 fl`/`c1 fl b` read the two bits of a token (`fl`: current clause satisfied),
`adv fl o` moves one assignment bit `B → A` (`o = some s`: literal token `1s`), `restore fl`
moves the used assignment bits back `A → B`. -/
inductive Lab
  | read1 | read2 | back1 | back2
  | c0 (fl : Bool) | c1 (fl b : Bool) | adv (fl : Bool) (o : Option Bool) | restore (fl : Bool)
  | drainI (ans : Bool) | drainA (ans : Bool) | drainB (ans : Bool) | finish (ans : Bool)
  deriving DecidableEq, Fintype

/-- Machine state: the last popped symbol. -/
abbrev St := Option G

abbrev Stmt := TM2.Stmt Γ Lab St
abbrev Cfg := TM2.Cfg Γ Lab St

/-- Generic loop: pop `s`; while the popped symbol `x` has `g x = some y`, push `y` onto `t`
(nothing if `t = none`) and repeat; otherwise go to `next`. -/
def loop (s : W) (g : G → Option G) (t : Option W) (self next : Lab) : Stmt :=
  .pop (some s) (fun _ o => o) <|
    .branch (fun v => (v.bind g).isSome)
      (match t with
        | some t => .push (some t) (fun v => (v.bind g).getD (.inl false)) (.goto fun _ => self)
        | none => .goto fun _ => self)
      (.goto fun _ => next)

/-- Left symbols pass (and stop at `#`). -/
def gRead1 : G → Option G
  | .inl b => some (.inl b)
  | .inr _ => none

/-- Right symbols `inr (some b)` pass as `inl b`. -/
def gRead2 : G → Option G
  | .inr (some b) => some (.inl b)
  | _ => none

/-- The program. -/
def prog : Lab → Stmt
  | .read1 => loop .inp gRead1 (some .F) .read1 .read2
  | .read2 => loop .inp gRead2 (some .A) .read2 .back1
  | .back1 => loop .F some (some .inp) .back1 .back2
  | .back2 => loop .A some (some .B) .back2 (.c0 false)
  | .c0 fl => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl b) => .c1 fl b
      | _ => .drainI true
  | .c1 fl false => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl false) => .restore fl
      | some (.inl true) => .adv fl none
      | _ => .drainI true
  | .c1 fl true => .pop (some .inp) (fun _ o => o) <| .goto fun v => match v with
      | some (.inl s) => .adv fl (some s)
      | _ => .drainI true
  | .adv fl o => .pop (some .B) (fun _ o => o) <|
      .branch (fun v => v.isSome)
        (.push (some .A) (fun v => v.getD (.inl false)) <|
          .goto fun v => .c0 (fl || decide (v = o.map fun s => .inl (!s))))
        (.goto fun _ => .c0 fl)
  | .restore fl => loop .A some (some .B) (.restore fl) (if fl then .c0 false else .drainI false)
  | .drainI ans => loop .inp some none (.drainI ans) (.drainA ans)
  | .drainA ans => loop .A some none (.drainA ans) (.drainB ans)
  | .drainB ans => loop .B some none (.drainB ans) (.finish ans)
  | .finish ans => .push none (fun _ => ans) <| .load (fun _ => none) .halt

/-- The verifier as a `FinTM2`. Input stack `some inp`, output stack `none`. -/
def tm : FinTM2 where
  K := Option W
  k₀ := some .inp
  k₁ := none
  Γ := Γ
  Λ := Lab
  main := .read1
  σ := St
  initialState := none
  Γk₀Fin := (inferInstance : Fintype G)
  m := prog

/-! ### Configurations -/

/-- Assemble all stacks from the (non-dependent) work stacks `V` and the output `o`. -/
def stk (V : W → List G) (o : List Bool) : ∀ k, List (Γ k)
  | none => o
  | some w => V w

theorem update_stk_some (V : W → List G) (o : List Bool) (w : W) (l : List G) :
    update (stk V o) (some w) l = stk (update V w l) o := by
  funext k
  rcases k with _ | k
  · rw [update_of_ne (by simp)]; rfl
  · by_cases h : k = w
    · subst h; simp [stk]
    · rw [update_of_ne (by simpa using h)]
      simp [stk, update_of_ne h]

theorem update_stk_none (V : W → List G) (o l : List Bool) :
    update (stk V o) none l = stk V l := by
  funext k
  rcases k with _ | k
  · simp [stk]
  · rw [update_of_ne (by simp)]; rfl

/-- Work stacks from four lists. -/
def mkV (i f a b : List G) : W → List G
  | .inp => i
  | .F => f
  | .A => a
  | .B => b

@[simp] theorem update_mkV_inp (i f a b x : List G) :
    update (mkV i f a b) .inp x = mkV x f a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_F (i f a b x : List G) :
    update (mkV i f a b) .F x = mkV i x a b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_A (i f a b x : List G) :
    update (mkV i f a b) .A x = mkV i f x b := by
  funext k; cases k <;> rfl
@[simp] theorem update_mkV_B (i f a b x : List G) :
    update (mkV i f a b) .B x = mkV i f a x := by
  funext k; cases k <;> rfl

/-- `n` steps of the machine lead from `c` to `d`. -/
def Run (n : ℕ) (c d : Cfg) : Prop :=
  (flip bind (TM2.step prog))^[n] (some c) = some d

theorem Run.zero (c : Cfg) : Run 0 c c := rfl

theorem Run.head {n : ℕ} {c d e : Cfg} (h₁ : TM2.step prog c = some d) (h₂ : Run n d e) :
    Run (n + 1) c e := by
  unfold Run
  rw [iterate_succ_apply]
  exact (congrArg _ h₁).trans h₂

theorem Run.trans {n m : ℕ} {c d e : Cfg} (h₁ : Run n c d) (h₂ : Run m d e) :
    Run (n + m) c e := by
  unfold Run at *
  rw [add_comm, iterate_add_apply, h₁, h₂]

theorem Run.of_eq {n m : ℕ} {c d : Cfg} (h : Run n c d) (hn : n = m) : Run m c d := hn ▸ h

/-- Result of pushing `ys` one at a time onto `t` (nothing if `t = none`). -/
def pushAll : Option W → List G → (W → List G) → W → List G
  | none, _, V => V
  | some t, ys, V => update V t (ys.reverse ++ V t)

/-- The generic loop runs `|xs| + 1` steps, consuming `xs` and the stopping symbol. -/
theorem loop_run (s : W) (g : G → Option G) (t : Option W) (self next : Lab)
    (hp : prog self = loop s g t self next) (hst : t ≠ some s) (o : List Bool) :
    ∀ (xs ys rest : List G) (v : St) (V : W → List G),
      xs.map g = ys.map some → rest.head?.bind g = none → V s = xs ++ rest →
      Run (xs.length + 1) ⟨some self, v, stk V o⟩
        ⟨some next, rest.head?, stk (pushAll t ys (update V s rest.tail)) o⟩ := by
  intro xs
  induction xs with
  | nil =>
      intro ys rest v V hg hr hV
      obtain rfl : ys = [] := by simpa using hg.symm
      refine Run.head ?_ (Run.zero _)
      simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
        List.nil_append, hr, Option.isSome_none, cond_false]
      rw [update_stk_some]
      rcases t with _ | t
      · rfl
      · simp [pushAll]
  | cons x xs ih =>
      intro ys rest v V hg hr hV
      rcases ys with _ | ⟨y, ys⟩
      · simp at hg
      simp only [List.map_cons, List.cons.injEq] at hg
      obtain ⟨hxy, hg⟩ := hg
      rcases t with _ | t
      · have key := ih ys rest (some x) (update V s (xs ++ rest)) hg hr (by simp)
        simp only [pushAll, update_idem] at key ⊢
        refine Run.head ?_ key
        simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
          List.cons_append, List.head?_cons, List.tail_cons, Option.bind_some, hxy,
          Option.isSome_some, cond_true]
        rw [update_stk_some]
      · have hts : t ≠ s := fun h => hst (by rw [h])
        have key := ih ys rest (some x) (update (update V s (xs ++ rest)) t (y :: V t)) hg hr
          (by rw [update_of_ne (Ne.symm hts)]; simp)
        have hfin : pushAll (some t) ys
              (update (update (update V s (xs ++ rest)) t (y :: V t)) s rest.tail) =
            pushAll (some t) (y :: ys) (update V s rest.tail) := by
          funext k
          simp only [pushAll]
          by_cases hk : k = t
          · subst hk; simp [update_of_ne hts]
          · by_cases hk' : k = s
            · subst hk'; simp [update_of_ne hk]
            · simp [update_of_ne hk, update_of_ne hk']
        rw [hfin] at key
        refine Run.head ?_ key
        simp only [TM2.step, hp, loop, TM2.stepAux, show stk V o (some s) = V s from rfl, hV,
          List.cons_append, List.head?_cons, List.tail_cons, Option.bind_some, hxy,
          Option.isSome_some, cond_true, Option.getD_some]
        rw [update_stk_some, show stk (update V s (xs ++ rest)) o (some t) =
          update V s (xs ++ rest) t from rfl, update_stk_some, update_of_ne hts]

/-! ### Cleanup and output -/

/-- Draining `inp`, `A`, `B` and reaching `finish ans`. -/
theorem drain_run (ans : Bool) (i a b : List G) (v : St) :
    Run (i.length + a.length + b.length + 3) ⟨some (.drainI ans), v, stk (mkV i [] a b) []⟩
      ⟨some (.finish ans), none, stk (mkV [] [] [] []) []⟩ := by
  have h₁ := loop_run .inp some none (.drainI ans) (.drainA ans) rfl (by simp) [] i i [] v
    (mkV i [] a b) rfl rfl (by simp [mkV])
  have h₂ := loop_run .A some none (.drainA ans) (.drainB ans) rfl (by simp) [] a a [] none
    (mkV [] [] a b) rfl rfl (by simp [mkV])
  have h₃ := loop_run .B some none (.drainB ans) (.finish ans) rfl (by simp) [] b b [] none
    (mkV [] [] [] b) rfl rfl (by simp [mkV])
  simp only [pushAll, List.tail_nil, List.head?_nil, update_mkV_inp, update_mkV_A,
    update_mkV_B] at h₁ h₂ h₃
  exact (h₁.trans (h₂.trans h₃)).of_eq (by omega)

theorem finish_run (ans : Bool) :
    Run 1 ⟨some (.finish ans), none, stk (mkV [] [] [] []) []⟩
      ⟨none, none, stk (mkV [] [] [] []) [ans]⟩ := by
  refine Run.head ?_ (Run.zero _)
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_none]
  rfl

/-! ### The main scan -/

/-- Bits stored on a work stack. -/
def enc (l : List Bool) : List G := l.map Sum.inl

@[simp] theorem enc_nil : enc [] = [] := rfl
@[simp] theorem enc_cons (b : Bool) (l : List Bool) : enc (b :: l) = .inl b :: enc l := rfl
@[simp] theorem length_enc (l : List Bool) : (enc l).length = l.length := List.length_map _

theorem step_c0_nil (fl : Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c0 fl), v, stk (mkV [] [] a b) []⟩ =
      some ⟨some (.drainI true), none, stk (mkV [] [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c0_cons (fl x : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c0 fl), v, stk (mkV (enc (x :: r)) [] a b) []⟩ =
      some ⟨some (.c1 fl x), some (.inl x), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_nil (fl x : Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl x), v, stk (mkV [] [] a b) []⟩ =
      some ⟨some (.drainI true), none, stk (mkV [] [] a b) []⟩ := by
  cases x <;>
  · simp only [TM2.step, prog, TM2.stepAux]
    rw [update_stk_some]
    simp [stk, mkV]

theorem step_c1_ff (fl : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl false), v, stk (mkV (enc (false :: r)) [] a b) []⟩ =
      some ⟨some (.restore fl), some (.inl false), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_ft (fl : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl false), v, stk (mkV (enc (true :: r)) [] a b) []⟩ =
      some ⟨some (.adv fl none), some (.inl true), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_c1_t (fl s : Bool) (r : List Bool) (a b : List G) (v : St) :
    TM2.step prog ⟨some (.c1 fl true), v, stk (mkV (enc (s :: r)) [] a b) []⟩ =
      some ⟨some (.adv fl (some s)), some (.inl s), stk (mkV (enc r) [] a b) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_adv_nil (fl : Bool) (o : Option Bool) (i a : List G) (v : St) :
    TM2.step prog ⟨some (.adv fl o), v, stk (mkV i [] a []) []⟩ =
      some ⟨some (.c0 fl), none, stk (mkV i [] a []) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  rw [update_stk_some]
  simp [stk, mkV]

theorem step_adv_cons (fl : Bool) (o : Option Bool) (x : Bool) (i a : List G) (bs : List Bool)
    (v : St) :
    TM2.step prog ⟨some (.adv fl o), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 (fl || decide (some (Sum.inl x : G) = o.map fun s => .inl (!s)))),
        some (.inl x), stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  simp only [TM2.step, prog, TM2.stepAux]
  simp [stk, mkV, update_stk_some]

theorem step_adv_none_cons (fl x : Bool) (i a : List G) (bs : List Bool) (v : St) :
    TM2.step prog ⟨some (.adv fl none), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 fl), some (.inl x), stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  rw [step_adv_cons]; simp

theorem step_adv_some_cons (fl s x : Bool) (i a : List G) (bs : List Bool) (v : St) :
    TM2.step prog ⟨some (.adv fl (some s)), v, stk (mkV i [] a (enc (x :: bs))) []⟩ =
      some ⟨some (.c0 (fl || x == !s)), some (.inl x), stk (mkV i [] (.inl x :: a) (enc bs)) []⟩ := by
  rw [step_adv_cons]; cases x <;> cases s <;> simp

/-- Number of steps of the main scan (mirrors `evalCNF`). -/
def T : List Bool → List Bool → List Bool → Bool → ℕ
  | false :: false :: r, bs, as, fl =>
      as.length + 3 +
        if fl then T r (as.reverse ++ bs) [] false else r.length + (as.length + bs.length) + 3
  | false :: true :: r, [], as, fl => 3 + T r [] as fl
  | false :: true :: r, x :: bs, as, fl => 3 + T r bs (x :: as) fl
  | true :: _ :: r, [], as, fl => 3 + T r [] as fl
  | true :: s :: r, x :: bs, as, fl => 3 + T r bs (x :: as) (fl || x == !s)
  | r, bs, as, _ => r.length + as.length + bs.length + 4

theorem T_nil (bs as : List Bool) (fl : Bool) : T [] bs as fl = 0 + as.length + bs.length + 4 :=
  rfl

theorem T_single (b : Bool) (bs as : List Bool) (fl : Bool) :
    T [b] bs as fl = 1 + as.length + bs.length + 4 := by
  cases b <;> rfl

theorem enc_reverse_append (as bs : List Bool) :
    (enc as).reverse ++ enc bs = enc (as.reverse ++ bs) := by
  simp [enc]

/-- The main scan computes `evalCNF` and ends, all work stacks empty, at `finish`. -/
theorem scan (r bs as : List Bool) (fl : Bool) (v : St) :
    Run (T r bs as fl) ⟨some (.c0 fl), v, stk (mkV (enc r) [] (enc as) (enc bs)) []⟩
      ⟨some (.finish (evalCNF r bs as fl)), none, stk (mkV [] [] [] []) []⟩ := by
  induction r, bs, as, fl using evalCNF.induct generalizing v with
  | case1 r bs as fl ih =>
      have hR := loop_run .A some (some .B) (.restore fl)
        (if fl then .c0 false else .drainI false) rfl (by simp) [] (enc as) (enc as) []
        (some (.inl false)) (mkV (enc r) [] (enc as) (enc bs)) rfl rfl (by simp [mkV])
      simp only [pushAll, List.tail_nil, List.head?_nil, update_mkV_A, mkV, update_mkV_B,
        enc_reverse_append] at hR
      have h₀ := step_c0_cons fl false (false :: r) (enc as) (enc bs) v
      have h₁ := step_c1_ff fl r (enc as) (enc bs) (some (.inl false))
      cases fl
      · have hD := drain_run false (enc r) [] (enc (as.reverse ++ bs)) none
        exact (Run.head h₀ (Run.head h₁ (hR.trans hD))).of_eq (by simp [T]; omega)
      · have hI := ih none
        exact (Run.head h₀ (Run.head h₁ (hR.trans hI))).of_eq (by simp [T]; omega)
  | case2 r as fl ih =>
      exact (Run.head (step_c0_cons fl false (true :: r) (enc as) [] v)
        (Run.head (step_c1_ft fl r (enc as) [] _)
          (Run.head (step_adv_nil fl none (enc r) (enc as) _) (ih none)))).of_eq
        (by simp [T]; omega)
  | case3 r x bs as fl ih =>
      exact (Run.head (step_c0_cons fl false (true :: r) (enc as) (enc (x :: bs)) v)
        (Run.head (step_c1_ft fl r (enc as) (enc (x :: bs)) _)
          (Run.head (step_adv_none_cons fl x (enc r) (enc as) bs _) (ih _)))).of_eq
        (by simp [T]; omega)
  | case4 s r as fl ih =>
      exact (Run.head (step_c0_cons fl true (s :: r) (enc as) [] v)
        (Run.head (step_c1_t fl s r (enc as) [] _)
          (Run.head (step_adv_nil fl (some s) (enc r) (enc as) _) (ih none)))).of_eq
        (by simp [T]; omega)
  | case5 s r x bs as fl ih =>
      exact (Run.head (step_c0_cons fl true (s :: r) (enc as) (enc (x :: bs)) v)
        (Run.head (step_c1_t fl s r (enc as) (enc (x :: bs)) _)
          (Run.head (step_adv_some_cons fl s x (enc r) (enc as) bs _) (ih _)))).of_eq
        (by simp [T]; omega)
  | case6 r bs as fl h₁ h₂ h₃ h₄ h₅ =>
      rcases r with _ | ⟨b, _ | ⟨b', r⟩⟩
      · have hD := drain_run true [] (enc as) (enc bs) none
        have h := Run.head (step_c0_nil fl (enc as) (enc bs) v) hD
        rw [T_nil]
        exact h.of_eq (by simp)
      · have hD := drain_run true [] (enc as) (enc bs) none
        have h := Run.head (step_c0_cons fl b [] (enc as) (enc bs) v)
          (Run.head (step_c1_nil fl b (enc as) (enc bs) (some (.inl b))) hD)
        rw [T_single]
        have h' := h.of_eq (m := 1 + as.length + bs.length + 4) (by simp; omega)
        cases b <;> exact h'
      · exfalso
        rcases bs with _ | ⟨x, bs⟩ <;> cases b <;> cases b' <;>
          first
          | exact h₁ r rfl
          | exact h₂ r rfl rfl
          | exact h₃ r x bs rfl rfl
          | exact h₄ _ r rfl rfl
          | exact h₅ _ r x bs rfl rfl

theorem T_le (r bs as : List Bool) (fl : Bool) :
    T r bs as fl ≤ (r.length + 1) * (bs.length + as.length + 5) := by
  induction r, bs, as, fl using evalCNF.induct with
  | case1 r bs as fl ih =>
      cases fl
      · simp [T]; nlinarith
      · simp [T] at ih ⊢; nlinarith
  | case2 r as fl ih => simp [T] at ih ⊢; nlinarith
  | case3 r x bs as fl ih => simp [T] at ih ⊢; nlinarith
  | case4 s r as fl ih => simp [T] at ih ⊢; nlinarith
  | case5 s r x bs as fl ih => simp [T] at ih ⊢; nlinarith
  | case6 r bs as fl h₁ h₂ h₃ h₄ h₅ =>
      rcases r with _ | ⟨b, _ | ⟨b', r⟩⟩
      · rw [T_nil]; simp; nlinarith
      · rw [T_single]; simp; nlinarith
      · exfalso
        rcases bs with _ | ⟨x, bs⟩ <;> cases b <;> cases b' <;>
          first
          | exact h₁ r rfl
          | exact h₂ r rfl rfl
          | exact h₃ r x bs rfl rfl
          | exact h₄ _ r rfl rfl
          | exact h₅ _ r x bs rfl rfl

/-! ### Splitting the input `w # y` -/

/-- Right-tagged certificate bits, as they appear in the pair encoding. -/
def encR (y : List Bool) : List G := y.map fun b => .inr (some b)

/-- Phases 1–4: stash `w`, stash `y`, and restore both in order (`w` on `inp`, `y` on `B`). -/
theorem prefix_run (w y : List Bool) :
    Run (w.length + 1 + (y.length + 1) + (w.length + 1) + (y.length + 1))
      ⟨some .read1, none, stk (mkV (enc w ++ .inr none :: encR y) [] [] []) []⟩
      ⟨some (.c0 false), none, stk (mkV (enc w) [] [] (enc y)) []⟩ := by
  have h₁ := loop_run .inp gRead1 (some .F) .read1 .read2 rfl (by simp) [] (enc w) (enc w)
    (.inr none :: encR y) none (mkV (enc w ++ .inr none :: encR y) [] [] [])
    (by simp [enc, gRead1]) rfl rfl
  have h₂ := loop_run .inp gRead2 (some .A) .read2 .back1 rfl (by simp) [] (encR y) (enc y) []
    (some (.inr none)) (mkV (encR y) (enc w).reverse [] []) (by simp [encR, enc, gRead2]) rfl
    (by simp [mkV])
  have h₃ := loop_run .F some (some .inp) .back1 .back2 rfl (by simp) [] (enc w).reverse
    (enc w).reverse [] none (mkV [] (enc w).reverse (enc y).reverse []) rfl rfl (by simp [mkV])
  have h₄ := loop_run .A some (some .B) .back2 (.c0 false) rfl (by simp) [] (enc y).reverse
    (enc y).reverse [] none (mkV (enc w) [] (enc y).reverse []) rfl rfl (by simp [mkV])
  simp only [pushAll, List.tail_cons, List.tail_nil, List.head?_cons, List.head?_nil,
    update_mkV_inp, update_mkV_F, update_mkV_A, update_mkV_B, mkV, List.append_nil,
    List.reverse_reverse] at h₁ h₂ h₃ h₄
  exact (((h₁.trans h₂).trans h₃).trans h₄).of_eq (by simp [encR])

theorem initList_tm (l : List G) :
    initList tm l = ⟨some .read1, none, stk (mkV l [] [] []) []⟩ := by
  simp only [initList]
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl

theorem haltList_tm (l : List Bool) :
    haltList tm l = ⟨none, none, stk (mkV [] [] [] []) l⟩ := by
  simp only [haltList]
  congr 1
  funext k
  rcases k with _ | k
  · rfl
  · cases k <;> rfl

/-- Exact number of steps on `w # y`. -/
def totalSteps (w y : List Bool) : ℕ :=
  w.length + 1 + (y.length + 1) + (w.length + 1) + (y.length + 1) + T w y [] false + 1

/-- Time bound `2 (n + 5)²` in the length `n = |w| + 1 + |y|` of `w # y`. -/
noncomputable def time : Polynomial ℕ :=
  Polynomial.C 2 * (Polynomial.X + Polynomial.C 5) ^ 2

/-- The verifier decides `check` on `w # y` in polynomial time. -/
noncomputable def verifier :
    TM2ComputableInPolyTime (pair_encoding (fin_encoding_string Bool) (fin_encoding_string Bool)).encode
      Computability.finEncodingBoolBool.encode (fun p => check p.1 p.2) where
  tm := tm
  inputAlphabet := Equiv.refl G
  outputAlphabet := Equiv.refl Bool
  time := time
  outputsFun := fun p => by
    obtain ⟨w, y⟩ := p
    have hin : List.map (Equiv.refl G).invFun
        ((pair_encoding (fin_encoding_string Bool) (fin_encoding_string Bool)).encode (w, y)) =
        enc w ++ .inr none :: encR y := by
      simp [pair_encoding, enc, encR]
      rfl
    have hlen : ((pair_encoding (fin_encoding_string Bool) (fin_encoding_string Bool)).encode
        (w, y)).length = w.length + 1 + y.length := by
      show (List.map (Sum.inl : Bool → G) w ++ (Sum.inr none : G) ::
        List.map (fun b : Bool => (Sum.inr (some b) : G)) y).length = _
      simp only [List.length_append, List.length_map, List.length_cons]
      omega
    have hrun := ((prefix_run w y).trans (scan w y [] false none)).trans (finish_run (check w y))
    unfold TM2OutputsInTime
    refine { steps := totalSteps w y, evals_in_steps := ?_, steps_le_m := ?_ }
    · change (flip bind (TM2.step prog))^[_] (some (initList tm _)) =
        Option.map (haltList tm) (some _)
      erw [hin, initList_tm, Option.map_some, haltList_tm]
      exact hrun
    · rw [hlen, totalSteps]
      have hT := T_le w y [] false
      simp only [time, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
        Polynomial.eval_add, Polynomial.eval_X, List.length_nil] at hT ⊢
      nlinarith

end Verifier

open Verifier in
/-- **SAT ∈ NP** (the easy half of Cook–Levin): certificates are assignments, `k = 1`, and the
checking relation `check` is decided in polynomial time by the explicit machine `Verifier.tm`. -/
theorem sat_in_np : InNondeterministicPolynomialTime (fin_encoding_string Bool) SAT :=
  ⟨Bool, inferInstance, fun w y => check w y = true, 1,
    ⟨fun p => check p.1 p.2, verifier, fun _ => Iff.rfl⟩, fun w => sat_iff_check w⟩

/-! ## Part 2: NP-hardness

`cook_levin` (membership `sat_in_np` + hardness) is proved in Pkg.lean, section [HARD], because the
reduction chain (D3Fam … Pkg) imports this file. Its statement there is identical to the former
placeholder declaration here (see NOTES.md, "CLOSE cook_levin"). -/

end PvsNP
