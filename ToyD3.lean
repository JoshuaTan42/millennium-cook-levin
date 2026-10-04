/-!
# SCRATCH — toy D3 trial run (throwaway; not a lakefile root; not imported by anything)

This file has no `import` line on purpose: it is checked by appending it to `Prog.lean`
(`Prog.lean` is not a built module yet, so it cannot be imported):

    (Prog.lean with `import Mathlib.Tactic.Linarith` added, then ToyD3.lean) > ToyCheck.lean
    lake env lean ToyCheck.lean      -- see check_toy.sh in the session scratchpad

Purpose: measure the cost per construct of writing a generator with the D1 library.
Toy task: from `n` in unary, emit the dense-CNF bits of the "diagonal" formula
`⋀_{i<n} ¬x_i` written as `n` clauses of width `n` (slot `i` of clause `i` is `¬x_i` = `11`,
every other slot is absent = `01`, clause end = `00`). Constructs used: one `xfer` (copy the
input into two loop counters), two nested `forLoop`s, a `cmp` of the two loop indices, three
`emit`s. The output stack ends up holding the bits in reverse (stacks reverse; a final reversal
is not part of this toy).
-/

namespace PvsNP.Toy

open PvsNP.Prog Turing Function

inductive TK | N | I | Id | J | Jd | T1 | T2 | out
  deriving DecidableEq

abbrev TΓ : TK → Type
  | .out => Bool
  | _ => Unit

inductive TL
  | start | oHead | oRest | iHead | iRest | endC | cmp
  | r (o : Ordering) | rB (o : Ordering) | out (o : Ordering) | done

/-- Bits of one slot, from the comparison of inner index with outer index. -/
def slotBits : Ordering → List Bool
  | .eq => [true, true]
  | _ => [false, true]

def prog : TL → TM2.Stmt TΓ TL Bool
  | .start => xfer .N [⟨.I, ()⟩, ⟨.J, ()⟩] .start .oHead
  | .oHead => forHead .I .Id () .iHead .oRest
  | .oRest => xfer .Id [⟨.I, ()⟩] .oRest .done
  | .iHead => forHead .J .Jd () .cmp .iRest
  | .iRest => xfer .Jd [⟨.J, ()⟩] .iRest .endC
  | .endC => emit .out [false, false] .oHead
  | .cmp => cmpStep .Jd .Id .T1 .T2 () () .cmp (.r .lt) (.r .eq) (.r .gt)
  | .r o => xfer .T1 [⟨.Jd, ()⟩] (.r o) (.rB o)
  | .rB o => xfer .T2 [⟨.Id, ()⟩] (.rB o) (.out o)
  | .out o => emit .out (slotBits o) .iHead
  | .done => .halt

/-! ### Specification -/

def rowBits (i k : ℕ) : List Bool :=
  (List.range k).flatMap fun t => if t = i then [true, true] else [false, true]

def diagBits (n m : ℕ) : List Bool :=
  (List.range m).flatMap fun i => rowBits i n ++ [false, false]

theorem slotBits_compare (k i : ℕ) :
    slotBits (compare (k + 1) (i + 1)) = if k = i then [true, true] else [false, true] := by
  rcases lt_trichotomy k i with h | h | h
  · rw [Nat.compare_eq_lt.2 (by omega), if_neg (by omega)]; rfl
  · rw [Nat.compare_eq_eq.2 (by omega), if_pos h]; rfl
  · rw [Nat.compare_eq_gt.2 (by omega), if_neg (by omega)]; rfl

/-! ### Inner loop body: compare the indices, emit one slot -/

def costIn (i k : ℕ) : ℕ := 3 * min (k + 1) (i + 1) + 3 + (if k + 1 = i + 1 then 0 else 1) + 1

/-- Invariant of the inner loop (iteration `k` of clause `i`). -/
def Pin (n i : ℕ) (k : ℕ) (S : ∀ k, List (TΓ k)) : Prop :=
  S .Id = cnt () (i + 1) ∧ S .T1 = [] ∧ S .T2 = [] ∧ S .I = cnt () (n - 1 - i) ∧
    S .out = (rowBits i k).reverse ++ (diagBits n i).reverse

theorem inner_body (n i : ℕ) (k : ℕ) (S : ∀ k, List (TΓ k)) (hJd : S .Jd = cnt () (k + 1))
    (hP : Pin n i k S) :
    ∃ (v' : Bool) (S' : ∀ k, List (TΓ k)),
      Run prog (costIn i k) ⟨some .cmp, true, S⟩ ⟨some .iHead, v', S'⟩ ∧
      S' .J = S .J ∧ S' .Jd = S .Jd ∧ Pin n i (k + 1) S' := by
  obtain ⟨hId, hT1, hT2, hI, hout⟩ := hP
  have hc := cmp_run (M := prog) (self := .cmp) (r := .r) (rB := .rB) (out := .out) rfl
    (fun _ => rfl) (fun _ => rfl) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (k + 1) (i + 1) true S hJd hId hT1 hT2
  have he := emit_run (M := prog) (self := .out (compare (k + 1) (i + 1))) rfl false S
  refine ⟨false, _, (hc.trans he).of_eq (by simp [costIn]), ?_, ?_, ?_⟩
  · rw [update_of_ne (by decide)]
  · rw [update_of_ne (by decide)]
  · refine ⟨by rw [update_of_ne (by decide), hId], by rw [update_of_ne (by decide), hT1],
      by rw [update_of_ne (by decide), hT2], by rw [update_of_ne (by decide), hI], ?_⟩
    rw [update_self, hout, slotBits_compare]
    simp [rowBits, List.range_succ]

/-! ### Outer loop body: the inner loop, then the clause terminator -/

def costOut (n i : ℕ) : ℕ := sumFrom (fun k => costIn i k + 1) 0 n + n + 2 + 1

def Pout (n i : ℕ) (S : ∀ k, List (TΓ k)) : Prop :=
  S .J = cnt () n ∧ S .Jd = [] ∧ S .T1 = [] ∧ S .T2 = [] ∧ S .out = (diagBits n i).reverse

theorem outer_body (n i : ℕ) (_hi : i < n) (S : ∀ k, List (TΓ k))
    (hI : S .I = cnt () (n - 1 - i)) (hId : S .Id = cnt () (i + 1)) (hP : Pout n i S) :
    ∃ (v' : Bool) (S' : ∀ k, List (TΓ k)),
      Run prog (costOut n i) ⟨some .iHead, true, S⟩ ⟨some .oHead, v', S'⟩ ∧
      S' .I = S .I ∧ S' .Id = S .Id ∧ Pout n (i + 1) S' := by
  obtain ⟨hJ, hJd, hT1, hT2, hout⟩ := hP
  obtain ⟨S₁, h₁, h₁J, h₁Jd, h₁Id, h₁T1, h₁T2, h₁I, h₁out⟩ :=
    forLoop_run (M := prog) (c := .J) (cd := .Jd) (head := .iHead) (body := .cmp)
      (rest := .iRest) (next := .endC) (uc := ()) (ucd := ()) rfl rfl (by decide) n (Pin n i)
      (fun _ S S' h ⟨a, b, c, d, e⟩ => ⟨by rw [h _ (by decide) (by decide), a],
        by rw [h _ (by decide) (by decide), b], by rw [h _ (by decide) (by decide), c],
        by rw [h _ (by decide) (by decide), d], by rw [h _ (by decide) (by decide), e]⟩)
      (costIn i) (fun k _ S _ hJd hP => inner_body n i k S hJd hP) true S hJ hJd
      ⟨hId, hT1, hT2, hI, by simp [hout, rowBits]⟩
  have he := emit_run (M := prog) (self := .endC) rfl (Flag.tag false) S₁
  refine ⟨_, _, (h₁.trans he).of_eq rfl, ?_, ?_, ?_⟩
  · rw [update_of_ne (by decide), h₁I, hI]
  · rw [update_of_ne (by decide), h₁Id, hId]
  · refine ⟨by rw [update_of_ne (by decide), h₁J], by rw [update_of_ne (by decide), h₁Jd],
      by rw [update_of_ne (by decide), h₁T1], by rw [update_of_ne (by decide), h₁T2], ?_⟩
    rw [update_self, h₁out]
    simp [diagBits, List.range_succ]

/-! ### The whole toy machine -/

def init (n : ℕ) : ∀ k, List (TΓ k)
  | .N => cnt () n
  | _ => []

def toyTime (n : ℕ) : ℕ := (n + 1) + (sumFrom (fun i => costOut n i + 1) 0 n + n + 2)

theorem toy_run (n : ℕ) : ∃ S' : ∀ k, List (TΓ k),
    Run prog (toyTime n) ⟨some .start, false, init n⟩ ⟨some .done, false, S'⟩ ∧
      S' .out = (diagBits n n).reverse := by
  have h₀ := xfer_run (M := prog) (self := .start) (next := .oHead) (k := .N) rfl
    (by simp [List.NodupKeys, List.keys]) (by simp [List.keys])
    () n false (init n) rfl
  set S₀ := addU [⟨TK.I, ()⟩, ⟨TK.J, ()⟩] n (update (init n) .N []) with hS₀
  obtain ⟨S', h₁, -, -, hP⟩ :=
    forLoop_run (M := prog) (c := .I) (cd := .Id) (head := .oHead) (body := .iHead)
      (rest := .oRest) (next := .done) (uc := ()) (ucd := ()) rfl rfl (by decide) n (Pout n)
      (fun _ S S' h ⟨a, b, c, d, e⟩ => ⟨by rw [h _ (by decide) (by decide), a],
        by rw [h _ (by decide) (by decide), b], by rw [h _ (by decide) (by decide), c],
        by rw [h _ (by decide) (by decide), d], by rw [h _ (by decide) (by decide), e]⟩)
      (costOut n) (fun i hi S hI hId hP => outer_body n i hi S hI hId hP) (Flag.tag false) S₀
      (by simp [hS₀, addU, init]) (by simp [hS₀, addU, init])
      ⟨by simp [hS₀, addU, init], by simp [hS₀, addU, init], by simp [hS₀, addU, init],
        by simp [hS₀, addU, init], by simp [hS₀, addU, init, diagBits]⟩
  exact ⟨S', h₀.trans h₁, hP.2.2.2.2⟩

/-- Polynomial bound on the step count. -/
theorem toyTime_le (n : ℕ) : toyTime n ≤ 10 * (n + 1) ^ 3 := by
  have hin : ∀ i, i < n → sumFrom (fun k => costIn i k + 1) 0 n ≤ n * (3 * n + 6) := by
    intro i hi
    refine sumFrom_le 0 n (fun k _ _ => ?_)
    simp only [costIn]
    have : min (k + 1) (i + 1) ≤ n := le_trans (min_le_right _ _) (by omega)
    split_ifs <;> omega
  have hout : sumFrom (fun i => costOut n i + 1) 0 n ≤ n * (n * (3 * n + 6) + n + 4) := by
    refine sumFrom_le 0 n (fun i _ hi => ?_)
    have := hin i (by omega)
    simp only [costOut]; omega
  simp only [toyTime]
  nlinarith [hout]

/-- Concrete sanity check of the specification (kernel `decide`, n = 2):
clauses `¬x₀` = `11 01 00` and `¬x₁` = `01 11 00`. -/
example : diagBits 2 2 = [true, true, false, true, false, false,
    false, true, true, true, false, false] := by decide

end PvsNP.Toy
