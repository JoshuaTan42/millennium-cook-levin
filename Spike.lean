import CookLevin

/-!
# SCRATCH / NON-CANONICAL — throwaway spike, 2026-09-27

NOT part of the proof. Not in the lakefile roots, not imported by anything. Later sessions must
not treat anything here as progress. Purpose: test design bet P3 of the Cook–Levin plan in
NOTES.md ("index stacks from the top; one TM2 step = a constant shift of each stack, decided by
label, state and the top-`d` windows only").

The model (`eff` + `shiftCells`) sees ONLY the label, the state, and the top-`d` cells of each
stack when deciding what happens. The shift itself moves cells positionally without reading
them. We compare it against Mathlib's real `TM2.step`.
-/

namespace Spike

open Turing Function

section Model

variable {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}

/-- Top symbol of stack `k` as the model sees it: the most recent symbol pushed in this step if
any, otherwise the window entry below the `j k` original symbols already consumed
(`none` = ⊥, i.e. empty). -/
def readTop (win : ∀ k, List (Option (Γ k))) (P : ∀ k, List (Γ k)) (j : K → ℕ) (k : K) :
    Option (Γ k) :=
  match P k with
  | x :: _ => some x
  | [] => (win k).getD (j k) none

/-- Symbolic effect of one statement tree, computed from the windows only.
`P k`: symbols pushed this step and still on top; `j k`: original symbols consumed. -/
def eff (win : ∀ k, List (Option (Γ k))) :
    TM2.Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → (K → ℕ) →
      Option Λ × σ × (∀ k, List (Γ k)) × (K → ℕ)
  | .push k f q, v, P, j => eff win q v (update P k (f v :: P k)) j
  | .peek k f q, v, P, j => eff win q (f v (readTop win P j k)) P j
  | .pop k f q, v, P, j =>
      eff win q (f v (readTop win P j k))
        (if (P k).isEmpty then P else update P k (P k).tail)
        (if (P k).isEmpty then update j k (j k + 1) else j)
  | .load a q, v, P, j => eff win q (a v) P j
  | .branch p q₁ q₂, v, P, j => cond (p v) (eff win q₁ v P j) (eff win q₂ v P j)
  | .goto f, v, P, j => (some (f v), v, P, j)
  | .halt, v, P, j => (none, v, P, j)

/-- Top-indexed, ⊥-padded cells `0..H-1` of stack `k` (`none` = ⊥). -/
def cells (H : ℕ) (S : ∀ k, List (Γ k)) (k : K) : List (Option (Γ k)) :=
  (List.range H).map fun i => (S k)[i]?

/-- The shift: positions `< |P|` get the pushed symbols, position `i ≥ |P|` gets old cell
`i - |P| + j` (⊥ if that is `≥ H`). Positional only; never reads cell contents. -/
def shiftCells {α : Type} (H : ℕ) (old : List (Option α)) (P : List α) (j : ℕ) :
    List (Option α) :=
  (List.range H).map fun i => if i < P.length then P[i]? else old.getD (i - P.length + j) none

/-- One model step on a cell array. -/
def modelStep (M : Λ → TM2.Stmt Γ Λ σ) (d H : ℕ) (l : Λ) (v : σ)
    (C : ∀ k, List (Option (Γ k))) : Option Λ × σ × (∀ k, List (Option (Γ k))) :=
  let r := eff (fun k => (C k).take d) (M l) v (fun _ => []) (fun _ => 0)
  (r.1, r.2.1, fun k => shiftCells H (C k) (r.2.2.1 k) (r.2.2.2 k))

variable [∀ k, DecidableEq (Γ k)] [DecidableEq Λ] [DecidableEq σ]

/-- Does one model step agree with the real `TM2.step` (label, state, all listed stacks)? -/
def agree (M : Λ → TM2.Stmt Γ Λ σ) (d H : ℕ) (ks : List K) (l : Λ) (v : σ)
    (S : ∀ k, List (Γ k)) : Bool :=
  match TM2.step M ⟨some l, v, S⟩ with
  | some c' =>
      let r := modelStep M d H l v (fun k => cells H S k)
      decide (c'.l = r.1) && decide (c'.var = r.2.1) &&
        ks.all fun k => decide (cells H c'.stk k = r.2.2 k)
  | none => false

/-- Run both for `n` steps from `(l, v, S)`, comparing after every step. The model iterates on
its own cell arrays (never re-reading the real stacks). -/
def agreeRun (M : Λ → TM2.Stmt Γ Λ σ) (d H : ℕ) (ks : List K) :
    ℕ → Option Λ → σ → (∀ k, List (Γ k)) → Option Λ → σ → (∀ k, List (Option (Γ k))) → Bool
  | 0, _, _, _, _, _, _ => true
  | n + 1, l, v, S, ml, mv, C =>
      match l, ml with
      | none, none => true
      | some l, some ml' =>
          match TM2.step M ⟨some l, v, S⟩ with
          | some c' =>
              let r := modelStep M d H ml' mv C
              decide (c'.l = r.1) && decide (c'.var = r.2.1) &&
                (ks.all fun k => decide (cells H c'.stk k = r.2.2 k)) &&
                agreeRun M d H ks n c'.l c'.var c'.stk r.1 r.2.1 r.2.2
          | none => false
      | _, _ => false

end Model

/-! ## Test 1: a toy machine built to hit the stress cases -/

inductive TK | a | b
  deriving DecidableEq

inductive TL | l0 | l1 | l2
  deriving DecidableEq

abbrev TΓ : TK → Type := fun _ => Bool

/-- * `l0`: push `true` on `a` then immediately pop it (push-then-pop, same stack, same step);
      then pop `b` (often empty: height 0); branch.
    * `l1`: pop `a`, push two symbols on `b` (attention moves from `a` to `b`).
    * `l2`: push on `a`, peek it, pop it, pop an ORIGINAL symbol of `a` (net consumption 1),
      peek `b`; branch or halt. -/
def toy : TL → TM2.Stmt TΓ TL (Option Bool)
  | .l0 =>
      .push .a (fun _ => true) <| .pop .a (fun _ o => o) <|
        .pop .b (fun v o => if o.isSome then o else v) <|
          .branch (fun v => v == some true) (.goto fun _ => .l1) (.goto fun _ => .l2)
  | .l1 =>
      .pop .a (fun _ o => o) <| .push .b (fun v => v.getD false) <|
        .push .b (fun _ => true) <| .goto fun _ => .l2
  | .l2 =>
      .push .a (fun _ => false) <| .peek .a (fun _ o => o) <| .pop .a (fun v _ => v) <|
        .pop .a (fun v o => if o == some true then some true else v) <|
          .peek .b (fun v o => if o == some false then none else v) <|
            .branch (fun v => v == some true) (.goto fun _ => .l0) .halt

def toyStk (xa xb : List Bool) : ∀ k : TK, List (TΓ k)
  | .a => xa
  | .b => xb

def bools : List (List Bool) :=
  [[], [false], [true], [false, false], [false, true], [true, false], [true, true],
   [false, false, false], [true, false, true], [true, true, true], [false, true, true]]

def toyStates : List (Option Bool) := [none, some false, some true]

/-- Exhaustive single-step check over 3 labels × 3 states × 11 × 11 stack contents. -/
def toyCount : ℕ × ℕ :=
  let tests := [TL.l0, .l1, .l2].flatMap fun l => toyStates.flatMap fun v =>
    bools.flatMap fun xa => bools.map fun xb => agree toy 2 8 [.a, .b] l v (toyStk xa xb)
  (tests.length, (tests.filter (· = false)).length)

#eval toyCount   -- expect (tests, 0 mismatches)

/-- Multi-step runs (up to 6 steps) from every start, model iterating on its own cells. -/
def toyRunCount : ℕ × ℕ :=
  let tests := [TL.l0, .l1, .l2].flatMap fun l => toyStates.flatMap fun v =>
    bools.flatMap fun xa => bools.map fun xb =>
      agreeRun toy 2 12 [.a, .b] 6 (some l) v (toyStk xa xb) (some l) v
        (fun k => cells 12 (toyStk xa xb) k)
  (tests.length, (tests.filter (· = false)).length)

#eval toyRunCount

/-! Kernel-checked instances of the stress cases (checked by `decide`, not just `#eval`). -/

-- height 0 on `b`, push-then-pop on `a`:
example : agree toy 2 8 [.a, .b] .l0 none (toyStk [false] []) = true := by decide
-- height 0 on both stacks:
example : agree toy 2 8 [.a, .b] .l0 none (toyStk [] []) = true := by decide
-- attention moves from `a` to `b`, `a` empty (pop on empty):
example : agree toy 2 8 [.a, .b] .l1 (some true) (toyStk [] [true]) = true := by decide
-- push, peek, pop the pushed symbol, then pop an original:
example : agree toy 2 8 [.a, .b] .l2 none (toyStk [true, false] [false]) = true := by decide
-- three steps, model on its own cells:
example : agreeRun toy 2 8 [.a, .b] 3 (some .l0) none (toyStk [true] [])
    (some .l0) none (fun k => cells 8 (toyStk [true] []) k) = true := by decide

/-! ## Test 2: the real SAT verifier machine from CookLevin.lean (read-only use) -/

open PvsNP.Verifier in
instance : ∀ k, DecidableEq (Γ k)
  | none => inferInstanceAs (DecidableEq Bool)
  | some _ => inferInstanceAs (DecidableEq G)

open PvsNP.Verifier

def labs : List Lab :=
  [.read1, .read2, .back1, .back2] ++
  [false, true].flatMap (fun fl =>
    [Lab.c0 fl, .restore fl, .c1 fl false, .c1 fl true,
     .adv fl none, .adv fl (some false), .adv fl (some true)]) ++
  [false, true].flatMap (fun a => [Lab.drainI a, .drainA a, .drainB a, .finish a])

def gs : List G := [.inl false, .inl true, .inr none, .inr (some false), .inr (some true)]
def gLists : List (List G) := [] :: gs.map ([·])
def sts : List St := none :: gs.map some

def vStk (i f a b : List G) (o : List Bool) : ∀ k, List (Γ k) := stk (mkV i f a b) o

def verKs : List (Option W) := [none, some .inp, some .F, some .A, some .B]

/-- Exhaustive single-step check: 30 labels × 6 states × 6⁴ work-stack contents × 3 outputs. -/
def verCount : ℕ × ℕ := Id.run do
  let mut n := 0
  let mut bad := 0
  for l in labs do
    for v in sts do
      for i in gLists do
        for f in gLists do
          for a in gLists do
            for b in gLists do
              for o in [[], [false], [true]] do
                n := n + 1
                if !agree prog 2 6 verKs l v (vStk i f a b o) then bad := bad + 1
  return (n, bad)

#eval verCount

/-- A full run of the verifier on a real input `w # y` (w = `10 00`, y = `[true]`),
model iterating on its own cells for 40 steps (the run halts well before). -/
def verRun : Bool :=
  let inp : List G := [.inl true, .inl false, .inl false, .inl false, .inr none, .inr (some true)]
  agreeRun prog 2 16 verKs 40 (some .read1) none (vStk inp [] [] [] []) (some .read1) none
    (fun k => cells 16 (vStk inp [] [] [] []) k)

#eval verRun

/-! ## Negative controls: the model must FAIL when its preconditions are violated -/

-- Window too small (`d = 0`): the model cannot see the popped symbol of `b` (real state becomes
-- `some false`, model keeps `some true`). Expect `false`.
#eval agree toy 0 8 [.a, .b] .l0 none (toyStk [] [false])
-- Cap too small (`H = 1`, height 2 > H - d): after a pop, the symbol that should shift up
-- from position 1 was never stored. Expect `false`.
#eval agree toy 2 1 [.a, .b] .l0 none (toyStk [] [true, false])
-- Same config with an adequate cap. Expect `true`.
#eval agree toy 2 4 [.a, .b] .l0 none (toyStk [] [true, false])

end Spike
