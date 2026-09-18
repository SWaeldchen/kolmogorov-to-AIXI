/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.SeqMeasure
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure

/-!
# Trimming an lsc function into a continuous semimeasure

The universal continuous semimeasure (Gács Theorem 2.3.5) is a weighted sum over an
effective enumeration of *all* lower semicomputable functions, each first **trimmed**
into a continuous semimeasure in a way that leaves genuine semimeasures unchanged.

Gács' discrete trimming (proof of Theorem 1.6.3) freezes the approximation as soon as
it violates the constraint. That does not transfer: lower approximations of a genuine
continuous semimeasure `ν` may violate `ψ(x0) + ψ(x1) ≤ ψ(x)` at finite stages, because
`ψ(x)` can lag behind `ψ(x0) + ψ(x1)`. The standard repair (Zvonkin–Levin, Li–Vitányi
Thm 4.5.2) is used instead:

* **Raise bottom-up.** At stage `s`, on the finite tree of strings of length `≤ s`, set
  `φ(x) = max(ψ_s(x), φ(x0) + φ(x1))` (`bump`, `stageVal`). This satisfies the children
  constraint by construction, is monotone in `s` when `ψ` is, and never exceeds a
  semimeasure that bounds `ψ_s` (`bump_le_of_semimeasure`).
* **Freeze on the root only.** If the raised root exceeds `1`, keep the previous stage
  (`trimSt`). For a genuine semimeasure the root check always passes, so the trimmed
  function equals `ν` in the limit (`iSup_trimSt_eq`).

`bump` is a tree recursion, for which Mathlib has no `Computable` closure lemma; its
computability is obtained by evaluating it level by level on lists (`levelVals`), which
is a `Nat.rec` with list state (`bump_eq_levelVals`, `trimSt_computable`).
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Bottom-up raising -/

/-- Raise `f` bottom-up with depth budget `d`: `bump f 0 = f`,
`bump f (d+1) x = max (f x) (bump f d x0 + bump f d x1)`. -/
def bump (f : BitString → ℕ) : ℕ → BitString → ℕ
  | 0, x => f x
  | d + 1, x => max (f x) (bump f d (x ++ [false]) + bump f d (x ++ [true]))

theorem le_bump (f : BitString → ℕ) (d : ℕ) (x : BitString) : f x ≤ bump f d x := by
  cases d with
  | zero => exact le_rfl
  | succ d => exact le_max_left _ _

theorem bump_children_le (f : BitString → ℕ) (d : ℕ) (x : BitString) :
    bump f d (x ++ [false]) + bump f d (x ++ [true]) ≤ bump f (d + 1) x :=
  le_max_right _ _

/-- Raising never exceeds a continuous semimeasure that bounds `f` (at scale `2^{-s}`). -/
theorem bump_le_of_semimeasure {ν : BitString → ℝ≥0∞}
    (hν : ∀ x, ν (x ++ [false]) + ν (x ++ [true]) ≤ ν x) {f : BitString → ℕ} {s : ℕ}
    (hf : ∀ x, (f x : ℝ≥0∞) / 2 ^ s ≤ ν x) (d : ℕ) (x : BitString) :
    (bump f d x : ℝ≥0∞) / 2 ^ s ≤ ν x := by
  induction d generalizing x with
  | zero => exact hf x
  | succ d ih =>
    simp only [bump]
    rcases le_total (f x) (bump f d (x ++ [false]) + bump f d (x ++ [true])) with h | h
    · rw [max_eq_right h, Nat.cast_add, ← ENNReal.div_add_div_same]
      exact (add_le_add (ih _) (ih _)).trans (hν x)
    · rw [max_eq_left h]; exact hf x

/-- Raising is monotone across a stage refinement `2 f ≤ g`. -/
theorem bump_mono_step {f g : BitString → ℕ} (h : ∀ y, 2 * f y ≤ g y) (d : ℕ) (x : BitString) :
    2 * bump f d x ≤ bump g (d + 1) x := by
  induction d generalizing x with
  | zero => exact (h x).trans (le_max_left _ _)
  | succ d ih =>
    change 2 * max (f x) (bump f d (x ++ [false]) + bump f d (x ++ [true]))
      ≤ max (g x) (bump g (d + 1) (x ++ [false]) + bump g (d + 1) (x ++ [true]))
    rcases le_total (f x) (bump f d (x ++ [false]) + bump f d (x ++ [true])) with hc | hc
    · rw [max_eq_right hc, Nat.mul_add]
      exact (add_le_add (ih _) (ih _)).trans (le_max_right _ _)
    · rw [max_eq_left hc]; exact (h x).trans (le_max_left _ _)

/-! ### The stage function -/

/-- Stage `s` of the trimming: raise `ψ s` on the tree of depth `s`, zero below it. -/
def stageVal (ψ : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) : ℕ :=
  if x.length ≤ s then bump (ψ s) (s - x.length) x else 0

theorem stageVal_children_le (ψ : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) :
    stageVal ψ s (x ++ [false]) + stageVal ψ s (x ++ [true]) ≤ stageVal ψ s x := by
  unfold stageVal
  simp only [List.length_append, List.length_singleton]
  by_cases h : x.length + 1 ≤ s
  · rw [if_pos h, if_pos h, if_pos (by omega)]
    have : s - x.length = (s - (x.length + 1)) + 1 := by omega
    rw [this]
    exact bump_children_le _ _ _
  · rw [if_neg h, if_neg h]; exact zero_le

theorem stageVal_nil (ψ : ℕ → BitString → ℕ) (s : ℕ) : stageVal ψ s [] = bump (ψ s) s [] := by
  simp [stageVal]

theorem stageVal_mono {ψ : ℕ → BitString → ℕ} {s : ℕ} (hψ : ∀ y, 2 * ψ s y ≤ ψ (s + 1) y)
    (x : BitString) : 2 * stageVal ψ s x ≤ stageVal ψ (s + 1) x := by
  unfold stageVal
  by_cases h : x.length ≤ s
  · rw [if_pos h, if_pos (by omega)]
    have : s + 1 - x.length = (s - x.length) + 1 := by omega
    rw [this]
    exact bump_mono_step hψ _ x
  · rw [if_neg h, mul_zero]; exact zero_le

theorem stageVal_ge (ψ : ℕ → BitString → ℕ) {s : ℕ} {x : BitString} (h : x.length ≤ s) :
    ψ s x ≤ stageVal ψ s x := by
  unfold stageVal; rw [if_pos h]; exact le_bump _ _ _

theorem stageVal_le_of_semimeasure {ν : BitString → ℝ≥0∞}
    (hν : ∀ x, ν (x ++ [false]) + ν (x ++ [true]) ≤ ν x) {ψ : ℕ → BitString → ℕ} {s : ℕ}
    (hf : ∀ x, (ψ s x : ℝ≥0∞) / 2 ^ s ≤ ν x) (x : BitString) :
    (stageVal ψ s x : ℝ≥0∞) / 2 ^ s ≤ ν x := by
  unfold stageVal
  split_ifs
  · exact bump_le_of_semimeasure hν hf _ x
  · simp

/-! ### Freezing on the root -/

/-- Root check at stage `s`: the raised root mass is at most `1`. -/
def rootOk (ψ : ℕ → BitString → ℕ) (s : ℕ) : Prop := bump (ψ s) s [] ≤ 2 ^ s

instance (ψ : ℕ → BitString → ℕ) (s : ℕ) : Decidable (rootOk ψ s) := by
  unfold rootOk; infer_instance

/-- **The trimmed stage function**: the raised stage if its root is at most `1`, otherwise
the previous stage rescaled. -/
def trimSt (ψ : ℕ → BitString → ℕ) : ℕ → BitString → ℕ
  | 0, x => if rootOk ψ 0 then stageVal ψ 0 x else 0
  | s + 1, x => if rootOk ψ (s + 1) then stageVal ψ (s + 1) x else 2 * trimSt ψ s x

theorem trimSt_le_stageVal {ψ : ℕ → BitString → ℕ} (hψ : ∀ s y, 2 * ψ s y ≤ ψ (s + 1) y)
    (s : ℕ) (x : BitString) : trimSt ψ s x ≤ stageVal ψ s x := by
  induction s with
  | zero => unfold trimSt; split_ifs <;> simp
  | succ s ih =>
    unfold trimSt
    split_ifs
    · exact le_rfl
    · exact (Nat.mul_le_mul_left 2 ih).trans (stageVal_mono (hψ s) x)

theorem trimSt_mono {ψ : ℕ → BitString → ℕ} (hψ : ∀ s y, 2 * ψ s y ≤ ψ (s + 1) y) (s : ℕ)
    (x : BitString) : 2 * trimSt ψ s x ≤ trimSt ψ (s + 1) x := by
  change 2 * trimSt ψ s x ≤ (if rootOk ψ (s + 1) then stageVal ψ (s + 1) x else 2 * trimSt ψ s x)
  split_ifs
  · exact (Nat.mul_le_mul_left 2 (trimSt_le_stageVal hψ s x)).trans (stageVal_mono (hψ s) x)
  · exact le_rfl

theorem trimSt_children_le (ψ : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) :
    trimSt ψ s (x ++ [false]) + trimSt ψ s (x ++ [true]) ≤ trimSt ψ s x := by
  induction s with
  | zero =>
    unfold trimSt; split_ifs
    · exact stageVal_children_le ψ 0 x
    · simp
  | succ s ih =>
    unfold trimSt; split_ifs
    · exact stageVal_children_le ψ (s + 1) x
    · rw [← Nat.mul_add]; exact Nat.mul_le_mul_left 2 ih

theorem trimSt_root_le (ψ : ℕ → BitString → ℕ) (s : ℕ) : trimSt ψ s [] ≤ 2 ^ s := by
  induction s with
  | zero =>
    unfold trimSt; split_ifs with h
    · rw [stageVal_nil]; exact h
    · exact zero_le
  | succ s ih =>
    unfold trimSt; split_ifs with h
    · rw [stageVal_nil]; exact h
    · rw [pow_succ, mul_comm (2 ^ s) 2]; exact Nat.mul_le_mul_left 2 ih

/-- Dyadic monotonicity of a numerator family from the doubling condition. -/
theorem dyadicValue_le_of_two_mul_le {a b s : ℕ} (h : 2 * a ≤ b) :
    dyadicValue a s ≤ dyadicValue b (s + 1) := by
  unfold dyadicValue
  rw [ENNReal.div_le_iff (two_pow_ne_zero' s) (two_pow_ne_top' s), div_eq_mul_inv, mul_right_comm,
    ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl (two_pow_ne_zero' _)) (Or.inl (two_pow_ne_top' _))]
  have : a * 2 ^ (s + 1) ≤ b * 2 ^ s := by
    calc a * 2 ^ (s + 1) = 2 * a * 2 ^ s := by ring
      _ ≤ b * 2 ^ s := Nat.mul_le_mul_right _ h
  exact_mod_cast this

theorem trimSt_dyadic_mono {ψ : ℕ → BitString → ℕ} (hψ : ∀ s y, 2 * ψ s y ≤ ψ (s + 1) y) (s : ℕ)
    (x : BitString) : dyadicValue (trimSt ψ s x) s ≤ dyadicValue (trimSt ψ (s + 1) x) (s + 1) :=
  dyadicValue_le_of_two_mul_le (trimSt_mono hψ s x)

/-- **The limit of the trimmed stages is a continuous semimeasure.** -/
theorem isContSemimeasure_iSup_trimSt {ψ : ℕ → BitString → ℕ}
    (hψ : ∀ s y, 2 * ψ s y ≤ ψ (s + 1) y) :
    IsContSemimeasure (fun x ↦ ⨆ s, dyadicValue (trimSt ψ s x) s) := by
  refine ⟨iSup_le fun s ↦ ?_, fun x ↦ ?_⟩
  · unfold dyadicValue
    rw [ENNReal.div_le_iff (two_pow_ne_zero' s) (two_pow_ne_top' s), one_mul]
    exact_mod_cast trimSt_root_le ψ s
  · rw [ENNReal.iSup_add_iSup_of_monotone
      (monotone_nat_of_le_succ fun s ↦ trimSt_dyadic_mono hψ s _)
      (monotone_nat_of_le_succ fun s ↦ trimSt_dyadic_mono hψ s _)]
    refine iSup_le fun s ↦ le_iSup_of_le s ?_
    unfold dyadicValue
    rw [ENNReal.div_add_div_same]
    gcongr
    exact_mod_cast trimSt_children_le ψ s x

/-- **Genuine semimeasures are unchanged**: if the approximations `ψ` converge to a
continuous semimeasure `ν`, the trimmed stages also converge to `ν`. -/
theorem iSup_trimSt_eq {ν : BitString → ℝ≥0∞} (hν : IsContSemimeasure ν)
    {ψ : ℕ → BitString → ℕ} (hψ : ∀ s y, 2 * ψ s y ≤ ψ (s + 1) y)
    (hle : ∀ s x, dyadicValue (ψ s x) s ≤ ν x) (hsup : ∀ x, ⨆ s, dyadicValue (ψ s x) s = ν x)
    (x : BitString) : ⨆ s, dyadicValue (trimSt ψ s x) s = ν x := by
  -- The root check always passes.
  have hok : ∀ s, rootOk ψ s := by
    intro s
    unfold rootOk
    have h := bump_le_of_semimeasure hν.2 (f := ψ s) (s := s) (fun x ↦ hle s x) s []
    have h1 : (bump (ψ s) s [] : ℝ≥0∞) / 2 ^ s ≤ 1 := h.trans hν.1
    rw [ENNReal.div_le_iff (two_pow_ne_zero' s) (two_pow_ne_top' s), one_mul] at h1
    exact_mod_cast h1
  have htrim : ∀ s, trimSt ψ s x = stageVal ψ s x := by
    intro s
    cases s with
    | zero => unfold trimSt; rw [if_pos (hok 0)]
    | succ s => unfold trimSt; rw [if_pos (hok (s + 1))]
  simp only [htrim]
  apply le_antisymm
  · exact iSup_le fun s ↦ stageVal_le_of_semimeasure hν.2 (fun y ↦ hle s y) x
  · rw [← hsup x]
    refine iSup_le fun s ↦ ?_
    have hmono : Monotone (fun s ↦ dyadicValue (ψ s x) s) :=
      monotone_nat_of_le_succ fun s ↦ dyadicValue_le_of_two_mul_le (hψ s x)
    calc dyadicValue (ψ s x) s ≤ dyadicValue (ψ (max s x.length) x) (max s x.length) :=
          hmono (le_max_left _ _)
      _ ≤ dyadicValue (stageVal ψ (max s x.length) x) (max s x.length) := by
          unfold dyadicValue; gcongr; exact_mod_cast stageVal_ge ψ (le_max_right _ _)
      _ ≤ ⨆ s, dyadicValue (stageVal ψ s x) s :=
          le_iSup (fun s ↦ dyadicValue (stageVal ψ s x) s) (max s x.length)

/-! ### Level-by-level evaluation of `bump`, for computability -/

/-- All extensions of `x` by `m` bits, children adjacent. -/
def extList (x : BitString) : ℕ → List BitString
  | 0 => [x]
  | m + 1 => (extList x m).flatMap (fun y ↦ [y ++ [false], y ++ [true]])

theorem length_extList (x : BitString) (m : ℕ) : (extList x m).length = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [extList, List.length_flatMap, List.map_const', List.length_cons,
      List.length_nil, List.sum_replicate, smul_eq_mul, ih]
    ring

theorem getElem?_flatMap_pair (l : List BitString) (i : ℕ) :
    (l.flatMap (fun y ↦ [y ++ [false], y ++ [true]]))[2 * i]? = (l[i]?).map (· ++ [false]) ∧
    (l.flatMap (fun y ↦ [y ++ [false], y ++ [true]]))[2 * i + 1]? = (l[i]?).map (· ++ [true]) := by
  induction l generalizing i with
  | nil => simp
  | cons y l ih =>
    cases i with
    | zero => simp
    | succ i =>
      obtain ⟨ih0, ih1⟩ := ih i
      constructor
      · rw [List.flatMap_cons, show 2 * (i + 1) = 2 + 2 * i by ring]
        rw [List.getElem?_append_right (by simp), List.getElem?_cons_succ]
        simpa using ih0
      · rw [List.flatMap_cons, show 2 * (i + 1) + 1 = 2 + (2 * i + 1) by ring]
        rw [List.getElem?_append_right (by simp), List.getElem?_cons_succ]
        simpa using ih1

end Kolmogorov
