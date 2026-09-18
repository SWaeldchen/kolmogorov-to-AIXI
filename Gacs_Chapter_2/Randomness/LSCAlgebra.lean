/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.LowerSemicomputable

/-!
# Algebra of lower semicomputable functions

`IsLSC₁` demands dyadic approximations, `approx s x / 2^s`, one scale per stage. That is
convenient for sums but awkward for products and reciprocals, whose natural
approximations are rationals with other denominators. This file supplies

* `IsLSC₁.of_ratApprox`: a computable, nondecreasing sequence of **rationals** with
  supremum `f` makes `f` lower semicomputable (round each rational down to the dyadic
  grid of its stage);
* `IsLSC₁.of_ratSeq`: the same without monotonicity, by taking running maxima
  (`runMax`, a `Nat.rec`, since Mathlib has no `Computable` list fold);
* `IsLSC₁.mul`: products of lsc functions are lsc;
* `IsComputableENNReal`: Gács' computable real-valued functions on strings
  (Definition 1.5.1), as a pair of computable rational sequences squeezing `f` to
  within `2^{-k}`; such an `f` is lsc, and so is `1/f` (`inv_isLSC₁`), which is the fact
  Theorem 2.2.1 needs to make `2^{-K(x)} / P(x)` a test.
-/

namespace Kolmogorov.Randomness

open scoped ENNReal

/-! ### Rationals as pairs -/

/-- The value `n / d` of a pair of naturals in `ℝ≥0∞`. -/
noncomputable def ratVal (q : ℕ × ℕ) : ℝ≥0∞ := (q.1 : ℝ≥0∞) / q.2

theorem natCast_pos_ne_zero {d : ℕ} (hd : 0 < d) : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd.ne'

/-- Comparison of rationals is a comparison of cross products. -/
theorem ratVal_le_ratVal {q r : ℕ × ℕ} (hq : 0 < q.2) (hr : 0 < r.2) :
    ratVal q ≤ ratVal r ↔ q.1 * r.2 ≤ r.1 * q.2 := by
  unfold ratVal
  rw [ENNReal.div_le_iff (natCast_pos_ne_zero hq) (ENNReal.natCast_ne_top _), div_eq_mul_inv,
    mul_right_comm, ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl (natCast_pos_ne_zero hr)) (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast Iff.rfl

/-! ### Rounding a rational down to a dyadic grid -/

/-- `⌊n 2^s / d⌋`, the numerator of `n/d` rounded down to scale `2^{-s}`. -/
def ratFloor (q : ℕ × ℕ) (s : ℕ) : ℕ := q.1 * 2 ^ s / q.2

theorem dyadicValue_ratFloor_le (q : ℕ × ℕ) (s : ℕ) (hq : 0 < q.2) :
    dyadicValue (ratFloor q s) s ≤ ratVal q := by
  unfold dyadicValue ratFloor ratVal
  rw [ENNReal.div_le_iff (two_pow_ne_zero' s) (two_pow_ne_top' s), div_eq_mul_inv, mul_right_comm,
    ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl (natCast_pos_ne_zero hq)) (Or.inl (ENNReal.natCast_ne_top _))]
  exact_mod_cast Nat.div_mul_le_self (q.1 * 2 ^ s) q.2

theorem ratVal_le_dyadicValue_ratFloor_add (q : ℕ × ℕ) (s : ℕ) (hq : 0 < q.2) :
    ratVal q ≤ dyadicValue (ratFloor q s) s + 2⁻¹ ^ s := by
  have h1 : q.1 * 2 ^ s < q.1 * 2 ^ s / q.2 * q.2 + q.2 := Nat.lt_div_mul_add hq
  have h2 : q.1 * 2 ^ s ≤ (q.1 * 2 ^ s / q.2 + 1) * q.2 := by rw [add_mul, one_mul]; omega
  have h3 : ratVal q ≤ ((q.1 * 2 ^ s / q.2 + 1 : ℕ) : ℝ≥0∞) / 2 ^ s := by
    unfold ratVal
    rw [ENNReal.div_le_iff (natCast_pos_ne_zero hq) (ENNReal.natCast_ne_top _), div_eq_mul_inv,
      mul_right_comm, ← div_eq_mul_inv,
      ENNReal.le_div_iff_mul_le (Or.inl (two_pow_ne_zero' s)) (Or.inl (two_pow_ne_top' s))]
    exact_mod_cast h2
  refine h3.trans (le_of_eq ?_)
  unfold dyadicValue ratFloor
  push_cast
  rw [div_eq_mul_inv, add_mul, one_mul, ← div_eq_mul_inv, ENNReal.inv_pow]

/-- Rounding respects order across one refinement of the grid: if `q ≤ r` then
`2⌊q⌋_s ≤ ⌊r⌋_{s+1}`. -/
theorem ratFloor_mono_step {q r : ℕ × ℕ} (hq : 0 < q.2) (hr : 0 < r.2)
    (h : ratVal q ≤ ratVal r) (s : ℕ) : 2 * ratFloor q s ≤ ratFloor r (s + 1) := by
  have hcross : q.1 * r.2 ≤ r.1 * q.2 := (ratVal_le_ratVal hq hr).mp h
  unfold ratFloor
  calc 2 * (q.1 * 2 ^ s / q.2) ≤ 2 * (q.1 * 2 ^ s) / q.2 := Nat.mul_div_le_mul_div_assoc _ _ _
    _ ≤ r.1 * 2 ^ (s + 1) / r.2 := by
        rw [Nat.le_div_iff_mul_le hr]
        refine Nat.le_of_mul_le_mul_right ?_ hq
        calc 2 * (q.1 * 2 ^ s) / q.2 * r.2 * q.2 = (2 * (q.1 * 2 ^ s) / q.2 * q.2) * r.2 := by ring
          _ ≤ 2 * (q.1 * 2 ^ s) * r.2 := Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
          _ = 2 * 2 ^ s * (q.1 * r.2) := by ring
          _ ≤ 2 * 2 ^ s * (r.1 * q.2) := Nat.mul_le_mul_left _ hcross
          _ = r.1 * 2 ^ (s + 1) * q.2 := by ring

/-! ### Lower semicomputability from rational approximations -/

/-- **Monotone rational approximations give lsc.** -/
theorem IsLSC₁.of_ratApprox {f : BitString → ℝ≥0∞} (approx : ℕ → BitString → ℕ × ℕ)
    (hd : ∀ s x, 0 < (approx s x).2)
    (hmono : ∀ s x, ratVal (approx s x) ≤ ratVal (approx (s + 1) x))
    (hsup : ∀ x, ⨆ s, ratVal (approx s x) = f x)
    (hcomp : Computable (fun p : ℕ × BitString ↦ approx p.1 p.2)) : IsLSC₁ f := by
  refine ⟨fun s x ↦ ratFloor (approx s x) s, fun s x ↦ ?_, fun x ↦ ?_, ?_⟩
  · have h := ratFloor_mono_step (hd s x) (hd (s + 1) x) (hmono s x) s
    unfold dyadicValue
    rw [ENNReal.div_le_iff (two_pow_ne_zero' s) (two_pow_ne_top' s), div_eq_mul_inv, mul_right_comm,
      ← div_eq_mul_inv,
      ENNReal.le_div_iff_mul_le (Or.inl (two_pow_ne_zero' _)) (Or.inl (two_pow_ne_top' _))]
    have : ratFloor (approx s x) s * 2 ^ (s + 1) ≤ ratFloor (approx (s + 1) x) (s + 1) * 2 ^ s := by
      calc ratFloor (approx s x) s * 2 ^ (s + 1) = 2 * ratFloor (approx s x) s * 2 ^ s := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ h
    exact_mod_cast this
  · rw [← hsup x]
    apply le_antisymm
    · exact iSup_le fun s ↦ (dyadicValue_ratFloor_le _ s (hd s x)).trans
        (le_iSup (fun s ↦ ratVal (approx s x)) s)
    · refine iSup_le fun s₀ ↦ ?_
      refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ENNReal.coe_ne_zero.mpr hε.ne')
      have hmono' : Monotone (fun s ↦ ratVal (approx s x)) :=
        monotone_nat_of_le_succ (fun s ↦ hmono s x)
      calc ratVal (approx s₀ x) ≤ ratVal (approx (max s₀ n) x) := hmono' (le_max_left _ _)
        _ ≤ dyadicValue (ratFloor (approx (max s₀ n) x) (max s₀ n)) (max s₀ n)
              + 2⁻¹ ^ (max s₀ n) := ratVal_le_dyadicValue_ratFloor_add _ _ (hd _ x)
        _ ≤ (⨆ s, dyadicValue (ratFloor (approx s x) s) s) + ε := by
            gcongr
            · exact le_iSup (fun s ↦ dyadicValue (ratFloor (approx s x) s) s) (max s₀ n)
            · exact (pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two)
                (le_max_right s₀ n)).trans hn.le
  · exact Primrec.nat_div.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.fst.comp hcomp)
        (natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst))
      (Computable.snd.comp hcomp)

/-! ### Running maxima -/

/-- The larger of two rationals (ties go to the second). -/
def ratMax (q r : ℕ × ℕ) : ℕ × ℕ := if q.1 * r.2 ≤ r.1 * q.2 then r else q

theorem ratMax_primrec : Primrec (fun p : (ℕ × ℕ) × (ℕ × ℕ) ↦ ratMax p.1 p.2) :=
  Primrec.ite
    (Primrec.nat_le.comp
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst)))
    Primrec.snd Primrec.fst

theorem ratMax_den_pos {q r : ℕ × ℕ} (hq : 0 < q.2) (hr : 0 < r.2) : 0 < (ratMax q r).2 := by
  unfold ratMax; split_ifs <;> assumption

theorem ratVal_ratMax {q r : ℕ × ℕ} (hq : 0 < q.2) (hr : 0 < r.2) :
    ratVal (ratMax q r) = max (ratVal q) (ratVal r) := by
  unfold ratMax
  split_ifs with h
  · rw [max_eq_right ((ratVal_le_ratVal hq hr).mpr h)]
  · rw [max_eq_left ((ratVal_le_ratVal hr hq).mpr (by omega))]

/-- Running maximum of a sequence of rationals, as a `Nat.rec`. -/
def runMax (r : ℕ → BitString → ℕ × ℕ) (s : ℕ) (x : BitString) : ℕ × ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ × ℕ) (r 0 x) (fun k acc ↦ ratMax acc (r (k + 1) x)) s

theorem runMax_zero (r : ℕ → BitString → ℕ × ℕ) (x : BitString) : runMax r 0 x = r 0 x := rfl

theorem runMax_succ (r : ℕ → BitString → ℕ × ℕ) (s : ℕ) (x : BitString) :
    runMax r (s + 1) x = ratMax (runMax r s x) (r (s + 1) x) := rfl

theorem runMax_computable {r : ℕ → BitString → ℕ × ℕ}
    (hr : Computable (fun p : ℕ × BitString ↦ r p.1 p.2)) :
    Computable (fun p : ℕ × BitString ↦ runMax r p.1 p.2) := by
  have hg : Computable (fun p : ℕ × BitString ↦ r 0 p.2) :=
    hr.comp (Computable.pair (Computable.const 0) Computable.snd)
  have hh : Computable₂ (fun (p : ℕ × BitString) (q : ℕ × (ℕ × ℕ)) ↦
      ratMax q.2 (r (q.1 + 1) p.2)) := by
    have : Computable (fun a : (ℕ × BitString) × (ℕ × (ℕ × ℕ)) ↦
        ratMax a.2.2 (r (a.2.1 + 1) a.1.2)) :=
      (ratMax_primrec.to_comp.comp (Computable.pair (Computable.snd.comp Computable.snd)
        (hr.comp (Computable.pair (Computable.succ.comp (Computable.fst.comp Computable.snd))
          (Computable.snd.comp Computable.fst))))).of_eq (fun _ ↦ rfl)
    exact this
  exact (Computable.nat_rec Computable.fst hg hh).of_eq (fun p ↦ rfl)

theorem runMax_den_pos {r : ℕ → BitString → ℕ × ℕ} (hd : ∀ s x, 0 < (r s x).2) (s : ℕ)
    (x : BitString) : 0 < (runMax r s x).2 := by
  induction s with
  | zero => exact hd 0 x
  | succ s ih => rw [runMax_succ]; exact ratMax_den_pos ih (hd _ x)

theorem le_ratVal_runMax {r : ℕ → BitString → ℕ × ℕ} (hd : ∀ s x, 0 < (r s x).2) {k s : ℕ}
    (hk : k ≤ s) (x : BitString) : ratVal (r k x) ≤ ratVal (runMax r s x) := by
  induction s with
  | zero =>
    obtain rfl : k = 0 := by omega
    exact le_rfl
  | succ s ih =>
    rw [runMax_succ, ratVal_ratMax (runMax_den_pos hd s x) (hd _ x)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hk) with h | h
    · exact (ih (Nat.lt_succ_iff.mp h)).trans (le_max_left _ _)
    · rw [h]; exact le_max_right _ _

theorem ratVal_runMax_le {r : ℕ → BitString → ℕ × ℕ} (hd : ∀ s x, 0 < (r s x).2)
    {f : BitString → ℝ≥0∞} (hle : ∀ s x, ratVal (r s x) ≤ f x) (s : ℕ) (x : BitString) :
    ratVal (runMax r s x) ≤ f x := by
  induction s with
  | zero => exact hle 0 x
  | succ s ih =>
    rw [runMax_succ, ratVal_ratMax (runMax_den_pos hd s x) (hd _ x)]
    exact max_le ih (hle _ x)

/-- **Rational approximations from below with supremum `f` give lsc**, monotone or
not. -/
theorem IsLSC₁.of_ratSeq {f : BitString → ℝ≥0∞} (r : ℕ → BitString → ℕ × ℕ)
    (hd : ∀ s x, 0 < (r s x).2) (hle : ∀ s x, ratVal (r s x) ≤ f x)
    (hconv : ∀ x, f x ≤ ⨆ s, ratVal (r s x))
    (hcomp : Computable (fun p : ℕ × BitString ↦ r p.1 p.2)) : IsLSC₁ f := by
  refine IsLSC₁.of_ratApprox (runMax r) (runMax_den_pos hd) (fun s x ↦ ?_) (fun x ↦ ?_)
    (runMax_computable hcomp)
  · rw [runMax_succ, ratVal_ratMax (runMax_den_pos hd s x) (hd _ x)]
    exact le_max_left _ _
  · apply le_antisymm
    · exact iSup_le fun s ↦ ratVal_runMax_le hd hle s x
    · exact (hconv x).trans (iSup_le fun k ↦ (le_ratVal_runMax hd le_rfl x).trans
        (le_iSup (fun s ↦ ratVal (runMax r s x)) k))

/-! ### Products -/

theorem ratVal_mul_pow (a b s : ℕ) :
    ratVal (a * b, 2 ^ s * 2 ^ s) = dyadicValue a s * dyadicValue b s := by
  unfold ratVal dyadicValue
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (two_pow_ne_zero' s)) (Or.inl (two_pow_ne_top' s))]
  ring

/-- Suprema of two nondecreasing sequences multiply along the diagonal. -/
theorem iSup_mul_iSup_of_monotone {u v : ℕ → ℝ≥0∞} (hu : Monotone u) (hv : Monotone v) :
    (⨆ s, u s) * (⨆ s, v s) = ⨆ s, u s * v s := by
  apply le_antisymm
  · rw [ENNReal.iSup_mul]
    refine iSup_le fun s ↦ ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun t ↦ ?_
    calc u s * v t ≤ u (max s t) * v (max s t) := by
          gcongr
          · exact hu (le_max_left s t)
          · exact hv (le_max_right s t)
      _ ≤ ⨆ s, u s * v s := le_iSup (fun s ↦ u s * v s) (max s t)
  · exact iSup_le fun s ↦ by gcongr <;> exact le_iSup _ s

/-- **Products of lsc functions are lsc.** -/
theorem IsLSC₁.mul {f g : BitString → ℝ≥0∞} (hf : IsLSC₁ f) (hg : IsLSC₁ g) :
    IsLSC₁ (fun x ↦ f x * g x) := by
  obtain ⟨a, ha1, ha2, ha3⟩ := hf
  obtain ⟨b, hb1, hb2, hb3⟩ := hg
  refine IsLSC₁.of_ratApprox (fun s x ↦ (a s x * b s x, 2 ^ s * 2 ^ s))
    (fun s x ↦ by positivity) (fun s x ↦ ?_) (fun x ↦ ?_) ?_
  · rw [ratVal_mul_pow, ratVal_mul_pow]
    exact mul_le_mul' (ha1 s x) (hb1 s x)
  · simp only [ratVal_mul_pow]
    rw [← ha2 x, ← hb2 x]
    exact (iSup_mul_iSup_of_monotone (monotone_nat_of_le_succ (fun s ↦ ha1 s x))
      (monotone_nat_of_le_succ (fun s ↦ hb1 s x))).symm
  · exact Computable.pair (Primrec.nat_mul.to_comp.comp ha3 hb3)
      (Primrec.nat_mul.to_comp.comp
        (natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst)
        (natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst))

/-! ### Computable real-valued functions on strings -/

/-- **Computable function** `BitString → ℝ≥0∞` (Gács Definition 1.5.1): computable
rational lower and upper approximations, `2^{-k}` apart at precision `k`. -/
def IsComputableENNReal (f : BitString → ℝ≥0∞) : Prop :=
  ∃ lo hi : ℕ → BitString → ℕ × ℕ,
    (∀ k x, 0 < (lo k x).2 ∧ 0 < (hi k x).2) ∧
    Computable (fun p : ℕ × BitString ↦ lo p.1 p.2) ∧
    Computable (fun p : ℕ × BitString ↦ hi p.1 p.2) ∧
    ∀ k x, ratVal (lo k x) ≤ f x ∧ f x ≤ ratVal (hi k x) ∧
      ratVal (hi k x) ≤ ratVal (lo k x) + 2⁻¹ ^ k

/-- A computable function is lower semicomputable. -/
theorem IsComputableENNReal.isLSC₁ {f : BitString → ℝ≥0∞} (hf : IsComputableENNReal f) :
    IsLSC₁ f := by
  obtain ⟨lo, hi, hd, hlo, _, hb⟩ := hf
  refine IsLSC₁.of_ratSeq lo (fun k x ↦ (hd k x).1) (fun k x ↦ (hb k x).1) (fun x ↦ ?_) hlo
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ENNReal.coe_ne_zero.mpr hε.ne')
  calc f x ≤ ratVal (hi n x) := (hb n x).2.1
    _ ≤ ratVal (lo n x) + 2⁻¹ ^ n := (hb n x).2.2
    _ ≤ (⨆ s, ratVal (lo s x)) + ε := add_le_add (le_iSup (fun s ↦ ratVal (lo s x)) n) hn.le

/-- `2^{-(n+1)} + 2^{-(n+1)} = 2^{-n}`. -/
theorem inv_two_pow_succ_add_self (n : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ (n + 1) + 2⁻¹ ^ (n + 1) = 2⁻¹ ^ n := by
  rw [← two_mul, pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
    one_mul]

/-- The upper approximations, pushed up by `2^{-k}`, still converge to `f` and are
strictly positive rationals. -/
theorem IsComputableENNReal.iInf_hi {f : BitString → ℝ≥0∞} {lo hi : ℕ → BitString → ℕ × ℕ}
    (hb : ∀ k x, ratVal (lo k x) ≤ f x ∧ f x ≤ ratVal (hi k x) ∧
      ratVal (hi k x) ≤ ratVal (lo k x) + 2⁻¹ ^ k) (x : BitString) :
    ⨅ k, (ratVal (hi k x) + 2⁻¹ ^ k) = f x := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt (ENNReal.coe_ne_zero.mpr hε.ne')
    calc (⨅ k, (ratVal (hi k x) + 2⁻¹ ^ k)) ≤ ratVal (hi (n + 1) x) + 2⁻¹ ^ (n + 1) :=
          iInf_le (fun k ↦ ratVal (hi k x) + 2⁻¹ ^ k) (n + 1)
      _ ≤ (ratVal (lo (n + 1) x) + 2⁻¹ ^ (n + 1)) + 2⁻¹ ^ (n + 1) := by gcongr; exact (hb _ x).2.2
      _ = ratVal (lo (n + 1) x) + 2⁻¹ ^ n := by rw [add_assoc, inv_two_pow_succ_add_self]
      _ ≤ f x + ε := add_le_add (hb _ x).1 hn.le
  · exact le_iInf fun k ↦ le_self_add.trans' (hb k x).2.1

/-- The rational `d 2^k / (n 2^k + d)` is `(n/d + 2^{-k})⁻¹`. -/
theorem ratVal_inv_shift {n d k : ℕ} (hd : 0 < d) :
    ratVal (d * 2 ^ k, n * 2 ^ k + d) = (ratVal (n, d) + 2⁻¹ ^ k)⁻¹ := by
  unfold ratVal
  simp only
  push_cast
  have hd0 : (d : ℝ≥0∞) ≠ 0 := natCast_pos_ne_zero hd
  have hdT : (d : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top d
  have hsum : (n : ℝ≥0∞) / d + 2⁻¹ ^ k = ((n : ℝ≥0∞) * 2 ^ k + d) / (d * 2 ^ k) := by
    rw [← ENNReal.div_add_div_same,
      ENNReal.mul_div_mul_right _ _ (two_pow_ne_zero' k) (two_pow_ne_top' k)]
    congr 1
    rw [ENNReal.div_eq_inv_mul, ENNReal.mul_inv (Or.inl hd0) (Or.inl hdT), mul_comm (d : ℝ≥0∞)⁻¹,
      mul_assoc, ENNReal.inv_mul_cancel hd0 hdT, mul_one, ENNReal.inv_pow]
  rw [hsum, ENNReal.inv_div (Or.inl (ENNReal.mul_ne_top hdT (two_pow_ne_top' k)))
    (Or.inl (mul_ne_zero hd0 (two_pow_ne_zero' k)))]

/-- **The reciprocal of a computable function is lsc.** Lower approximations of `1/f`
come from upper approximations of `f`. -/
theorem IsComputableENNReal.inv_isLSC₁ {f : BitString → ℝ≥0∞} (hf : IsComputableENNReal f) :
    IsLSC₁ (fun x ↦ (f x)⁻¹) := by
  obtain ⟨lo, hi, hd, _, hhi, hb⟩ := hf
  set r : ℕ → BitString → ℕ × ℕ := fun k x ↦
    ((hi k x).2 * 2 ^ k, (hi k x).1 * 2 ^ k + (hi k x).2) with hr
  have hrval : ∀ k x, ratVal (r k x) = (ratVal (hi k x) + 2⁻¹ ^ k)⁻¹ := fun k x ↦
    ratVal_inv_shift (hd k x).2
  have hinf := IsComputableENNReal.iInf_hi hb
  refine IsLSC₁.of_ratSeq r (fun k x ↦ by simp only [hr]; have := (hd k x).2; positivity)
    (fun k x ↦ ?_) (fun x ↦ ?_) ?_
  · rw [hrval]
    exact ENNReal.inv_le_inv.mpr (le_self_add.trans' (hb k x).2.1)
  · simp only [hrval]
    rw [← hinf x, ENNReal.inv_iInf]
  · exact Computable.pair
      (Primrec.nat_mul.to_comp.comp (Computable.snd.comp hhi)
        (natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst))
      (Primrec.nat_add.to_comp.comp
        (Primrec.nat_mul.to_comp.comp (Computable.fst.comp hhi)
          (natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst))
        (Computable.snd.comp hhi))

end Kolmogorov.Randomness
