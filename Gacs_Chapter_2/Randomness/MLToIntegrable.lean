/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.ComputableMeasure

/-!
# Gács Proposition 2.2.3, second half: from probability-bounded to integrable tests

If `d` is a probability-bounded test then `d − 2 log d − c` is an integrable test. We
prove the multiplicative version with the weights

  `w_k = 2^k / ((k+1)(k+2))`,   `∑_k w_k · 2^{-k} = ∑_k 1/((k+1)(k+2)) = 1`,

whose series telescopes exactly, so no constant `c` is needed. Given a probability-bounded
`t`, the corrected test is

  `t'(x) = sup { w_k : 2^k < t(x) }`,

which is lower semicomputable (the admissible `k` are enumerated from the approximations
of `t`), has expectation `∑_k w_k · P{t > 2^k} ≤ ∑_k w_k 2^{-k} = 1`, and satisfies
`t ≤ 2 (k+1)(k+2) · t'` on the level `2^k < t ≤ 2^{k+1}`, i.e. `d' ≥ d − 2 log(d + 2) − 1`.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The weights and the corrected test -/

/-- `w_k = 2^k / ((k+1)(k+2))`. -/
noncomputable def mlWeight (k : ℕ) : ℝ≥0∞ := (2 : ℝ≥0∞) ^ k / (((k + 1) * (k + 2) : ℕ) : ℝ≥0∞)

theorem ratVal_mlWeight (k : ℕ) : ratVal (2 ^ k, (k + 1) * (k + 2)) = mlWeight k := by
  unfold ratVal mlWeight; push_cast; rfl

/-- **The corrected test** `t'(x) = sup {w_k : 2^k < t x}`. -/
noncomputable def mlCorrected (t : BitString → ℝ≥0∞) (x : BitString) : ℝ≥0∞ :=
  ⨆ k : ℕ, if (2 : ℝ≥0∞) ^ k < t x then mlWeight k else 0

theorem mlWeight_le_mlCorrected {t : BitString → ℝ≥0∞} {x : BitString} {k : ℕ}
    (h : (2 : ℝ≥0∞) ^ k < t x) : mlWeight k ≤ mlCorrected t x := by
  unfold mlCorrected
  refine le_iSup_of_le k ?_
  rw [if_pos h]

theorem two_pow_lt_dyadicValue_iff (k a s : ℕ) :
    (2 : ℝ≥0∞) ^ k < dyadicValue a s ↔ 2 ^ k * 2 ^ s < a := by
  unfold dyadicValue
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl (two_pow_ne_zero' s)) (Or.inl (two_pow_ne_top' s))]
  exact_mod_cast Iff.rfl

/-! ### The best admissible weight at a stage -/

/-- Among `k < n`, the largest weight `w_k` with `2^k < a_s(x)/2^s`, as a rational. -/
def bestW (a : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) (n : ℕ) : ℕ × ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ × ℕ) (0, 1)
    (fun k acc ↦ if 2 ^ k * 2 ^ s < a s x then ratMax acc (2 ^ k, (k + 1) * (k + 2)) else acc) n

theorem bestW_succ (a : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) (n : ℕ) :
    bestW a s x (n + 1)
      = if 2 ^ n * 2 ^ s < a s x then ratMax (bestW a s x n) (2 ^ n, (n + 1) * (n + 2))
        else bestW a s x n := rfl

theorem bestW_den_pos (a : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) (n : ℕ) :
    0 < (bestW a s x n).2 := by
  induction n with
  | zero => exact Nat.one_pos
  | succ n ih =>
    rw [bestW_succ]
    split_ifs
    · exact ratMax_den_pos ih (by positivity)
    · exact ih

theorem ratVal_bestW_le {a : ℕ → BitString → ℕ} {t : BitString → ℝ≥0∞}
    (hle : ∀ s x, dyadicValue (a s x) s ≤ t x) (s : ℕ) (x : BitString) (n : ℕ) :
    ratVal (bestW a s x n) ≤ mlCorrected t x := by
  induction n with
  | zero => simp [bestW, ratVal]
  | succ n ih =>
    rw [bestW_succ]
    split_ifs with h
    · rw [ratVal_ratMax (bestW_den_pos a s x n) (by positivity), ratVal_mlWeight]
      exact max_le ih (mlWeight_le_mlCorrected
        (((two_pow_lt_dyadicValue_iff _ _ _).mpr h).trans_le (hle s x)))
    · exact ih

theorem mlWeight_le_ratVal_bestW {a : ℕ → BitString → ℕ} {s : ℕ} {x : BitString} {k n : ℕ}
    (hk : k < n) (hadm : 2 ^ k * 2 ^ s < a s x) : mlWeight k ≤ ratVal (bestW a s x n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [bestW_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
    · have := ih h
      split_ifs
      · rw [ratVal_ratMax (bestW_den_pos a s x n) (by positivity)]
        exact this.trans (le_max_left _ _)
      · exact this
    · subst h
      rw [if_pos hadm, ratVal_ratMax (bestW_den_pos a s x k) (by positivity), ratVal_mlWeight]
      exact le_max_right _ _

theorem bestW_computable {a : ℕ → BitString → ℕ}
    (ha : Computable (fun p : ℕ × BitString ↦ a p.1 p.2)) :
    Computable (fun p : ℕ × BitString ↦ bestW a p.1 p.2 (p.1 + 1)) := by
  have hh : Computable₂ (fun (p : ℕ × BitString) (q : ℕ × (ℕ × ℕ)) ↦
      if 2 ^ q.1 * 2 ^ p.1 < a p.1 p.2 then ratMax q.2 (2 ^ q.1, (q.1 + 1) * (q.1 + 2))
      else q.2) := by
    have htest : Computable (fun r : (ℕ × BitString) × (ℕ × (ℕ × ℕ)) ↦
        decide (2 ^ r.2.1 * 2 ^ r.1.1 < a r.1.1 r.1.2)) :=
      (natLt_primrec.to_comp.comp (Computable.pair
        (Primrec.nat_mul.to_comp.comp
          (natPow_primrec.to_comp.comp (Computable.const 2) (Computable.fst.comp Computable.snd))
          (natPow_primrec.to_comp.comp (Computable.const 2) (Computable.fst.comp Computable.fst)))
        (ha.comp Computable.fst))).of_eq (fun _ ↦ rfl)
    have hmax : Computable (fun r : (ℕ × BitString) × (ℕ × (ℕ × ℕ)) ↦
        ratMax r.2.2 (2 ^ r.2.1, (r.2.1 + 1) * (r.2.1 + 2))) :=
      (ratMax_primrec.to_comp.comp (Computable.pair (Computable.snd.comp Computable.snd)
        (Computable.pair
          (natPow_primrec.to_comp.comp (Computable.const 2) (Computable.fst.comp Computable.snd))
          (Primrec.nat_mul.to_comp.comp (Computable.succ.comp (Computable.fst.comp Computable.snd))
            (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd)
              (Computable.const 2)))))).of_eq (fun _ ↦ rfl)
    have : Computable (fun r : (ℕ × BitString) × (ℕ × (ℕ × ℕ)) ↦
        if 2 ^ r.2.1 * 2 ^ r.1.1 < a r.1.1 r.1.2
          then ratMax r.2.2 (2 ^ r.2.1, (r.2.1 + 1) * (r.2.1 + 2)) else r.2.2) :=
      (Computable.cond htest hmax (Computable.snd.comp Computable.snd)).of_eq
        (fun _ ↦ Bool.cond_decide _ _ _)
    exact this
  exact (Computable.nat_rec (Computable.succ.comp Computable.fst) (Computable.const (0, 1))
    hh).of_eq (fun _ ↦ rfl)

/-- **The corrected test is lower semicomputable.** -/
theorem mlCorrected_isLSC₁ {t : BitString → ℝ≥0∞} (ht : IsLSC₁ t) : IsLSC₁ (mlCorrected t) := by
  obtain ⟨a, hmono, hsup, ha⟩ := ht
  have hle : ∀ s x, dyadicValue (a s x) s ≤ t x := fun s x ↦ by
    rw [← hsup x]; exact le_iSup (fun s ↦ dyadicValue (a s x) s) s
  refine IsLSC₁.of_ratSeq (fun s x ↦ bestW a s x (s + 1)) (fun s x ↦ bestW_den_pos a s x _)
    (fun s x ↦ ratVal_bestW_le hle s x _) (fun x ↦ ?_) (bestW_computable ha)
  unfold mlCorrected
  refine iSup_le fun k ↦ ?_
  split_ifs with hk
  · rw [← hsup x, lt_iSup_iff] at hk
    obtain ⟨s₀, hs₀⟩ := hk
    have hmono' : Monotone (fun s ↦ dyadicValue (a s x) s) :=
      monotone_nat_of_le_succ (fun s ↦ hmono s x)
    have hadm : 2 ^ k * 2 ^ (max s₀ k) < a (max s₀ k) x :=
      (two_pow_lt_dyadicValue_iff _ _ _).mp (hs₀.trans_le (hmono' (le_max_left s₀ k)))
    exact (mlWeight_le_ratVal_bestW (by omega : k < max s₀ k + 1) hadm).trans
      (le_iSup (fun s ↦ ratVal (bestW a s x (s + 1))) (max s₀ k))
  · exact zero_le

/-! ### The telescoping series -/

theorem inv_step (n : ℕ) :
    (1 : ℝ≥0∞) / (((n + 1) * (n + 2) : ℕ) : ℝ≥0∞) + 1 / ((n + 1 + 1 : ℕ) : ℝ≥0∞)
      = 1 / ((n + 1 : ℕ) : ℝ≥0∞) := by
  set A : ℝ≥0∞ := ((n + 1 : ℕ) : ℝ≥0∞) with hA
  set B : ℝ≥0∞ := ((n + 2 : ℕ) : ℝ≥0∞) with hB
  have hA0 : A ≠ 0 := by rw [hA]; exact_mod_cast Nat.succ_ne_zero n
  have hAT : A ≠ ⊤ := ENNReal.natCast_ne_top _
  have hB0 : B ≠ 0 := by rw [hB]; exact_mod_cast Nat.succ_ne_zero (n + 1)
  have hBT : B ≠ ⊤ := ENNReal.natCast_ne_top _
  have hAB : (((n + 1) * (n + 2) : ℕ) : ℝ≥0∞) = A * B := by rw [hA, hB]; push_cast; ring
  have h1B : (1 : ℝ≥0∞) + A = B := by rw [hA, hB]; push_cast; ring
  rw [hAB]
  calc (1 : ℝ≥0∞) / (A * B) + 1 / B = 1 / (A * B) + A / (A * B) := by
        congr 1
        rw [← ENNReal.mul_div_mul_left 1 B hA0 hAT, mul_one]
    _ = (1 + A) / (A * B) := ENNReal.div_add_div_same
    _ = B / (A * B) := by rw [h1B]
    _ = 1 / A := by rw [← ENNReal.mul_div_mul_right 1 A hB0 hBT, one_mul]

theorem sum_range_inv_add_tail (n : ℕ) :
    ∑ k ∈ Finset.range n, (1 : ℝ≥0∞) / (((k + 1) * (k + 2) : ℕ) : ℝ≥0∞)
      + 1 / ((n + 1 : ℕ) : ℝ≥0∞) = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_assoc, inv_step, ih]

/-- `∑_k 1/((k+1)(k+2)) ≤ 1` (in fact `= 1`). -/
theorem tsum_inv_succ_mul_le_one :
    ∑' k : ℕ, (1 : ℝ≥0∞) / (((k + 1) * (k + 2) : ℕ) : ℝ≥0∞) ≤ 1 :=
  ENNReal.tsum_le_of_sum_range_le fun n ↦ le_self_add.trans (sum_range_inv_add_tail n).le

theorem mlWeight_mul_inv_two_pow (k : ℕ) :
    mlWeight k * 2⁻¹ ^ k = 1 / (((k + 1) * (k + 2) : ℕ) : ℝ≥0∞) := by
  unfold mlWeight
  rw [div_eq_mul_inv, mul_right_comm, ← ENNReal.inv_pow,
    ENNReal.mul_inv_cancel (two_pow_ne_zero' k) (two_pow_ne_top' k), one_mul, one_div]

/-! ### Proposition 2.2.3, second half -/

/-- The expectation of the corrected test is at most one. -/
theorem tsum_mul_mlCorrected_le {P : ComputableMeasure} {t : BitString → ℝ≥0∞}
    (h : IsMLTest P t) : ∑' x, P.mass x * mlCorrected t x ≤ 1 := by
  have hpt : ∀ x, P.mass x * mlCorrected t x
      ≤ ∑' k, mlWeight k * ({x | (2 : ℝ≥0∞) ^ k < t x}).indicator P.mass x := by
    intro x
    unfold mlCorrected
    rw [ENNReal.mul_iSup]
    refine iSup_le fun k ↦ le_trans ?_ (ENNReal.le_tsum k)
    split_ifs with hk
    · rw [Set.indicator_of_mem (show x ∈ {x | (2 : ℝ≥0∞) ^ k < t x} from hk), mul_comm]
    · rw [mul_zero]; exact zero_le
  calc ∑' x, P.mass x * mlCorrected t x
      ≤ ∑' x, ∑' k, mlWeight k * ({x | (2 : ℝ≥0∞) ^ k < t x}).indicator P.mass x :=
        ENNReal.tsum_le_tsum hpt
    _ = ∑' k, mlWeight k * P.measureOf {x | (2 : ℝ≥0∞) ^ k < t x} := by
        rw [ENNReal.tsum_comm]
        exact tsum_congr (fun k ↦ ENNReal.tsum_mul_left)
    _ ≤ ∑' k, mlWeight k * 2⁻¹ ^ k := ENNReal.tsum_le_tsum (fun k ↦ mul_le_mul' le_rfl (h.2 k))
    _ = ∑' k, (1 : ℝ≥0∞) / (((k + 1) * (k + 2) : ℕ) : ℝ≥0∞) :=
        tsum_congr (fun k ↦ mlWeight_mul_inv_two_pow k)
    _ ≤ 1 := tsum_inv_succ_mul_le_one

/-- **Gács Proposition 2.2.3 (b), test part.** The corrected test of a probability-bounded
test is an integrable test. -/
theorem IsMLTest.mlCorrected_isIntegrableTest {P : ComputableMeasure} {t : BitString → ℝ≥0∞}
    (h : IsMLTest P t) : IsIntegrableTest P (mlCorrected t) :=
  ⟨mlCorrected_isLSC₁ h.1, tsum_mul_mlCorrected_le h⟩

/-- **Gács Proposition 2.2.3 (b), size part.** On the level `2^k < t ≤ 2^{k+1}`,
`t ≤ 2 (k+1)(k+2) · t'`, i.e. `d' ≥ d − 2 log (d + 2) − 1`. -/
theorem le_mul_mlCorrected {t : BitString → ℝ≥0∞} {x : BitString} {k : ℕ}
    (h1 : (2 : ℝ≥0∞) ^ k < t x) (h2 : t x ≤ 2 ^ (k + 1)) :
    t x ≤ 2 * (((k + 1) * (k + 2) : ℕ) : ℝ≥0∞) * mlCorrected t x := by
  have hD0 : (((k + 1) * (k + 2) : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos (k + 1))).ne'
  have hDT : (((k + 1) * (k + 2) : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  calc t x ≤ 2 ^ (k + 1) := h2
    _ = 2 * ((((k + 1) * (k + 2) : ℕ) : ℝ≥0∞) * mlWeight k) := by
        unfold mlWeight
        rw [mul_comm (((k + 1) * (k + 2) : ℕ) : ℝ≥0∞), ENNReal.div_mul_cancel hD0 hDT, pow_succ,
          mul_comm]
    _ ≤ 2 * ((((k + 1) * (k + 2) : ℕ) : ℝ≥0∞) * mlCorrected t x) := by
        gcongr
        exact mlWeight_le_mlCorrected h1
    _ = 2 * (((k + 1) * (k + 2) : ℕ) : ℝ≥0∞) * mlCorrected t x := by ring

end Kolmogorov
