/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Information.NonIncrease

/-!
# Gács Remark 3.1.11: `I*(x : y) =⁺ log (m(x, y) / (m(x) m(y)))`

For a universal semimeasure `m`, multiplicatively and without division:
`2^{-c} m(x, y) ≤ 2^{I*(x:y)} m(x) m(y) ≤ 2^c m(x, y)` (`infoStar_eq_log_ratio`). This is the
coding theorem `m ≍ 2^{-K}` applied three times; it is what lets Gács read `I*(x : y)` as a
randomness deficiency of `(x, y)` with respect to `m × m`.
-/

namespace Kolmogorov.Information

open scoped ENNReal
open Kolmogorov.Randomness (exists_inv_two_pow_le_of_pos two_pow_ne_zero' two_pow_ne_top'
  le_two_pow_mul_of_inv)

variable {U : Map}

theorem inv_two_pow_eq_zpow (n : ℕ) : (2 : ℝ≥0∞)⁻¹ ^ n = 2 ^ (-(n : ℤ)) := by
  rw [ENNReal.zpow_neg, zpow_natCast, ENNReal.inv_pow]

theorem zpow_infoStar (x y : BitString) :
    (2 : ℝ≥0∞) ^ InfoStar U x y * (2⁻¹ ^ Ku U x * 2⁻¹ ^ Ku U y) = 2⁻¹ ^ Ku U (pairCode x y) := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  rw [inv_two_pow_eq_zpow, inv_two_pow_eq_zpow, inv_two_pow_eq_zpow,
    ← ENNReal.zpow_add h2 h2', ← ENNReal.zpow_add h2 h2']
  congr 1
  unfold InfoStar
  ring

/-- **Gács Remark 3.1.11.** `2^{-c} m(x,y) ≤ 2^{I*(x:y)} m(x) m(y) ≤ 2^c m(x,y)`. -/
theorem infoStar_eq_log_ratio {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, 2⁻¹ ^ c * m (pairCode x y) ≤ 2 ^ InfoStar U x y * (m x * m y) ∧
      2 ^ InfoStar U x y * (m x * m y) ≤ 2 ^ c * m (pairCode x y) := by
  obtain ⟨c1, c2, hc1, hc2, h1, h2⟩ := universalSemimeasure_equiv_prefixComplexity hm hU
  obtain ⟨e1, he1⟩ := exists_inv_two_pow_le_of_pos hc1
  obtain ⟨e2, he2⟩ := exists_inv_two_pow_le_of_pos hc2
  -- `m ≤ 2^{e1} 2^{-K}` and `2^{-e2} 2^{-K} ≤ m`
  have hup : ∀ x, m x ≤ 2 ^ e1 * 2⁻¹ ^ Ku U x := fun x ↦ by
    have := (mul_le_mul' he1 le_rfl).trans (h1 x)
    rw [prefixComplexityWeight, complexityWeight_KP hU] at this
    exact le_two_pow_mul_of_inv this
  have hlo : ∀ x, 2⁻¹ ^ e2 * 2⁻¹ ^ Ku U x ≤ m x := fun x ↦ by
    have := (mul_le_mul' he2 le_rfl).trans (h2 x)
    rwa [prefixComplexityWeight, complexityWeight_KP hU] at this
  refine ⟨2 * e1 + 2 * e2, fun x y ↦ ⟨?_, ?_⟩⟩
  · calc 2⁻¹ ^ (2 * e1 + 2 * e2) * m (pairCode x y)
        ≤ 2⁻¹ ^ (2 * e1 + 2 * e2) * (2 ^ e1 * 2⁻¹ ^ Ku U (pairCode x y)) :=
          mul_le_mul' le_rfl (hup _)
      _ ≤ 2⁻¹ ^ (2 * e2) * 2⁻¹ ^ Ku U (pairCode x y) := by
          rw [← mul_assoc]
          refine mul_le_mul' ?_ le_rfl
          rw [show 2 * e1 + 2 * e2 = e1 + (e1 + 2 * e2) by ring, pow_add, mul_comm,
            ← mul_assoc, ← ENNReal.inv_pow (n := e1),
            ENNReal.mul_inv_cancel (two_pow_ne_zero' _) (two_pow_ne_top' _), one_mul]
          exact pow_le_pow_right_of_le_one' (by norm_num) (by omega)
      _ = 2 ^ InfoStar U x y * ((2⁻¹ ^ e2 * 2⁻¹ ^ Ku U x) * (2⁻¹ ^ e2 * 2⁻¹ ^ Ku U y)) := by
          rw [← zpow_infoStar x y, two_mul, pow_add]; ring
      _ ≤ 2 ^ InfoStar U x y * (m x * m y) :=
          mul_le_mul' le_rfl (mul_le_mul' (hlo x) (hlo y))
  · calc 2 ^ InfoStar U x y * (m x * m y)
        ≤ 2 ^ InfoStar U x y * ((2 ^ e1 * 2⁻¹ ^ Ku U x) * (2 ^ e1 * 2⁻¹ ^ Ku U y)) :=
          mul_le_mul' le_rfl (mul_le_mul' (hup x) (hup y))
      _ = 2 ^ (2 * e1) * 2⁻¹ ^ Ku U (pairCode x y) := by
          rw [← zpow_infoStar x y, two_mul, pow_add]; ring
      _ ≤ 2 ^ (2 * e1) * (2 ^ e2 * m (pairCode x y)) :=
          mul_le_mul' le_rfl (le_two_pow_mul_of_inv (hlo _))
      _ ≤ 2 ^ (2 * e1 + 2 * e2) * m (pairCode x y) := by
          rw [← mul_assoc, ← pow_add]
          exact mul_le_mul' (pow_le_pow_right₀ one_le_two (by omega)) le_rfl

end Kolmogorov.Information
