/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Classical.Entropy
import Gacs_Chapter_2.Randomness.Descriptions

/-!
# Entropy as expected complexity (Gács Theorem 3.1.3)

For a computable probability distribution `P` on strings,

  `H(P) ≤ ∑ₓ P(x) K(x) ≤⁺ H(P) + K(P)`,

where `K(P)` is the prefix complexity of a description `y_P` of `P` (Chapter 2's
`IsLSCDescription`; only lower approximations of `P` are needed), and the constant is
universal (independent of `P`).

* Lower bound (`entropy_le_expectedComplexity`): Gibbs' inequality with the lengths `K(x)`,
  which satisfy Kraft's inequality `∑ 2^{-K(x)} ≤ 1`.
* Upper bound (`expectedComplexity_le`): the exact coding theorem of Chapter 2,
  `2^{-K(y_P)} P(x) ≤ 2^c 2^{-K(x)}` (`semimeasure_le_exact`), gives
  `K(x) ≤ −log₂ P(x) + K(y_P) + c` whenever `P(x) > 0`; multiply by `P(x)` and sum.

Complexities are the natural numbers `(KP U x []).toNat`, finite for an optimal `U`.
-/

namespace Kolmogorov.Information.Classical

open scoped ENNReal
open Kolmogorov.Randomness

/-- Kraft's inequality for prefix complexity, in terms of the natural lengths `K(x)`. -/
theorem tsum_inv_two_pow_KP_le_one (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∑' x, (2 : ℝ≥0∞)⁻¹ ^ (KP U x []).toNat ≤ 1 := by
  refine le_trans (le_of_eq (tsum_congr fun x ↦ ?_))
    (KP_kraft_sum_le_one U hU.isPrefixDecompressor [])
  obtain ⟨k, hk, -⟩ := exists_weight_eq U hU x
  rw [hk, ENat.toNat_coe, complexityWeight_coe]

/-- **Gács Theorem 3.1.3, lower bound.** `H(P) ≤ ∑ₓ P(x) K(x)`. -/
theorem entropy_le_expectedComplexity (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableMeasure) :
    entropy P.mass ≤ ∑' x, P.mass x * ((KP U x []).toNat : ℝ≥0∞) :=
  entropy_le_tsum_mul_length P.mass P.tsum_eq _ (tsum_inv_two_pow_KP_le_one U hU)

/-- From `2^{-k_y} ρ ≤ 2^c 2^{-k_x}` to `k_x ≤ −log₂ ρ + k_y + c`. -/
theorem length_le_of_dom {ρ : ℝ} (hρ : 0 < ρ) {kx ky c : ℕ}
    (h : (2 : ℝ)⁻¹ ^ ky * ρ ≤ 2 ^ c * (2 : ℝ)⁻¹ ^ kx) :
    (kx : ℝ) ≤ -Real.logb 2 ρ + ky + c := by
  have h1 := Real.logb_le_logb_of_le one_lt_two (by positivity) h
  rw [Real.logb_mul (by positivity) hρ.ne', Real.logb_mul (by positivity) (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_pow, Real.logb_inv,
    Real.logb_self_eq_one one_lt_two] at h1
  linarith

/-- The termwise upper bound `P(x) K(x) ≤ −P(x) log₂ P(x) + P(x) (K(y) + c)`. -/
theorem mass_mul_length_le {p : ℝ≥0∞} (hp : p ≤ 1) {kx ky c : ℕ}
    (hdom : (2 : ℝ≥0∞)⁻¹ ^ ky * p ≤ 2 ^ c * (2 : ℝ≥0∞)⁻¹ ^ kx) :
    p * (kx : ℝ≥0∞) ≤ ENNReal.ofReal (Real.negMulLog p.toReal / Real.log 2)
      + p * ((ky : ℝ≥0∞) + c) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  obtain ⟨ρ, hρ0, hρ1, rfl⟩ := exists_ofReal_of_le_one hp
  have hρ : 0 < ρ := by
    rcases hρ0.eq_or_lt with h | h
    · exact absurd (by rw [← h]; simp) hp0
    · exact h
  have hreal : (2 : ℝ)⁻¹ ^ ky * ρ ≤ 2 ^ c * (2 : ℝ)⁻¹ ^ kx := by
    have hfin : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ kx ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofNat_ne_top)
        (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero))
    have := ENNReal.toReal_mono hfin hdom
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hρ0] using this
  have hk := length_le_of_dom hρ hreal
  rw [ENNReal.toReal_ofReal hρ0, ← ENNReal.ofReal_natCast kx, ← ENNReal.ofReal_mul hρ0,
    show ((ky : ℝ≥0∞) + c) = ENNReal.ofReal ((ky : ℝ) + c) by
      rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_natCast],
    ← ENNReal.ofReal_mul hρ0,
    ← ENNReal.ofReal_add (div_nonneg (Real.negMulLog_nonneg hρ0 hρ1) log_two_pos'.le)
      (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : Real.negMulLog ρ / Real.log 2 + ρ * ((ky : ℝ) + c)
      = ρ * (-Real.logb 2 ρ + ky + c) := by
    unfold Real.negMulLog Real.logb; ring
  rw [e]
  exact mul_le_mul_of_nonneg_left hk hρ0

/-- **Gács Theorem 3.1.3, upper bound.** There is a universal `c` such that for every computable
probability distribution `P` with description `y_P`,
`∑ₓ P(x) K(x) ≤ H(P) + K(y_P) + c`. -/
theorem expectedComplexity_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : ComputableMeasure) (yP : BitString), IsLSCDescription yP P.mass →
      ∑' x, P.mass x * ((KP U x []).toNat : ℝ≥0∞)
        ≤ entropy P.mass + ((KP U yP []).toNat : ℝ≥0∞) + c := by
  obtain ⟨c, hc⟩ := semimeasure_le_exact U hU
  refine ⟨c, fun P yP hy ↦ ?_⟩
  have hsemi : IsSemimeasure P.mass := P.tsum_eq.le
  obtain ⟨ky, hky, hwy⟩ := exists_weight_eq U hU yP
  rw [hky, ENat.toNat_coe]
  calc ∑' x, P.mass x * ((KP U x []).toNat : ℝ≥0∞)
      ≤ ∑' x, (ENNReal.ofReal (Real.negMulLog (P.mass x).toReal / Real.log 2)
          + P.mass x * ((ky : ℝ≥0∞) + c)) := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        obtain ⟨kx, hkx, hwx⟩ := exists_weight_eq U hU x
        have h := hc P.mass yP hsemi hy x
        rw [hwy, hwx] at h
        rw [hkx, ENat.toNat_coe]
        exact mass_mul_length_le (P.mass_le_one x) h
    _ = entropy P.mass + ((ky : ℝ≥0∞) + c) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, P.tsum_eq, one_mul]; rfl
    _ = entropy P.mass + (ky : ℝ≥0∞) + c := by rw [add_assoc]

/-- **Gács Theorem 3.1.3.** For a computable distribution `P` with description `y_P`:
`H(P) ≤ ∑ₓ P(x) K(x) ≤ H(P) + K(y_P) + c`, with `c` universal. -/
theorem entropy_expectedComplexity (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : ComputableMeasure) (yP : BitString), IsLSCDescription yP P.mass →
      entropy P.mass ≤ ∑' x, P.mass x * ((KP U x []).toNat : ℝ≥0∞) ∧
        ∑' x, P.mass x * ((KP U x []).toNat : ℝ≥0∞)
          ≤ entropy P.mass + ((KP U yP []).toNat : ℝ≥0∞) + c := by
  obtain ⟨c, hc⟩ := expectedComplexity_le U hU
  exact ⟨c, fun P yP hy ↦ ⟨entropy_le_expectedComplexity U hU P, hc P yP hy⟩⟩

end Kolmogorov.Information.Classical
