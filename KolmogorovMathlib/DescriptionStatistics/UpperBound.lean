/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.LengthPairMachine
import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin

/-!
# Theorem 1.7.1, upper half: `2^{-n} · f(x, n) ≤× m(x, n)`

This file proves the `≤×` direction of Gács' Theorem 1.7.1 (`thm:Hstat`) for an
optimal prefix decompressor `U`: the a priori mass carried by the length-`n`
programs for `x` is dominated, up to a constant independent of `x` and `n`, by
the a priori probability of the pair `⟨x, n⟩`. In the notation of the
formalization,

  `2^{-n} · progCount U x n ≤ 2^c · aprioriMeasure U (pairCode x (natCode n)) []`.

Gács' informal reading: *if an object has many descriptions of one length, then
the pair of the object with that length has a short description*.

The proof is pure assembly:

* `progSlice_eq_progCount` identifies the left side with the slice
  `progSlice U x n`;
* `progSlice_le_aprioriMeasure_progLenMap` moves the slice under the a priori
  measure of the length-pairing machine `progLenMap U`, evaluated at the pair;
* the coding theorem, in its two halves `aprioriMeasure_le_complexityWeight_optimal`
  (`m_M ≤× 2^{-K_U}`) and `complexityWeight_KP_le_aprioriMeasure`
  (`2^{-K_U} ≤ m_U`), transfers that mass from `progLenMap U` to `U` itself
  (`aprioriMeasure_le_two_pow_mul_aprioriMeasure_optimal`).

No hypothesis on `n` is needed: this half of the theorem is unconditional, and
in the multiplicative form the degenerate case `f(x, n) = 0` is harmless.

The companion lower bound `m(x, n) ≤× 2^{-n} · f(x, n)` requires a padding
construction and a stronger, prefix-prepending form of universality; it is not
part of this file.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The coding theorem as a domination statement between machines -/

/-- **Optimal transfer of a priori mass.** For an optimal prefix decompressor `U`
and any prefix decompressor `M`, the a priori semimeasure of `M` is dominated by
that of `U` up to a constant: `m_M(x | y) ≤ 2^c · m_U(x | y)`.

This is the two-sided coding theorem assembled into a single inequality:
`2^{-c} · m_M ≤ 2^{-K_U} ≤ m_U`, then multiplied through by `2^c`. -/
theorem aprioriMeasure_le_two_pow_mul_aprioriMeasure_optimal {U : Map}
    (hU : IsOptimalPrefixConditional U) {M : Map} (hM : IsPrefixDecompressor M) :
    ∃ c : ℕ, ∀ x y : BitString,
      aprioriMeasure M x y ≤ (2 : ℝ≥0∞) ^ c * aprioriMeasure U x y := by
  obtain ⟨c, hc⟩ := aprioriMeasure_le_complexityWeight_optimal hU hM
  refine ⟨c, fun x y ↦ ?_⟩
  have h : (2 : ℝ≥0∞)⁻¹ ^ c * aprioriMeasure M x y ≤ aprioriMeasure U x y :=
    (hc x y).trans (complexityWeight_KP_le_aprioriMeasure U x y)
  have hcc : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ c = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  calc aprioriMeasure M x y
      = (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹ ^ c * aprioriMeasure M x y) := by
        rw [← mul_assoc, hcc, one_mul]
    _ ≤ (2 : ℝ≥0∞) ^ c * aprioriMeasure U x y := by gcongr

/-! ### The upper bound -/

/-- **Theorem 1.7.1, upper half (`≤×`).** For an optimal prefix decompressor `U`
there is a constant `c` such that, for every string `x` and every length `n`,

  `2^{-n} · f(x, n) ≤ 2^c · m(x, n)`,

where `f(x, n) = progCount U x n` counts the length-`n` programs for `x` and
`m(x, n) = aprioriMeasure U (pairCode x (natCode n)) []` is the a priori
probability of the pair. The constant depends only on `U`. -/
theorem progCount_le_aprioriMeasure_pair (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ),
      (2 : ℝ≥0∞)⁻¹ ^ n * (progCount U x n : ℝ≥0∞)
        ≤ (2 : ℝ≥0∞) ^ c * aprioriMeasure U (pairCode x (natCode n)) [] := by
  obtain ⟨c, hc⟩ := aprioriMeasure_le_two_pow_mul_aprioriMeasure_optimal hU
    (progLenMap_isPrefixDecompressor U hU.isPrefixDecompressor)
  refine ⟨c, fun x n ↦ ?_⟩
  calc (2 : ℝ≥0∞)⁻¹ ^ n * (progCount U x n : ℝ≥0∞)
      = progSlice U x n := (progSlice_eq_progCount U x n).symm
    _ ≤ aprioriMeasure (progLenMap U) (pairCode x (natCode n)) [] :=
        progSlice_le_aprioriMeasure_progLenMap U x n
    _ ≤ (2 : ℝ≥0∞) ^ c * aprioriMeasure U (pairCode x (natCode n)) [] := hc _ _

end Kolmogorov
