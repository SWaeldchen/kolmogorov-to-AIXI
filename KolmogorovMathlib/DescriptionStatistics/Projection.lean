/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.UpperBound
import KolmogorovMathlib.DescriptionStatistics.ShortestDescriptions
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Prefix.Properties
import KolmogorovMathlib.Prefix.Symmetry

/-!
# Lemma 1.7.3: `Σ_y m(x, y) =× m(x)`

Gács' Lemma 1.7.3 (source line 2124): summing the a priori probability of the pair
`⟨x, y⟩` over all second components `y` recovers, up to a constant factor, the a
priori probability of `x` alone.

The repository's `pairMarginal U x z = ∑' y, aprioriMeasure U (pairCode x y) z`
(`AlgorithmicProbability/PairMarginal.lean`) is literally the left-hand side.

* **`≤×`**: the marginal is a semimeasure dominated by the first-component
  projection machine (`pairMarginal_le_aprioriMeasure_projMap`), and the optimal
  transfer `aprioriMeasure_le_two_pow_mul_aprioriMeasure_optimal` moves that to `U`.
* **`≥×`**: Gács' one-line argument `m(x) =× m(x, x) ≤ Σ_y m(x, y)`. The identity
  `K(x, x) =⁺ K(x)` supplies `m(x) ≤× m(x, x)` through the coding theorem, and the
  term `y = x` sits under the sum.

Everything here is assembly; no new machines are built.
-/

namespace Kolmogorov

open scoped ENNReal

/-- **Lemma 1.7.3, `≤×` half.** `Σ_y m(⟨x, y⟩) ≤ 2^c · m(x)`. -/
theorem pairMarginal_le_two_pow_mul_aprioriMeasure (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString,
      pairMarginal U x [] ≤ (2 : ℝ≥0∞) ^ c * aprioriMeasure U x [] := by
  obtain ⟨c, hc⟩ := aprioriMeasure_le_two_pow_mul_aprioriMeasure_optimal hU
    (projMap_isPrefixDecompressor U hU.isPrefixDecompressor)
  exact ⟨c, fun x ↦ (pairMarginal_le_aprioriMeasure_projMap U x []).trans (hc x [])⟩

/-- **Lemma 1.7.3, `≥×` half.** `m(x) ≤ 2^c · Σ_y m(⟨x, y⟩)`, via the term `y = x`. -/
theorem aprioriMeasure_le_two_pow_mul_pairMarginal (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString,
      aprioriMeasure U x [] ≤ (2 : ℝ≥0∞) ^ c * pairMarginal U x [] := by
  obtain ⟨c₁, hc₁⟩ := aprioriMeasure_le_complexityWeight_optimal hU hU.isPrefixDecompressor
  obtain ⟨c₂, hc₂⟩ := KPPair_self_le_KPPlain U hU
  refine ⟨c₁ + c₂, fun x ↦ ?_⟩
  -- `m(x) ≤ 2^{c₁} · 2^{-K(x)}` (coding theorem, hard half).
  have h1 : aprioriMeasure U x [] ≤ (2 : ℝ≥0∞) ^ c₁ * complexityWeight (KPPlain U x) :=
    le_two_pow_mul_of_inv_two_pow_mul_le (hc₁ x [])
  -- `2^{-K(x)} ≤ 2^{c₂} · 2^{-K(x,x)}` from `K(x,x) ≤ K(x) + c₂`.
  have h2 : complexityWeight (KPPlain U x)
      ≤ (2 : ℝ≥0∞) ^ c₂ * complexityWeight (KPPair U x x) := by
    have h := complexityWeight_le_of_le (hc₂ x)
    rw [complexityWeight_add_nat, mul_comm] at h
    exact le_two_pow_mul_of_inv_two_pow_mul_le h
  -- `2^{-K(x,x)} ≤ m(⟨x,x⟩)` (coding theorem, easy half).
  have h3 : complexityWeight (KPPair U x x) ≤ aprioriMeasure U (pairCode x x) [] :=
    complexityWeight_KP_le_aprioriMeasure U (pairCode x x) []
  -- `m(⟨x,x⟩)` is one term of the marginal.
  have h4 : aprioriMeasure U (pairCode x x) [] ≤ pairMarginal U x [] := by
    rw [pairMarginal_def]
    exact ENNReal.le_tsum x
  calc aprioriMeasure U x []
      ≤ (2 : ℝ≥0∞) ^ c₁ * complexityWeight (KPPlain U x) := h1
    _ ≤ (2 : ℝ≥0∞) ^ c₁ * ((2 : ℝ≥0∞) ^ c₂ * complexityWeight (KPPair U x x)) := by gcongr
    _ ≤ (2 : ℝ≥0∞) ^ c₁ * ((2 : ℝ≥0∞) ^ c₂ * aprioriMeasure U (pairCode x x) []) := by gcongr
    _ ≤ (2 : ℝ≥0∞) ^ c₁ * ((2 : ℝ≥0∞) ^ c₂ * pairMarginal U x []) := by gcongr
    _ = (2 : ℝ≥0∞) ^ (c₁ + c₂) * pairMarginal U x [] := by rw [pow_add, mul_assoc]

/-- **Lemma 1.7.3, packaged**: `Σ_y m(⟨x, y⟩) =× m(x)` with one shared constant. -/
theorem pairMarginal_eq_aprioriMeasure (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x : BitString,
      pairMarginal U x [] ≤ (2 : ℝ≥0∞) ^ c * aprioriMeasure U x [] ∧
      aprioriMeasure U x [] ≤ (2 : ℝ≥0∞) ^ c * pairMarginal U x [] := by
  obtain ⟨c₁, hc₁⟩ := pairMarginal_le_two_pow_mul_aprioriMeasure U hU
  obtain ⟨c₂, hc₂⟩ := aprioriMeasure_le_two_pow_mul_pairMarginal U hU
  refine ⟨c₁ + c₂, fun x ↦ ⟨?_, ?_⟩⟩
  · calc pairMarginal U x [] ≤ (2 : ℝ≥0∞) ^ c₁ * aprioriMeasure U x [] := hc₁ x
      _ ≤ (2 : ℝ≥0∞) ^ (c₁ + c₂) * aprioriMeasure U x [] := by
          gcongr
          · exact one_le_two
          · exact Nat.le_add_right c₁ c₂
  · calc aprioriMeasure U x [] ≤ (2 : ℝ≥0∞) ^ c₂ * pairMarginal U x [] := hc₂ x
      _ ≤ (2 : ℝ≥0∞) ^ (c₁ + c₂) * pairMarginal U x [] := by
          gcongr
          · exact one_le_two
          · exact Nat.le_add_left c₂ c₁

end Kolmogorov
