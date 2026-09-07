/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.UpperBound
import KolmogorovMathlib.AlgorithmicProbability.PairProjection

/-!
# The second-component projection and the first-component marginal

`AlgorithmicProbability/PairProjection` builds `projMap`, which decodes the *first*
component of `U`'s output, and uses it to bound the sum over *second* components
`Σ_y m(⟨x, y⟩)`. Theorem 1.7.2 needs the mirror image: the sum over *first*
components at a fixed second component, `Σ_x m(⟨x, y⟩)`, bounded by `m(y)`.

This file is that mirror image, line for line: `projMap2` post-composes `U` with
`decodeSecond`, inherits prefix-freeness because `Part.map` does not change the
halting domain, and dominates the first-component marginal because a program has
only one output, so distinct first components come from distinct programs.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The machine -/

/-- The **second-component projection machine**: run `U` and decode the second
component of its output. -/
def projMap2 (U : Map) : Map :=
  fun pr ↦ (U pr).map decodeSecond

/-- Membership characterisation of the second-component projection. -/
theorem produces_projMap2_iff (U : Map) (p y x : BitString) :
    produces (projMap2 U) p y x ↔ ∃ z, produces U p y z ∧ decodeSecond z = x := by
  change x ∈ Part.map decodeSecond (U (p, y)) ↔ ∃ z, produces U p y z ∧ decodeSecond z = x
  rw [Part.mem_map_iff]

/-- Post-composition by a total function does not change the halting domain. -/
theorem domainAt_projMap2 (U : Map) (y : BitString) :
    domainAt (projMap2 U) y = domainAt U y := rfl

/-- **The second-component projection is a prefix decompressor** whenever `U` is. -/
theorem projMap2_isPrefixDecompressor (U : Map) (hU : IsPrefixDecompressor U) :
    IsPrefixDecompressor (projMap2 U) := by
  refine ⟨?_, ?_⟩
  · have hf : Partrec (fun pr : BitString × BitString ↦ U pr) := hU.isDecompressor
    have hg : Computable₂ (fun (_ : BitString × BitString) (z : BitString) ↦ decodeSecond z) :=
      (decodeSecond_computable.comp Computable.snd).to₂
    exact (hf.map hg).of_eq (fun pr ↦ rfl)
  · intro y
    rw [domainAt_projMap2]
    exact hU.isPrefixMachine y

/-! ### The first-component marginal -/

/-- The **first-component marginal** at fixed second component `y`: the total a
priori probability of the pairs `⟨x, y⟩` over all `x`, in context `z`. -/
noncomputable def firstMarginal (M : Map) (y z : BitString) : ℝ≥0∞ :=
  ∑' x : BitString, aprioriMeasure M (pairCode x y) z

/-- Unfolding lemma for `firstMarginal`. -/
theorem firstMarginal_def (M : Map) (y z : BitString) :
    firstMarginal M y z = ∑' x : BitString, aprioriMeasure M (pairCode x y) z :=
  rfl

/-- **The first-component marginal is bounded by the projection machine's a priori
semimeasure.** Mirror of `pairMarginal_le_aprioriMeasure_projMap`. -/
theorem firstMarginal_le_aprioriMeasure_projMap2 (U : Map) (y z : BitString) :
    firstMarginal U y z ≤ aprioriMeasure (projMap2 U) y z := by
  classical
  rw [firstMarginal_def]
  simp only [aprioriMeasure]
  rw [ENNReal.tsum_comm]
  refine ENNReal.tsum_le_tsum (fun p ↦ ?_)
  by_cases hp : ∃ x, produces U p z (pairCode x y)
  · -- Determinism of `U` pins a unique first component `x₀`.
    obtain ⟨x₀, hx₀⟩ := hp
    have huniq : ∀ x, produces U p z (pairCode x y) → x = x₀ := by
      intro x hx
      have hmem : pairCode x y = pairCode x₀ y := Part.mem_unique hx hx₀
      exact (Prod.ext_iff.mp (@pairCode_injective (x, y) (x₀, y) hmem)).1
    have hsum : (∑' x, if produces U p z (pairCode x y) then progWeight p else 0)
        = progWeight p := by
      rw [tsum_eq_single x₀ (fun x hx ↦ by rw [if_neg (fun h ↦ hx (huniq x h))])]
      rw [if_pos hx₀]
    have hproj : produces (projMap2 U) p z y :=
      (produces_projMap2_iff U p z y).mpr ⟨pairCode x₀ y, hx₀, decodeSecond_pairCode x₀ y⟩
    rw [hsum, if_pos hproj]
  · push Not at hp
    rw [ENNReal.tsum_eq_zero.mpr (fun x ↦ if_neg (hp x))]
    exact zero_le

/-- **`Σ_x m(⟨x, y⟩) ≤× m(y)`.** The first-component marginal is dominated by the
a priori probability of the second component alone. -/
theorem firstMarginal_le_two_pow_mul_aprioriMeasure (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ y : BitString,
      firstMarginal U y [] ≤ (2 : ℝ≥0∞) ^ c * aprioriMeasure U y [] := by
  obtain ⟨c, hc⟩ := aprioriMeasure_le_two_pow_mul_aprioriMeasure_optimal hU
    (projMap2_isPrefixDecompressor U hU.isPrefixDecompressor)
  exact ⟨c, fun y ↦ (firstMarginal_le_aprioriMeasure_projMap2 U y []).trans (hc y [])⟩

end Kolmogorov
