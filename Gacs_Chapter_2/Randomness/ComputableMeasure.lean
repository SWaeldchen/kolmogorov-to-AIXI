/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.LSCAlgebra

/-!
# Computable measures and tests of randomness (Gács §2.2, definitions)

* `ComputableMeasure`: a probability measure on strings whose mass function is
  computable in the sense of `IsComputableENNReal` (Gács Definition 1.5.1).
* `IsIntegrableTest P t` (Definition 2.2.1): `t` lower semicomputable with
  `∑ P(x) t(x) ≤ 1`. Gács' `d` is `log t`.
* `IsMLTest P t`: `t` lower semicomputable with `P {t > 2^k} ≤ 2^{-k}` for all `k`, the
  probability-bounded condition (2.1.1) for an arbitrary `P`.
* `IsIntegrableTest.isMLTest`: **Proposition 2.2.3, first half** — every integrable test
  is probability-bounded, by Markov's inequality.

The converse half of Proposition 2.2.3 (a probability-bounded test yields an integrable
one after the correction `d − 2 log d − c`) is in `MLToIntegrable.lean`.
-/

namespace Kolmogorov.Randomness

open scoped ENNReal

/-- **Computable probability measure** on strings. -/
structure ComputableMeasure where
  /-- The mass function. -/
  mass : BitString → ℝ≥0∞
  /-- Total mass one. -/
  tsum_eq : ∑' x, mass x = 1
  /-- The mass function is computable. -/
  computable : IsComputableENNReal mass

namespace ComputableMeasure

theorem mass_le_one (P : ComputableMeasure) (x : BitString) : P.mass x ≤ 1 := by
  rw [← P.tsum_eq]; exact ENNReal.le_tsum x

theorem mass_ne_top (P : ComputableMeasure) (x : BitString) : P.mass x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (P.mass_le_one x)

/-- The measure of a set of strings. -/
noncomputable def measureOf (P : ComputableMeasure) (S : Set BitString) : ℝ≥0∞ :=
  ∑' x, S.indicator P.mass x

theorem measureOf_mono (P : ComputableMeasure) {S T : Set BitString} (h : S ⊆ T) :
    P.measureOf S ≤ P.measureOf T :=
  ENNReal.tsum_le_tsum (fun x ↦ Set.indicator_le_indicator_of_subset h (fun _ ↦ zero_le) x)

theorem measureOf_le_one (P : ComputableMeasure) (S : Set BitString) : P.measureOf S ≤ 1 := by
  rw [← P.tsum_eq]
  exact ENNReal.tsum_le_tsum (fun x ↦ Set.indicator_le_self _ _ x)

end ComputableMeasure

/-! ### Tests -/

/-- **Integrable (expectation-bounded) test** for `P`, Gács Definition 2.2.1, in
multiplicative form `t = 2^d`. -/
def IsIntegrableTest (P : ComputableMeasure) (t : BitString → ℝ≥0∞) : Prop :=
  IsLSC₁ t ∧ ∑' x, P.mass x * t x ≤ 1

/-- **Probability-bounded (Martin-Löf) test** for `P`: condition (2.1.1) for an arbitrary
computable measure. -/
def IsMLTest (P : ComputableMeasure) (t : BitString → ℝ≥0∞) : Prop :=
  IsLSC₁ t ∧ ∀ k : ℕ, P.measureOf {x | (2 : ℝ≥0∞) ^ k < t x} ≤ 2⁻¹ ^ k

/-- A **universal integrable test** dominates every integrable test up to a constant. -/
def IsUniversalIntegrableTest (P : ComputableMeasure) (t₀ : BitString → ℝ≥0∞) : Prop :=
  IsIntegrableTest P t₀ ∧ ∀ t, IsIntegrableTest P t → ∃ c : ℕ, ∀ x, t x ≤ 2 ^ c * t₀ x

/-! ### Proposition 2.2.3, first half: Markov's inequality -/

/-- **Gács Proposition 2.2.3 (a).** An integrable test is probability-bounded:
`P {t > 2^k} ≤ 2^{-k} ∑ P t ≤ 2^{-k}`. -/
theorem IsIntegrableTest.isMLTest {P : ComputableMeasure} {t : BitString → ℝ≥0∞}
    (h : IsIntegrableTest P t) : IsMLTest P t := by
  refine ⟨h.1, fun k ↦ ?_⟩
  have hpt : ∀ x, ({x | (2 : ℝ≥0∞) ^ k < t x}).indicator P.mass x
      ≤ P.mass x * t x * 2⁻¹ ^ k := by
    intro x
    by_cases hx : (2 : ℝ≥0∞) ^ k < t x
    · rw [Set.indicator_of_mem (show x ∈ {x | (2 : ℝ≥0∞) ^ k < t x} from hx)]
      calc P.mass x = P.mass x * (2 ^ k * 2⁻¹ ^ k) := by
            rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel (two_pow_ne_zero' k) (two_pow_ne_top' k),
              mul_one]
        _ = P.mass x * 2 ^ k * 2⁻¹ ^ k := by ring
        _ ≤ P.mass x * t x * 2⁻¹ ^ k := mul_le_mul' (mul_le_mul' le_rfl hx.le) le_rfl
    · rw [Set.indicator_of_notMem (show x ∉ {x | (2 : ℝ≥0∞) ^ k < t x} from hx)]
      exact zero_le
  calc P.measureOf {x | (2 : ℝ≥0∞) ^ k < t x}
      ≤ ∑' x, P.mass x * t x * 2⁻¹ ^ k := ENNReal.tsum_le_tsum hpt
    _ = (∑' x, P.mass x * t x) * 2⁻¹ ^ k := ENNReal.tsum_mul_right
    _ ≤ 1 * 2⁻¹ ^ k := mul_le_mul' h.2 le_rfl
    _ = 2⁻¹ ^ k := one_mul _

end Kolmogorov.Randomness
