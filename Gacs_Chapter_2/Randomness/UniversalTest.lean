/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.ComputableMeasure
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.AlgorithmicStatistics.DeficiencyTest
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems

/-!
# Gács Theorem 2.2.1: the universal integrable test `d_P(x) = −log P(x) − K(x)`

For a computable probability measure `P`, the function

  `t_P(x) = 2^{-K(x)} / P(x)`   (Gács: `d_P = log (m(x)/P(x))`, Definition 2.2.4/2.2.7)

is an integrable test, and every integrable test `t` satisfies `t ≤ 2^c · t_P`.

## Proof

*Test.* `2^{-K}` is lower semicomputable because `K` is upper semicomputable
(`KP_le_isRE`, `isLSC₁_complexityWeight_of_isRE`); `1/P` is lower semicomputable because
`P` is computable (`IsComputableENNReal.inv_isLSC₁`); products of lsc functions are lsc.
The expectation is `∑ P · 2^{-K}/P ≤ ∑ 2^{-K} ≤ 1` by Kraft.

*Universality.* For an integrable test `t`, `ν = P · t` is a lower semicomputable
semimeasure, so by the coding theorem `2^{-c} ν ≤ 2^{-K}`, i.e. `t ≤ 2^c · 2^{-K}/P`.

Gács writes the test with the universal semimeasure `m` in place of `2^{-K}`; the two
differ by a constant factor (coding theorem), and `universalSemimeasure_div_isUniversal`
gives that form too.
-/

namespace Kolmogorov.Randomness

open scoped ENNReal

/-! ### `K` is upper semicomputable and `2^{-K}` is lower semicomputable -/

/-- The relation `K_U(x) ≤ N` is recursively enumerable for any decompressor `U`. -/
theorem KP_le_isRE (U : Map) (hU : isDecompressor U) :
    IsRE (fun q : BitString × ℕ ↦ KP U q.1 [] ≤ (q.2 : ENat)) := by
  have hR : IsRE (fun p : (BitString × ℕ) × BitString ↦ produces U p.2 [] p.1.1) :=
    (producesIsRe U hU).comp
      (g := fun p : (BitString × ℕ) × BitString ↦ ((p.1.1, ([] : BitString), p.1.2), p.2))
      (Computable.pair (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.const []) (Computable.snd.comp Computable.fst)))
        Computable.snd)
  refine (IsRE.existsInList (R := fun (q : BitString × ℕ) (p : BitString) ↦ produces U p [] q.1)
    hR (fun q : BitString × ℕ ↦ boundedPrograms q.2)
    (Computable.boundedPrograms.comp Computable.snd)).congr (fun q ↦ ?_)
  rw [KP_eq_condK, condKLeIff]
  constructor
  · rintro ⟨p, hmem, hprod⟩
    exact ⟨p, (mem_boundedPrograms_iff p q.2).mp hmem, hprod⟩
  · rintro ⟨p, hlen, hprod⟩
    exact ⟨p, (mem_boundedPrograms_iff p q.2).mpr hlen, hprod⟩

/-- `2^{-K_U(x)}` is lower semicomputable. -/
theorem prefixComplexityWeight_isLSC₁ (U : Map) (hU : isDecompressor U) :
    IsLSC₁ (prefixComplexityWeight U) :=
  (isLSC₁_complexityWeight_of_isRE (fun x ↦ KP U x []) (KP_le_isRE U hU)).congr
    (fun _ ↦ rfl)

/-- A unary lsc function is a conditional lsc function ignoring its condition. -/
theorem IsLSC₁.toCond {f : BitString → ℝ≥0∞} (hf : IsLSC₁ f) : IsLSC (fun x _ ↦ f x) := by
  obtain ⟨a, h1, h2, h3⟩ := hf
  exact ⟨fun s x _ ↦ a s x, fun s x _ ↦ h1 s x, fun x _ ↦ h2 x,
    h3.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd))⟩

/-! ### The canonical test -/

/-- **Gács' `t_P`** (Definition 2.2.7), with `2^{-K}` in place of `m`:
`t_P(x) = 2^{-K(x)} / P(x)`. -/
noncomputable def canonicalIntegrableTest (U : Map) (P : ComputableMeasure) (x : BitString) :
    ℝ≥0∞ :=
  prefixComplexityWeight U x / P.mass x

/-- **Theorem 2.2.1, test property.** -/
theorem canonicalIntegrableTest_isIntegrableTest (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableMeasure) : IsIntegrableTest P (canonicalIntegrableTest U P) := by
  refine ⟨?_, ?_⟩
  · exact ((prefixComplexityWeight_isLSC₁ U hU.isDecompressor).mul
      P.computable.inv_isLSC₁).congr (fun x ↦ by rw [canonicalIntegrableTest, div_eq_mul_inv])
  · calc ∑' x, P.mass x * canonicalIntegrableTest U P x
        ≤ ∑' x, prefixComplexityWeight U x :=
          ENNReal.tsum_le_tsum (fun x ↦ ENNReal.mul_div_le)
      _ ≤ 1 := KP_kraft_sum_le_one U hU.isPrefixDecompressor []

/-- **Theorem 2.2.1, universality.** Every integrable test for `P` is dominated by `t_P`. -/
theorem integrableTest_le_canonical (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableMeasure) {t : BitString → ℝ≥0∞} (ht : IsIntegrableTest P t) :
    ∃ c : ℕ, ∀ x, t x ≤ 2 ^ c * canonicalIntegrableTest U P x := by
  -- `ν = P · t` is a lower semicomputable semimeasure.
  have hν : IsLowerSemicomputableSemimeasure (fun x ↦ P.mass x * t x) :=
    ⟨ht.2, (P.computable.isLSC₁.mul ht.1).toCond⟩
  obtain ⟨c, hc⟩ := lowerSemicomputableSemimeasure_le_prefixComplexityWeight hν hU
  refine ⟨c, fun x ↦ ?_⟩
  have hw0 : prefixComplexityWeight U x ≠ 0 := by
    unfold prefixComplexityWeight
    obtain ⟨k, hk⟩ : ∃ k : ℕ, KP U x [] = (k : ENat) :=
      ⟨_, (ENat.coe_toNat (KP_ne_top_of_optimal U hU x [])).symm⟩
    rw [hk, complexityWeight_coe]
    exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
  unfold canonicalIntegrableTest
  rcases eq_or_ne (P.mass x) 0 with hP0 | hP0
  · rw [hP0, ENNReal.div_zero hw0, ENNReal.mul_top (two_pow_ne_zero' c)]
    exact le_top
  · rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hP0) (Or.inl (P.mass_ne_top x))]
    have h := hc x
    -- `2^{-c} · P t ≤ w`, hence `P t ≤ 2^c · w`.
    calc t x * P.mass x = 2 ^ c * (2⁻¹ ^ c * (P.mass x * t x)) := by
          rw [← mul_assoc, ← ENNReal.inv_pow,
            ENNReal.mul_inv_cancel (two_pow_ne_zero' c) (two_pow_ne_top' c), one_mul, mul_comm]
      _ ≤ 2 ^ c * prefixComplexityWeight U x := by gcongr

/-- **Gács Theorem 2.2.1.** `t_P = 2^{-K}/P` is a universal integrable test for every
computable probability measure `P`. -/
theorem canonicalIntegrableTest_isUniversal (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableMeasure) : IsUniversalIntegrableTest P (canonicalIntegrableTest U P) :=
  ⟨canonicalIntegrableTest_isIntegrableTest U hU P,
    fun _ ht ↦ integrableTest_le_canonical U hU P ht⟩

/-! ### Gács' form with the universal semimeasure `m` -/

/-- Every positive `ℝ≥0∞` is at least `2^{-c}` for some `c`. -/
theorem exists_inv_two_pow_le_of_pos {a : ℝ≥0∞} (ha : 0 < a) : ∃ c : ℕ, 2⁻¹ ^ c ≤ a := by
  obtain ⟨c, hc⟩ := ENNReal.exists_inv_two_pow_lt ha.ne'
  exact ⟨c, hc.le⟩

/-- **Theorem 2.2.1 in Gács' form.** For a universal semimeasure `m`, `m(x)/P(x)` is a
universal integrable test. -/
theorem universalSemimeasure_div_isUniversal {m : BitString → ℝ≥0∞}
    (hm : IsUniversalSemimeasure m) (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableMeasure) : IsUniversalIntegrableTest P (fun x ↦ m x / P.mass x) := by
  obtain ⟨c1, c2, hc1, hc2, h1, h2⟩ := universalSemimeasure_equiv_prefixComplexity hm hU
  refine ⟨⟨?_, ?_⟩, fun t ht ↦ ?_⟩
  · exact ((IsLSC.toUnary hm.1.2).mul P.computable.inv_isLSC₁).congr
      (fun x ↦ by rw [div_eq_mul_inv])
  · calc ∑' x, P.mass x * (m x / P.mass x) ≤ ∑' x, m x :=
          ENNReal.tsum_le_tsum (fun x ↦ ENNReal.mul_div_le)
      _ ≤ 1 := hm.1.1
  · obtain ⟨c, hc⟩ := integrableTest_le_canonical U hU P ht
    obtain ⟨c', hc'⟩ := exists_inv_two_pow_le_of_pos hc2
    refine ⟨c + c', fun x ↦ ?_⟩
    -- `w ≤ c2⁻¹ m ≤ 2^{c'} m`.
    have hwm : prefixComplexityWeight U x ≤ 2 ^ c' * m x := by
      have : 2⁻¹ ^ c' * prefixComplexityWeight U x ≤ m x := (mul_le_mul' hc' le_rfl).trans (h2 x)
      calc prefixComplexityWeight U x = 2 ^ c' * (2⁻¹ ^ c' * prefixComplexityWeight U x) := by
            rw [← mul_assoc, ← ENNReal.inv_pow,
              ENNReal.mul_inv_cancel (two_pow_ne_zero' c') (two_pow_ne_top' c'), one_mul]
        _ ≤ 2 ^ c' * m x := by gcongr
    calc t x ≤ 2 ^ c * canonicalIntegrableTest U P x := hc x
      _ = 2 ^ c * (prefixComplexityWeight U x / P.mass x) := rfl
      _ ≤ 2 ^ c * (2 ^ c' * m x / P.mass x) := by gcongr
      _ = 2 ^ (c + c') * (m x / P.mass x) := by rw [pow_add, mul_div_assoc]; ring

end Kolmogorov.Randomness
