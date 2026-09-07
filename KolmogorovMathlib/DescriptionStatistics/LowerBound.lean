/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.ProgramCount
import KolmogorovMathlib.DescriptionStatistics.PrefixPrependUniversal
import KolmogorovMathlib.DescriptionStatistics.PaddingMachine
import KolmogorovMathlib.DescriptionStatistics.PaddingMachineComputable
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin
import KolmogorovMathlib.Prefix.Symmetry

/-!
# Theorem 1.7.1, lower half: `m(x, n) ≤× 2^{-n} · f(x, n)`

This file proves the `≥×` direction of Gács' Theorem 1.7.1 (`thm:Hstat`) for a
prefix-prepend universal machine `U`: once `n` exceeds the pair complexity
`K(x, n)` by a fixed constant, the a priori probability of the pair `⟨x, n⟩` is
dominated by the mass of the length-`n` programs for `x`,

  `2^{-(c₀ + c₁)} · m(x, n) ≤ 2^{-n} · f(x, n)`   whenever `K(x, n) + c₀ ≤ n`.

The two constants are kept separate: `c₀ = 2|g| + 1` is the overhead of the
padding construction (a universality tag `g` plus its unary length code) and is
the only constant the hypothesis needs; `c₁` is the coding-theorem constant.

## The construction

* `padUnion U` — Gács' machine `G`: the tagged union `taggedUnion (padBuilder U)`
  of the padding cores. On `natCode i ++ w` it behaves as `P_i` on `w`.
* Universality gives a tag `g` with `G(p) = x → U(g ++ p) = x`. Set `r := |g|`.
* For a shortest program `q` of the pair `⟨x, n⟩` and any padding `u` of length
  `ℓ := n − |q| − (2r + 1)`, the string `g ++ natCode r ++ q ++ u` has length
  exactly `n` and is a `U`-program for `x` (`padProgram_produces`). Distinct `u`
  give distinct programs, so `2^ℓ ≤ f(x, n)` (`two_pow_le_progCount`).
* The coding theorem `2^{-c₁} · m(x, n) ≤ 2^{-K(x, n)}` and the identity
  `2^{-n} · 2^ℓ = 2^{-(|q| + c₀)}` finish the calculation.

Partial recursiveness of `G` is the content of `PaddingMachineComputable`
(`taggedUnion_padBuilder_isDecompressor`); everything else here is elementary.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Gács' machine `G` -/

/-- **The padding union** `G := taggedUnion (i ↦ P_i)`: on input `natCode i ++ w`
it runs the padding core `P_i` on `w`. Reading `i` from the input is what lets
`G` be defined without reference to its own universality tag. -/
noncomputable def padUnion (U : Map) : Map := taggedUnion (padBuilder U)

/-- The padding union is a prefix machine whenever `U` is: each core is
(`padBuilder_isPrefixMachine`), and tagged unions preserve this. -/
theorem padUnion_isPrefixMachine {U : Map} (hU : IsPrefixMachine U) :
    IsPrefixMachine (padUnion U) :=
  taggedUnion_isPrefixMachine (fun i ↦ padBuilder_isPrefixMachine hU i)

/-- The padding union is partial recursive whenever `U` is a prefix decompressor:
this is the dovetailing construction of `PaddingMachineComputable`. -/
theorem padUnion_isDecompressor {U : Map} (hU : IsPrefixDecompressor U) :
    isDecompressor (padUnion U) := by
  unfold padUnion
  exact taggedUnion_padBuilder_isDecompressor hU

/-- The padding union is a prefix decompressor whenever `U` is. -/
theorem padUnion_isPrefixDecompressor {U : Map} (hU : IsPrefixDecompressor U) :
    IsPrefixDecompressor (padUnion U) :=
  ⟨padUnion_isDecompressor hU, padUnion_isPrefixMachine hU.isPrefixMachine⟩

/-! ### The padded programs -/

/-- The length of a padded program `g ++ natCode |g| ++ q ++ u`. -/
theorem padProgram_length (g q u : BitString) :
    (g ++ (natCode g.length ++ (q ++ u))).length
      = g.length + (g.length + 1) + q.length + u.length := by
  simp only [List.length_append, length_natCode]; omega

/-- Padding with different strings gives different programs. -/
theorem padProgram_injective (g q : BitString) :
    Function.Injective (fun u : BitString ↦ g ++ (natCode g.length ++ (q ++ u))) := by
  intro u u' h
  simp only at h
  exact List.append_cancel_left (List.append_cancel_left (List.append_cancel_left h))

/-- **A padded program produces `x`.** If `q` is a `U`-program for the pair
`⟨x, n⟩` and the padding `u` brings the total length to exactly `n`, then
`g ++ natCode |g| ++ q ++ u` is a `U`-program for `x`: `P_{|g|}` accepts
`q ++ u` because the pair records the total length, the tagged union routes
`natCode |g| ++ (q ++ u)` to `P_{|g|}`, and the simulation prepends `g`. -/
theorem padProgram_produces {U : Map} (hU : IsPrefixMachine U)
    (s : PrefixPrependSimulation U (padUnion U)) {x q u : BitString} {n : ℕ}
    (hq : produces U q [] (pairCode x (natCode n)))
    (hlen : s.tag.length + (s.tag.length + 1) + q.length + u.length = n) :
    produces U (s.tag ++ (natCode s.tag.length ++ (q ++ u))) [] x := by
  apply s.simulates
  unfold padUnion
  apply taggedUnion_produces_natCode
  apply padBuilder_produces_of_spec hU
  refine ⟨q, u, rfl, ?_⟩
  have htot : (q ++ u).length + 2 * s.tag.length + 1 = n := by
    simp only [List.length_append]; omega
  rw [htot]
  exact hq

/-! ### Counting -/

/-- **The padding injection.** Under the same hypotheses, the `2^ℓ` paddings of
length `ℓ` give `2^ℓ` distinct length-`n` programs for `x`. -/
theorem two_pow_le_progCount {U : Map} (hU : IsPrefixMachine U)
    (s : PrefixPrependSimulation U (padUnion U)) {x q : BitString} {n ℓ : ℕ}
    (hq : produces U q [] (pairCode x (natCode n)))
    (hℓ : s.tag.length + (s.tag.length + 1) + q.length + ℓ = n) :
    2 ^ ℓ ≤ progCount U x n := by
  classical
  rw [← cardStringsOfLength ℓ, progCount]
  refine Finset.card_le_card_of_injOn
    (fun u : BitString ↦ s.tag ++ (natCode s.tag.length ++ (q ++ u))) ?_ ?_
  · intro u hu
    rw [Finset.mem_coe, memStringsOfLength] at hu
    rw [Finset.mem_coe, mem_progSet]
    refine ⟨?_, padProgram_produces hU s hq (by omega)⟩
    rw [padProgram_length]; omega
  · intro u _ u' _ h
    exact padProgram_injective _ _ h

/-! ### Arithmetic -/

/-- `2^{-(a + ℓ)} · 2^ℓ = 2^{-a}` in `ℝ≥0∞`. -/
theorem inv_two_pow_add_mul_two_pow (a ℓ : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ (a + ℓ) * (2 : ℝ≥0∞) ^ ℓ = (2 : ℝ≥0∞)⁻¹ ^ a := by
  rw [pow_add, mul_assoc, ← mul_pow,
    ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]

/-! ### The lower bound -/

/-- **Theorem 1.7.1, lower half (`≥×`).** For a prefix-prepend universal `U`
there are constants `c₀` (padding overhead) and `c₁` (coding theorem) such that
for all `x` and `n` with `K(x, n) + c₀ ≤ n`,

  `2^{-(c₀ + c₁)} · m(x, n) ≤ 2^{-n} · f(x, n)`. -/
theorem aprioriMeasure_pair_le_progCount (U : Map) (hU : IsPrefixPrependUniversal U) :
    ∃ c₀ c₁ : ℕ, ∀ (x : BitString) (n : ℕ),
      KPPair U x (natCode n) + (c₀ : ENat) ≤ (n : ENat) →
        (2 : ℝ≥0∞)⁻¹ ^ (c₀ + c₁) * aprioriMeasure U (pairCode x (natCode n)) []
          ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (progCount U x n : ℝ≥0∞) := by
  -- A universality tag for Gács' machine `G`.
  obtain ⟨s⟩ := hU.2 (padUnion U) (padUnion_isPrefixDecompressor hU.isPrefixDecompressor)
  -- The coding-theorem constant for `U` against itself.
  obtain ⟨c₁, hc₁⟩ := aprioriMeasure_le_complexityWeight_optimal
    hU.isOptimalPrefixConditional hU.isPrefixDecompressor
  refine ⟨2 * s.tag.length + 1, c₁, fun x n hn ↦ ?_⟩
  -- The pair has a shortest program `q`, of length `K(x, n)`.
  have hKP : KPPair U x (natCode n) = KP U (pairCode x (natCode n)) [] := rfl
  have hne : KP U (pairCode x (natCode n)) [] ≠ ⊤ := by
    intro h
    rw [hKP, h, top_add] at hn
    exact ENat.coe_ne_top n (top_le_iff.mp hn)
  obtain ⟨q, hq, hqlen⟩ := KP_mem_candidateLengths_of_ne_top hne
  -- The slack `ℓ := n − |q| − c₀` is a genuine natural number.
  have hk : q.length + (2 * s.tag.length + 1) ≤ n := by
    rw [hKP, ← hqlen] at hn
    exact_mod_cast hn
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, n = (2 * s.tag.length + 1 + q.length) + ℓ :=
    ⟨n - (2 * s.tag.length + 1 + q.length), by omega⟩
  -- Counting: `2^ℓ ≤ f(x, n)`.
  have hcount : (2 : ℝ≥0∞) ^ ℓ ≤ (progCount U x n : ℝ≥0∞) := by
    exact_mod_cast two_pow_le_progCount hU.isPrefixDecompressor.isPrefixMachine s hq
      (by omega)
  -- Coding: `2^{-c₁} · m(x, n) ≤ 2^{-|q|}`.
  have hcode : (2 : ℝ≥0∞)⁻¹ ^ c₁ * aprioriMeasure U (pairCode x (natCode n)) []
      ≤ (2 : ℝ≥0∞)⁻¹ ^ q.length := by
    have h := hc₁ (pairCode x (natCode n)) []
    rwa [← hqlen, complexityWeight_coe] at h
  calc (2 : ℝ≥0∞)⁻¹ ^ (2 * s.tag.length + 1 + c₁)
        * aprioriMeasure U (pairCode x (natCode n)) []
      = (2 : ℝ≥0∞)⁻¹ ^ (2 * s.tag.length + 1)
          * ((2 : ℝ≥0∞)⁻¹ ^ c₁ * aprioriMeasure U (pairCode x (natCode n)) []) := by
        rw [pow_add, mul_assoc]
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (2 * s.tag.length + 1) * (2 : ℝ≥0∞)⁻¹ ^ q.length := by gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ (2 * s.tag.length + 1 + q.length) := by rw [← pow_add]
    _ = (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ ℓ := by
        rw [hℓ, inv_two_pow_add_mul_two_pow]
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (progCount U x n : ℝ≥0∞) := by gcongr

end Kolmogorov
