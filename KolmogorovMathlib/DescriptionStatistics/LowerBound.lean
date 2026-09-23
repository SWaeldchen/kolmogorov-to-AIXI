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
prefix-prepend universal machine `U`: once `n` exceeds the plain complexity `K(x)` by
a fixed constant, the a priori probability of the pair `⟨x, n⟩` is dominated by the
mass of the length-`n` programs for `x`,

  `2^{-c'} · m(x, n) ≤ 2^{-n} · f(x, n)`   whenever `K(x) + c ≤ n`

(`aprioriMeasure_pair_le_progCount`). This is Gács' hypothesis `n ≥ K(x)` up to a
constant depending only on `U`.

The proof has two regimes, split at `K(x, n) + c₀`.

* **The padding lemma** (`aprioriMeasure_pair_le_progCount_of_KPPair_add_le`) is Gács'
  argument as printed, and holds under the hypothesis it consumes, `K(x, n) + c₀ ≤ n`.
  Its two constants are kept separate: `c₀ = 2|g| + 1` is the overhead of the padding
  construction (a universality tag `g` plus its unary length code); `c₁` is the
  coding-theorem constant.
* **The window** `K(x) + c ≤ n < K(x, n) + c₀`, of width up to `log n`, is where the
  padding argument has no room. There a second machine, which pads with a
  self-delimiting *filler* instead of stating a length, supplies a program of length
  exactly `n` (`one_le_progCount_of_KPPlain_add_le`), and one program is enough.

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

## The filler machine

* `fillerUnion U := taggedUnion (fun _ ↦ U)` — Gács' machine `G'`: on `1^k 0 p` it
  discards the filler and runs `U` on `p`. The tagged union of a *constant* family is
  exactly this machine, so prefix-freeness, simulation and partial recursiveness all
  come from `Prefix.Combinators`.
* Universality gives a tag `g'`; with `q` a shortest program for `x`, the program
  `g' ++ 1^k 0 q` has length `K(x) + |g'| + 1 + k`, for every `k`. Hence `f(x, n) ≥ 1`
  for all `n ≥ K(x) + c` with `c := |g'| + 1`.

`K(x, n)` stays in the conclusion throughout: the program must state its own length
to remain prefix-free, so the count is governed by the pair complexity. Only the
hypothesis is weakened.
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

/-- **The padding lemma**: the lower half of Theorem 1.7.1 under the hypothesis the
padding argument consumes. For a prefix-prepend universal `U` there are constants `c₀`
(padding overhead) and `c₁` (coding theorem) such that for all `x` and `n` with
`K(x, n) + c₀ ≤ n`,

  `2^{-(c₀ + c₁)} · m(x, n) ≤ 2^{-n} · f(x, n)`.

The theorem itself, `aprioriMeasure_pair_le_progCount` below, weakens the hypothesis
to `K(x) + c ≤ n`. -/
theorem aprioriMeasure_pair_le_progCount_of_KPPair_add_le (U : Map)
    (hU : IsPrefixPrependUniversal U) :
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

/-! ### The filler machine `G'` -/

/-- **The filler machine** `G' := taggedUnion (fun _ ↦ U)`: on `natCode k ++ p`,
that is `1^k 0 p`, it discards the unary filler and runs `U` on `p`. Every index
runs the same machine, so the tag carries no information; its only job is to let
a program for `x` be lengthened by any amount while staying prefix-free. -/
def fillerUnion (U : Map) : Map := taggedUnion fun _ ↦ U

/-- The filler machine is a prefix machine whenever `U` is. -/
theorem fillerUnion_isPrefixMachine {U : Map} (hU : IsPrefixMachine U) :
    IsPrefixMachine (fillerUnion U) :=
  taggedUnion_isPrefixMachine fun _ ↦ hU

/-- The filler machine is partial recursive whenever `U` is: the constant family
`fun _ ↦ U` is uniformly partial recursive. -/
theorem fillerUnion_isDecompressor {U : Map} (hU : isDecompressor U) :
    isDecompressor (fillerUnion U) := by
  unfold fillerUnion
  exact taggedUnion_isDecompressor_of_uniform (hU.comp Computable.snd)

/-- The filler machine is a prefix decompressor whenever `U` is. -/
theorem fillerUnion_isPrefixDecompressor {U : Map} (hU : IsPrefixDecompressor U) :
    IsPrefixDecompressor (fillerUnion U) :=
  ⟨fillerUnion_isDecompressor hU.isDecompressor, fillerUnion_isPrefixMachine hU.isPrefixMachine⟩

/-- Whatever `U` produces from `q`, the filler machine produces from `1^k 0 q`,
for every `k`. -/
theorem fillerUnion_produces {U : Map} (k : ℕ) {q y x : BitString}
    (h : produces U q y x) : produces (fillerUnion U) (natCode k ++ q) y x :=
  taggedUnion_produces_natCode (M := fun _ ↦ U) (i := k) h

/-! ### Every length past `K(x) + c` is realised -/

/-- **The window lemma.** For a prefix-prepend universal `U` there is a constant `c`
such that `x` has a program of length exactly `n` whenever `K(x) + c ≤ n`. The
program is `g ++ 1^k 0 q` with `q` a shortest program for `x`, `g` the universality
tag of the filler machine, and `k` chosen to make the length come out to `n`. -/
theorem one_le_progCount_of_KPPlain_add_le (U : Map) (hU : IsPrefixPrependUniversal U) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ),
      KPPlain U x + (c : ENat) ≤ (n : ENat) → 1 ≤ progCount U x n := by
  classical
  obtain ⟨s⟩ := hU.2 (fillerUnion U) (fillerUnion_isPrefixDecompressor hU.isPrefixDecompressor)
  refine ⟨s.tag.length + 1, fun x n hn ↦ ?_⟩
  -- `x` has a shortest program `q`, of length `K(x)`.
  have hne : KP U x [] ≠ ⊤ := by
    intro h
    rw [KPPlain_eq_KP, h, top_add] at hn
    exact ENat.coe_ne_top n (top_le_iff.mp hn)
  obtain ⟨q, hq, hqlen⟩ := KP_mem_candidateLengths_of_ne_top hne
  have hk : q.length + (s.tag.length + 1) ≤ n := by
    rw [KPPlain_eq_KP, ← hqlen] at hn
    exact_mod_cast hn
  -- The filler length `k` that makes `g ++ 1^k 0 q` come out to exactly `n`.
  obtain ⟨k, hkn⟩ : ∃ k, n = s.tag.length + ((k + 1) + q.length) :=
    ⟨n - (s.tag.length + 1 + q.length), by omega⟩
  have hp : produces U (s.tag ++ (natCode k ++ q)) [] x :=
    s.simulates _ _ _ (fillerUnion_produces k hq)
  have hlen : (s.tag ++ (natCode k ++ q)).length = n := by
    simp only [List.length_append, length_natCode]; omega
  exact Finset.card_pos.mpr ⟨_, mem_progSet.mpr ⟨hlen, hp⟩⟩

/-! ### The lower bound under `K(x) + c ≤ n` -/

/-- **Theorem 1.7.1, lower half (`≥×`).** For a prefix-prepend
universal `U` there are constants `c` and `c'` such that for all `x` and `n` with
`K(x) + c ≤ n`,

  `2^{-c'} · m(x, n) ≤ 2^{-n} · f(x, n)`.

Compared with the padding lemma
`aprioriMeasure_pair_le_progCount_of_KPPair_add_le`, the hypothesis is on the plain
complexity `K(x)` rather than the pair complexity `K(x, n)`; the conclusion is the
same. The proof splits at `K(x, n) + c₀`: above it the pair-hypothesis theorem
applies, below it the window lemma gives `f(x, n) ≥ 1` and the a priori probability
of the pair is at most `2^{c₀ + c₂} · 2^{-n}` by the coding theorem. -/
theorem aprioriMeasure_pair_le_progCount (U : Map)
    (hU : IsPrefixPrependUniversal U) :
    ∃ c c' : ℕ, ∀ (x : BitString) (n : ℕ),
      KPPlain U x + (c : ENat) ≤ (n : ENat) →
        (2 : ℝ≥0∞)⁻¹ ^ c' * aprioriMeasure U (pairCode x (natCode n)) []
          ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (progCount U x n : ℝ≥0∞) := by
  obtain ⟨c₀, c₁, hpair⟩ := aprioriMeasure_pair_le_progCount_of_KPPair_add_le U hU
  obtain ⟨c, hc⟩ := one_le_progCount_of_KPPlain_add_le U hU
  obtain ⟨c₂, hc₂⟩ := aprioriMeasure_le_complexityWeight_optimal
    hU.isOptimalPrefixConditional hU.isPrefixDecompressor
  refine ⟨c, c₀ + c₁ + c₂, fun x n hn ↦ ?_⟩
  -- Shrinking the constant only weakens a lower bound: `2^{-(a+b)} · m ≤ 2^{-a} · m`.
  have hdrop : ∀ (a b : ℕ) (m : ℝ≥0∞),
      (2 : ℝ≥0∞)⁻¹ ^ (a + b) * m ≤ (2 : ℝ≥0∞)⁻¹ ^ a * m := fun a b m ↦ by
    rw [pow_add, mul_assoc]
    exact mul_le_mul_right (mul_le_of_le_one_left zero_le
      (pow_le_one₀ zero_le (ENNReal.inv_le_one.mpr one_le_two))) _
  have hKP : KPPair U x (natCode n) = KP U (pairCode x (natCode n)) [] := rfl
  by_cases hcase : KPPair U x (natCode n) + (c₀ : ENat) ≤ (n : ENat)
  · -- The padding regime: the pair-hypothesis theorem, with a smaller constant.
    exact (hdrop (c₀ + c₁) c₂ _).trans (hpair x n hcase)
  · -- The window: `n < K(x, n) + c₀`, so `2^{-n}` already dominates the a priori
    -- probability of the pair, and `f(x, n) ≥ 1` does the rest.
    have hlt : (n : ENat) ≤ KP U (pairCode x (natCode n)) [] + (c₀ : ENat) := by
      rw [← hKP]; exact (not_le.mp hcase).le
    have hf : (1 : ℝ≥0∞) ≤ (progCount U x n : ℝ≥0∞) := by exact_mod_cast hc x n hn
    have hw : (2 : ℝ≥0∞)⁻¹ ^ c₀ * complexityWeight (KP U (pairCode x (natCode n)) [])
        ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
      rw [mul_comm, ← complexityWeight_add_nat]
      exact complexityWeight_le_of_le hlt
    rw [show c₀ + c₁ + c₂ = c₀ + c₂ + c₁ by omega]
    calc (2 : ℝ≥0∞)⁻¹ ^ (c₀ + c₂ + c₁) * aprioriMeasure U (pairCode x (natCode n)) []
        ≤ (2 : ℝ≥0∞)⁻¹ ^ (c₀ + c₂) * aprioriMeasure U (pairCode x (natCode n)) [] :=
          hdrop _ _ _
      _ = (2 : ℝ≥0∞)⁻¹ ^ c₀
            * ((2 : ℝ≥0∞)⁻¹ ^ c₂ * aprioriMeasure U (pairCode x (natCode n)) []) := by
          rw [pow_add, mul_assoc]
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ c₀ * complexityWeight (KP U (pairCode x (natCode n)) []) :=
          mul_le_mul_right (hc₂ _ _) _
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n := hw
      _ = (2 : ℝ≥0∞)⁻¹ ^ n * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (progCount U x n : ℝ≥0∞) := mul_le_mul_right hf _

end Kolmogorov
