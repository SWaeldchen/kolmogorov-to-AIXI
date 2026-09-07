/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.LowerBound
import KolmogorovMathlib.DescriptionStatistics.ShortestDescriptions
import KolmogorovMathlib.AlgorithmicStatistics.NonStochastic
import KolmogorovMathlib.Encoding.Tuples

/-!
# Theorem 1.7.2, first half: `log |D_n| =⁺ n − K(n)`

`D_n` is the set of halting programs of length exactly `n` (Definition 1.7.2), and the
first assertion of Theorem 1.7.2 is that `|D_n|` is about `2^{n − K(n)}`. In the
multiplicative form used throughout this directory:

  `2^{-n} · |D_n|  =×  m(n)  =×  2^{-K(n)}`.

Both directions come from Theorem 1.7.1, but in an asymmetric way.

* **`≤×`** is the length-projection idea: the machine that runs `U` and outputs the
  *length of its own program* (`selfLenMap`) assigns to `n` exactly the mass
  `2^{-n} · |D_n|`; the coding theorem transfers that mass to `U`.
* **`≥×`** does **not** sum Theorem 1.7.1 over all outputs, which is the route in
  the source and which fails here because the lower bound's premise depends on the
  output. Instead it applies the lower bound at the single output `x = []`: programs
  producing `[]` are halting programs, so `|D_n| ≥ f([], n)`, and `K(⟨[], n⟩) =⁺ K(n)`
  because pairing with a fixed string is computable. The resulting premise
  `K(n) + c ≤ n` is the same guard the repository already carries in
  `card_KPPlain_le_lower_bound_faithful`.

Numbers are encoded as `natCode n`, consistently with the rest of this directory.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The halting set `D_n` -/

open Classical in
/-- **`D_n`**: the halting programs of length exactly `n`, in the empty context. -/
noncomputable def haltSet (U : Map) (n : ℕ) : Finset BitString :=
  (stringsOfLength n).filter (fun p ↦ (U (p, [])).Dom)

/-- Membership in `D_n`, unfolded. -/
theorem mem_haltSet {U : Map} {p : BitString} {n : ℕ} :
    p ∈ haltSet U n ↔ p.length = n ∧ (U (p, [])).Dom := by
  classical
  simp [haltSet, Finset.mem_filter, memStringsOfLength]

/-- **`|D_n|`**, the number of halting programs of length `n`. -/
noncomputable def haltCount (U : Map) (n : ℕ) : ℕ := (haltSet U n).card

/-- The length-`n` programs for any fixed output are halting programs of length `n`. -/
theorem progSet_subset_haltSet (U : Map) (x : BitString) (n : ℕ) :
    progSet U x n ⊆ haltSet U n := by
  classical
  intro p hp
  rw [mem_progSet] at hp
  exact mem_haltSet.mpr ⟨hp.1, Part.dom_iff_mem.mpr ⟨x, hp.2⟩⟩

/-- `f(x, n) ≤ |D_n|` for every output `x`. -/
theorem progCount_le_haltCount (U : Map) (x : BitString) (n : ℕ) :
    progCount U x n ≤ haltCount U n :=
  Finset.card_le_card (progSet_subset_haltSet U x n)

/-! ### The length-output machine and the halting slice -/

/-- The **self-length machine**: run `U` on the program (empty context) and, if it
halts, output the unary code of the *program's own length*. -/
def selfLenMap (U : Map) : Map :=
  fun pr ↦ (U (pr.1, [])).map (fun _ ↦ natCode pr.1.length)

/-- Membership characterisation of the self-length machine. -/
theorem produces_selfLenMap_iff (U : Map) (p y w : BitString) :
    produces (selfLenMap U) p y w ↔ ∃ z, produces U p [] z ∧ natCode p.length = w := by
  change w ∈ Part.map (fun _ ↦ natCode p.length) (U (p, [])) ↔
    ∃ z, produces U p [] z ∧ natCode p.length = w
  rw [Part.mem_map_iff]

/-- The halting domain of the self-length machine is `U`'s domain in the empty
context. -/
theorem domainAt_selfLenMap (U : Map) (y : BitString) :
    domainAt (selfLenMap U) y = domainAt U [] := rfl

/-- **The self-length machine is a prefix decompressor** whenever `U` is. -/
theorem selfLenMap_isPrefixDecompressor (U : Map) (hU : IsPrefixDecompressor U) :
    IsPrefixDecompressor (selfLenMap U) := by
  refine ⟨?_, ?_⟩
  · have hf : Partrec (fun pr : BitString × BitString ↦ U (pr.1, [])) :=
      hU.isDecompressor.comp (Computable.fst.pair (Computable.const []))
    have hg : Computable₂
        (fun (pr : BitString × BitString) (_ : BitString) ↦ natCode pr.1.length) :=
      (natCode_primrec.to_comp.comp
        (Computable.list_length.comp (Computable.fst.comp Computable.fst))).to₂
    exact (hf.map hg).of_eq (fun pr ↦ rfl)
  · intro y
    rw [domainAt_selfLenMap]
    exact hU.isPrefixMachine []

/-- A halting program of length `n` is a program for `natCode n` on the self-length
machine. -/
theorem produces_selfLenMap_of_mem_haltSet {U : Map} {p : BitString} {n : ℕ}
    (hp : p ∈ haltSet U n) :
    produces (selfLenMap U) p [] (natCode n) := by
  obtain ⟨hlen, hdom⟩ := mem_haltSet.mp hp
  obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp hdom
  exact (produces_selfLenMap_iff U p [] (natCode n)).mpr ⟨z, hz, by rw [hlen]⟩

/-- The **halting slice**: the total a priori weight of `D_n`. -/
noncomputable def haltSlice (U : Map) (n : ℕ) : ℝ≥0∞ :=
  ∑ p ∈ haltSet U n, progWeight p

/-- `haltSlice U n = 2^{-n} · |D_n|`. -/
theorem haltSlice_eq_haltCount (U : Map) (n : ℕ) :
    haltSlice U n = (2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞) := by
  classical
  have hconst : ∀ p ∈ haltSet U n, progWeight p = (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro p hp
    simp [progWeight, programLength, (mem_haltSet.mp hp).1]
  rw [haltSlice, Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul,
    haltCount, mul_comm]

/-- The halting slice is dominated by the self-length machine's a priori mass at `n`. -/
theorem haltSlice_le_aprioriMeasure_selfLenMap (U : Map) (n : ℕ) :
    haltSlice U n ≤ aprioriMeasure (selfLenMap U) (natCode n) [] := by
  classical
  unfold haltSlice aprioriMeasure
  calc (∑ p ∈ haltSet U n, progWeight p)
      = ∑ p ∈ haltSet U n,
          (if produces (selfLenMap U) p [] (natCode n) then progWeight p else 0) := by
        refine Finset.sum_congr rfl (fun p hp ↦ ?_)
        rw [if_pos (produces_selfLenMap_of_mem_haltSet hp)]
    _ ≤ ∑' p : BitString,
          (if produces (selfLenMap U) p [] (natCode n) then progWeight p else 0) :=
        ENNReal.sum_le_tsum _

/-! ### Theorem 1.7.2, first half, upper direction -/

/-- **`2^{-n} · |D_n| ≤× m(n)`.** -/
theorem haltCount_le_aprioriMeasure (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ,
      (2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞)
        ≤ (2 : ℝ≥0∞) ^ c * aprioriMeasure U (natCode n) [] := by
  obtain ⟨c, hc⟩ := aprioriMeasure_le_two_pow_mul_aprioriMeasure_optimal hU
    (selfLenMap_isPrefixDecompressor U hU.isPrefixDecompressor)
  refine ⟨c, fun n ↦ ?_⟩
  calc (2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞)
      = haltSlice U n := (haltSlice_eq_haltCount U n).symm
    _ ≤ aprioriMeasure (selfLenMap U) (natCode n) [] :=
        haltSlice_le_aprioriMeasure_selfLenMap U n
    _ ≤ (2 : ℝ≥0∞) ^ c * aprioriMeasure U (natCode n) [] := hc _ _

/-- **`2^{-n} · |D_n| ≤× 2^{-K(n)}`**, the upper direction of `eq:Dn` with the coding
theorem folded in. -/
theorem haltCount_le_complexityWeight (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ,
      (2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞)
        ≤ (2 : ℝ≥0∞) ^ c * complexityWeight (KPPlain U (natCode n)) := by
  obtain ⟨c, hc⟩ := haltCount_le_aprioriMeasure U hU
  obtain ⟨c₁, hc₁⟩ := aprioriMeasure_le_complexityWeight_optimal hU hU.isPrefixDecompressor
  refine ⟨c + c₁, fun n ↦ ?_⟩
  have hm : aprioriMeasure U (natCode n) []
      ≤ (2 : ℝ≥0∞) ^ c₁ * complexityWeight (KPPlain U (natCode n)) :=
    le_two_pow_mul_of_inv_two_pow_mul_le (hc₁ (natCode n) [])
  calc (2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞)
      ≤ (2 : ℝ≥0∞) ^ c * aprioriMeasure U (natCode n) [] := hc n
    _ ≤ (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞) ^ c₁ * complexityWeight (KPPlain U (natCode n))) := by
        gcongr
    _ = (2 : ℝ≥0∞) ^ (c + c₁) * complexityWeight (KPPlain U (natCode n)) := by
        rw [pow_add, mul_assoc]

/-! ### Pairing with the empty string is free -/

/-- `K(⟨[], w⟩) ≤⁺ K(w)`: prepending an empty first component is computable. -/
theorem KPPlain_pairCode_nil_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ w : BitString,
      KPPlain U (pairCode [] w) ≤ KPPlain U w + (c : ENat) := by
  have hf : Partrec (fun w : BitString ↦ (Part.some (pairCode [] w) : Part BitString)) :=
    (pairCode_primrec.to_comp.comp (Computable.const []) Computable.id : Computable _)
  obtain ⟨c, hc⟩ := KPPlain_partrec_map_le U hU _ hf
  exact ⟨c, fun w ↦ hc w _ (Part.mem_some _)⟩

/-! ### Theorem 1.7.2, first half, lower direction -/

/-- **`m(n) ≤× 2^{-n} · |D_n|`** whenever `K(n) + c₀ ≤ n`. Proof: the lower half of
Theorem 1.7.1 at the single output `[]`. -/
theorem aprioriMeasure_le_haltCount (U : Map) (hU : IsPrefixPrependUniversal U) :
    ∃ c₀ c₁ : ℕ, ∀ n : ℕ, KPPlain U (natCode n) + (c₀ : ENat) ≤ (n : ENat) →
      (2 : ℝ≥0∞)⁻¹ ^ c₁ * aprioriMeasure U (natCode n) []
        ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞) := by
  have hUo := hU.isOptimalPrefixConditional
  obtain ⟨d₀, d₁, hlow⟩ := aprioriMeasure_pair_le_progCount U hU
  obtain ⟨c₂, hc₂⟩ := KPPlain_pairCode_nil_le U hUo
  obtain ⟨e₁, he₁⟩ := aprioriMeasure_le_complexityWeight_optimal hUo hUo.isPrefixDecompressor
  refine ⟨c₂ + d₀, d₀ + d₁ + e₁ + c₂, fun n hn ↦ ?_⟩
  -- The premise of the lower bound at `x = []`, from `K(⟨[], n⟩) ≤ K(n) + c₂`.
  have hpair : KPPair U [] (natCode n) ≤ KPPlain U (natCode n) + (c₂ : ENat) :=
    hc₂ (natCode n)
  have hprem : KPPair U [] (natCode n) + (d₀ : ENat) ≤ (n : ENat) := by
    calc KPPair U [] (natCode n) + (d₀ : ENat)
        ≤ (KPPlain U (natCode n) + (c₂ : ENat)) + (d₀ : ENat) := by gcongr
      _ = KPPlain U (natCode n) + ((c₂ + d₀ : ℕ) : ENat) := by rw [add_assoc, Nat.cast_add]
      _ ≤ (n : ENat) := hn
  have hlow' := hlow [] n hprem
  -- `m(n) ≤ 2^{e₁ + c₂} · m(⟨[], n⟩)`: coding both ways through `K(⟨[],n⟩) ≤ K(n) + c₂`.
  have hm : aprioriMeasure U (natCode n) []
      ≤ (2 : ℝ≥0∞) ^ (e₁ + c₂) * aprioriMeasure U (pairCode [] (natCode n)) [] := by
    have h1 : aprioriMeasure U (natCode n) []
        ≤ (2 : ℝ≥0∞) ^ e₁ * complexityWeight (KPPlain U (natCode n)) :=
      le_two_pow_mul_of_inv_two_pow_mul_le (he₁ (natCode n) [])
    have h2 : complexityWeight (KPPlain U (natCode n))
        ≤ (2 : ℝ≥0∞) ^ c₂ * complexityWeight (KPPlain U (pairCode [] (natCode n))) := by
      have h := complexityWeight_le_of_le hpair
      rw [complexityWeight_add_nat, mul_comm] at h
      exact le_two_pow_mul_of_inv_two_pow_mul_le h
    have h3 : complexityWeight (KPPlain U (pairCode [] (natCode n)))
        ≤ aprioriMeasure U (pairCode [] (natCode n)) [] :=
      complexityWeight_KP_le_aprioriMeasure U (pairCode [] (natCode n)) []
    calc aprioriMeasure U (natCode n) []
        ≤ (2 : ℝ≥0∞) ^ e₁ * complexityWeight (KPPlain U (natCode n)) := h1
      _ ≤ (2 : ℝ≥0∞) ^ e₁
            * ((2 : ℝ≥0∞) ^ c₂ * complexityWeight (KPPlain U (pairCode [] (natCode n)))) := by
          gcongr
      _ ≤ (2 : ℝ≥0∞) ^ e₁ * ((2 : ℝ≥0∞) ^ c₂ * aprioriMeasure U (pairCode [] (natCode n)) []) := by
          gcongr
      _ = (2 : ℝ≥0∞) ^ (e₁ + c₂) * aprioriMeasure U (pairCode [] (natCode n)) [] := by
          rw [pow_add, mul_assoc]
  -- Assemble.
  have hcount : (progCount U [] n : ℝ≥0∞) ≤ (haltCount U n : ℝ≥0∞) := by
    exact_mod_cast progCount_le_haltCount U [] n
  calc (2 : ℝ≥0∞)⁻¹ ^ (d₀ + d₁ + e₁ + c₂) * aprioriMeasure U (natCode n) []
      = (2 : ℝ≥0∞)⁻¹ ^ (d₀ + d₁)
          * ((2 : ℝ≥0∞)⁻¹ ^ (e₁ + c₂) * aprioriMeasure U (natCode n) []) := by
        rw [← mul_assoc, ← pow_add]; ring_nf
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ (d₀ + d₁) * aprioriMeasure U (pairCode [] (natCode n)) [] := by
        gcongr
        exact inv_two_pow_mul_le_of_le_two_pow_mul hm
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (progCount U [] n : ℝ≥0∞) := hlow'
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞) := by gcongr

/-- **`2^{-K(n)} ≤× 2^{-n} · |D_n|`** whenever `K(n) + c₀ ≤ n`: the lower direction of
`eq:Dn` in complexity form. -/
theorem complexityWeight_le_haltCount (U : Map) (hU : IsPrefixPrependUniversal U) :
    ∃ c₀ c₁ : ℕ, ∀ n : ℕ, KPPlain U (natCode n) + (c₀ : ENat) ≤ (n : ENat) →
      (2 : ℝ≥0∞)⁻¹ ^ c₁ * complexityWeight (KPPlain U (natCode n))
        ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞) := by
  obtain ⟨c₀, c₁, h⟩ := aprioriMeasure_le_haltCount U hU
  refine ⟨c₀, c₁, fun n hn ↦ ?_⟩
  calc (2 : ℝ≥0∞)⁻¹ ^ c₁ * complexityWeight (KPPlain U (natCode n))
      ≤ (2 : ℝ≥0∞)⁻¹ ^ c₁ * aprioriMeasure U (natCode n) [] := by
        gcongr
        exact complexityWeight_KP_le_aprioriMeasure U (natCode n) []
    _ ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞) := h n hn

end Kolmogorov
