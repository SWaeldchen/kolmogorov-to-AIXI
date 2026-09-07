/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.ComplexityLevels
import KolmogorovMathlib.DescriptionStatistics.ProjectionSecond

/-!
# The Markov half of Theorem 1.7.2's second assertion

`ComplexityLevels` bounds the complexity window from above. This file supplies the
lower bound `2^{-K(n)} ≤× 2^{-n} · windowCount U n c`, completing the second assertion
of Theorem 1.7.2, and packages both halves.

## Gács' argument (source lines 2138–2161)

The programs in `D_n` are themselves objects. Two facts pin their complexities:

* **Upper**: every `p ∈ D_n` has `K(p) ≤ n + c₀`, because the machine that outputs its
  own input whenever `U` halts on it (`idMap`) describes `p` in `|p| = n` bits.
* **Lower, on average**: `Σ_{p ∈ D_n} 2^{-K(p)} ≤× 2^{-K(n)}`. Since `K(p, |p|) =⁺ K(p)`
  (pairing with one's own length is computable) this is the first-component marginal
  of `m` at the second component `n`, which `ProjectionSecond` bounds by `m(n)`.

Combined with `|D_n| ≥× 2^{n − K(n)}` from `HaltingCount`, the average of `2^{-K(p)}`
over `D_n` is at most about `2^{-n}`. **Markov's inequality** then says at most half
of `D_n` can have `2^{-K(p)}` twice that large, so at least half have
`K(p) ≥ n − c₁`. Those programs are objects with complexity in a window of fixed
width around `n`, and distinct programs are distinct objects, so they inject into the
window. Hence `windowCount ≥ |D_n| / 2 ≥× 2^{n − K(n)}`.

Markov's inequality is not taken from Mathlib but written out directly: the "bad"
programs each carry weight at least `2^{c₁+1} · 2^{-n}`, so their number times that
threshold is at most the total, which is at most `2^{c₁} · 2^{-n} · |D_n|`.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Two more `ℝ≥0∞` helpers -/

/-- Move `2^{-c}` from the right of an inequality to the left as `2^c`. -/
theorem two_pow_mul_le_of_le_inv_two_pow_mul {a b : ℝ≥0∞} {c : ℕ}
    (h : a ≤ (2 : ℝ≥0∞)⁻¹ ^ c * b) : (2 : ℝ≥0∞) ^ c * a ≤ b := by
  have hcc : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ c = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  calc (2 : ℝ≥0∞) ^ c * a ≤ (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹ ^ c * b) := by gcongr
    _ = b := by rw [← mul_assoc, hcc, one_mul]

/-- Cancel a common nonzero finite factor of the form `2^i · 2^{-j}`. -/
theorem le_of_mul_two_pow_mul_inv_two_pow_le {a b : ℝ≥0∞} {i j : ℕ}
    (h : a * ((2 : ℝ≥0∞) ^ i * (2 : ℝ≥0∞)⁻¹ ^ j) ≤ b * ((2 : ℝ≥0∞) ^ i * (2 : ℝ≥0∞)⁻¹ ^ j)) :
    a ≤ b := by
  have hi : (2 : ℝ≥0∞) ^ i * (2 : ℝ≥0∞)⁻¹ ^ i = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  have hj : (2 : ℝ≥0∞)⁻¹ ^ j * (2 : ℝ≥0∞) ^ j = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  have hunit : ((2 : ℝ≥0∞) ^ i * (2 : ℝ≥0∞)⁻¹ ^ j) * ((2 : ℝ≥0∞)⁻¹ ^ i * (2 : ℝ≥0∞) ^ j) = 1 := by
    calc ((2 : ℝ≥0∞) ^ i * (2 : ℝ≥0∞)⁻¹ ^ j) * ((2 : ℝ≥0∞)⁻¹ ^ i * (2 : ℝ≥0∞) ^ j)
        = ((2 : ℝ≥0∞) ^ i * (2 : ℝ≥0∞)⁻¹ ^ i) * ((2 : ℝ≥0∞)⁻¹ ^ j * (2 : ℝ≥0∞) ^ j) := by ring
      _ = 1 := by rw [hi, hj, mul_one]
  calc a = a * (((2 : ℝ≥0∞) ^ i * (2 : ℝ≥0∞)⁻¹ ^ j) * ((2 : ℝ≥0∞)⁻¹ ^ i * (2 : ℝ≥0∞) ^ j)) := by
        rw [hunit, mul_one]
    _ = (a * ((2 : ℝ≥0∞) ^ i * (2 : ℝ≥0∞)⁻¹ ^ j)) * ((2 : ℝ≥0∞)⁻¹ ^ i * (2 : ℝ≥0∞) ^ j) := by
        ring
    _ ≤ (b * ((2 : ℝ≥0∞) ^ i * (2 : ℝ≥0∞)⁻¹ ^ j)) * ((2 : ℝ≥0∞)⁻¹ ^ i * (2 : ℝ≥0∞) ^ j) := by
        gcongr
    _ = b := by rw [mul_assoc, hunit, mul_one]

/-! ### The identity machine on the halting set: `K(p) ≤ |p| + c₀` -/

/-- The **identity machine**: run `U` on the program and, if it halts, output the
program itself. -/
def idMap (U : Map) : Map :=
  fun pr ↦ (U (pr.1, [])).map (fun _ ↦ pr.1)

/-- Membership characterisation of the identity machine. -/
theorem produces_idMap_iff (U : Map) (p y w : BitString) :
    produces (idMap U) p y w ↔ ∃ z, produces U p [] z ∧ p = w := by
  change w ∈ Part.map (fun _ ↦ p) (U (p, [])) ↔ ∃ z, produces U p [] z ∧ p = w
  rw [Part.mem_map_iff]

/-- The halting domain of the identity machine is `U`'s domain in the empty context. -/
theorem domainAt_idMap (U : Map) (y : BitString) :
    domainAt (idMap U) y = domainAt U [] := rfl

/-- **The identity machine is a prefix decompressor** whenever `U` is. -/
theorem idMap_isPrefixDecompressor (U : Map) (hU : IsPrefixDecompressor U) :
    IsPrefixDecompressor (idMap U) := by
  refine ⟨?_, ?_⟩
  · have hf : Partrec (fun pr : BitString × BitString ↦ U (pr.1, [])) :=
      hU.isDecompressor.comp (Computable.fst.pair (Computable.const []))
    have hg : Computable₂ (fun (pr : BitString × BitString) (_ : BitString) ↦ pr.1) :=
      (Computable.fst.comp Computable.fst).to₂
    exact (hf.map hg).of_eq (fun pr ↦ rfl)
  · intro y
    rw [domainAt_idMap]
    exact hU.isPrefixMachine []

/-- **Halting programs are cheap to describe**: `K(p) ≤ |p| + c₀` whenever `U` halts
on `p`, since `p` is its own program on the identity machine. -/
theorem KPPlain_le_length_of_dom (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ p : BitString, (U (p, [])).Dom →
      KPPlain U p ≤ (p.length : ENat) + (c : ENat) := by
  obtain ⟨c, hc⟩ := hU.invariance (idMap_isPrefixDecompressor U hU.isPrefixDecompressor)
  refine ⟨c, fun p hp ↦ ?_⟩
  obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp hp
  have hprod : produces (idMap U) p [] p := (produces_idMap_iff U p [] p).mpr ⟨z, hz, rfl⟩
  calc KPPlain U p = KP U p [] := rfl
    _ ≤ KP (idMap U) p [] + (c : ENat) := hc p []
    _ ≤ (p.length : ENat) + (c : ENat) := by
        gcongr
        exact KP_le_programLength_of_produces hprod

/-! ### The average of `2^{-K(p)}` over `D_n` -/

/-- `K(⟨p, |p|⟩) ≤⁺ K(p)`: pairing a string with its own length is computable. -/
theorem KPPlain_pairCode_selfLength_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ p : BitString,
      KPPlain U (pairCode p (natCode p.length)) ≤ KPPlain U p + (c : ENat) := by
  have hprim : Primrec (fun p : BitString ↦ pairCode p (natCode p.length)) :=
    pairCode_primrec.comp Primrec.id (natCode_primrec.comp Primrec.list_length)
  have hf : Partrec (fun p : BitString ↦
      (Part.some (pairCode p (natCode p.length)) : Part BitString)) :=
    hprim.to_comp
  obtain ⟨c, hc⟩ := KPPlain_partrec_map_le U hU _ hf
  exact ⟨c, fun p ↦ hc p _ (Part.mem_some _)⟩

/-- **The total weight of `D_n` as objects is `≤× 2^{-K(n)}`.** Each `2^{-K(p)}` is
at most `2^a · m(⟨p, n⟩)`, and summing those over `p` is bounded by the first-component
marginal at `n`, which `ProjectionSecond` bounds by `m(n)`. -/
theorem sum_complexityWeight_haltSet_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ,
      (∑ p ∈ haltSet U n, complexityWeight (KPPlain U p))
        ≤ (2 : ℝ≥0∞) ^ c * complexityWeight (KPPlain U (natCode n)) := by
  obtain ⟨a, ha⟩ := KPPlain_pairCode_selfLength_le U hU
  obtain ⟨b, hb⟩ := firstMarginal_le_two_pow_mul_aprioriMeasure U hU
  obtain ⟨e, he⟩ := aprioriMeasure_le_complexityWeight_optimal hU hU.isPrefixDecompressor
  refine ⟨a + b + e, fun n ↦ ?_⟩
  classical
  have hterm : ∀ p ∈ haltSet U n,
      complexityWeight (KPPlain U p)
        ≤ (2 : ℝ≥0∞) ^ a * aprioriMeasure U (pairCode p (natCode n)) [] := by
    intro p hp
    have hlen := (mem_haltSet.mp hp).1
    have h1 : complexityWeight (KPPlain U p)
        ≤ (2 : ℝ≥0∞) ^ a * complexityWeight (KPPlain U (pairCode p (natCode p.length))) := by
      have h := complexityWeight_le_of_le (ha p)
      rw [complexityWeight_add_nat, mul_comm] at h
      exact le_two_pow_mul_of_inv_two_pow_mul_le h
    have h2 : complexityWeight (KPPlain U (pairCode p (natCode p.length)))
        ≤ aprioriMeasure U (pairCode p (natCode p.length)) [] :=
      complexityWeight_KP_le_aprioriMeasure U _ []
    rw [hlen] at h1 h2
    exact h1.trans (by gcongr)
  calc (∑ p ∈ haltSet U n, complexityWeight (KPPlain U p))
      ≤ ∑ p ∈ haltSet U n, (2 : ℝ≥0∞) ^ a * aprioriMeasure U (pairCode p (natCode n)) [] :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ≥0∞) ^ a * ∑ p ∈ haltSet U n, aprioriMeasure U (pairCode p (natCode n)) [] := by
        rw [Finset.mul_sum]
    _ ≤ (2 : ℝ≥0∞) ^ a * ∑' x : BitString, aprioriMeasure U (pairCode x (natCode n)) [] := by
        gcongr
        exact ENNReal.sum_le_tsum _
    _ = (2 : ℝ≥0∞) ^ a * firstMarginal U (natCode n) [] := by rw [firstMarginal_def]
    _ ≤ (2 : ℝ≥0∞) ^ a * ((2 : ℝ≥0∞) ^ b * aprioriMeasure U (natCode n) []) := by
        gcongr
        exact hb (natCode n)
    _ ≤ (2 : ℝ≥0∞) ^ a
          * ((2 : ℝ≥0∞) ^ b * ((2 : ℝ≥0∞) ^ e * complexityWeight (KPPlain U (natCode n)))) := by
        gcongr
        exact le_two_pow_mul_of_inv_two_pow_mul_le (he (natCode n) [])
    _ = (2 : ℝ≥0∞) ^ (a + b + e) * complexityWeight (KPPlain U (natCode n)) := by ring

/-! ### Markov: the compressible programs are at most half of `D_n` -/

open Classical in
/-- The **bad set**: halting programs of length `n` that are too compressible,
`K(p) + (c₁ + 1) ≤ n`. -/
noncomputable def badSet (U : Map) (n c₁ : ℕ) : Finset BitString :=
  (haltSet U n).filter (fun p ↦ KPPlain U p + ((c₁ + 1 : ℕ) : ENat) ≤ (n : ENat))

/-- Membership in the bad set, unfolded. -/
theorem mem_badSet {U : Map} {n c₁ : ℕ} {p : BitString} :
    p ∈ badSet U n c₁ ↔ p ∈ haltSet U n ∧ KPPlain U p + ((c₁ + 1 : ℕ) : ENat) ≤ (n : ENat) := by
  classical
  simp [badSet, Finset.mem_filter]

/-- The bad set sits inside `D_n`. -/
theorem badSet_subset_haltSet (U : Map) (n c₁ : ℕ) : badSet U n c₁ ⊆ haltSet U n :=
  fun _ hp ↦ (mem_badSet.mp hp).1

/-- Each bad program carries weight at least `2^{c₁+1} · 2^{-n}`. -/
theorem two_pow_mul_le_complexityWeight_of_mem_badSet {U : Map} {n c₁ : ℕ} {p : BitString}
    (hp : p ∈ badSet U n c₁) :
    (2 : ℝ≥0∞) ^ (c₁ + 1) * (2 : ℝ≥0∞)⁻¹ ^ n ≤ complexityWeight (KPPlain U p) := by
  have h := complexityWeight_le_of_le (mem_badSet.mp hp).2
  rw [complexityWeight_add_nat, complexityWeight_coe, mul_comm] at h
  exact two_pow_mul_le_of_le_inv_two_pow_mul h

/-- **Markov.** Under the guard `K(n) + c₀ ≤ n`, at most half of `D_n` is bad. -/
theorem two_mul_card_badSet_le (U : Map) (hU : IsPrefixPrependUniversal U) :
    ∃ c₀ c₁ : ℕ, ∀ n : ℕ, KPPlain U (natCode n) + (c₀ : ENat) ≤ (n : ENat) →
      2 * (badSet U n c₁).card ≤ haltCount U n := by
  have hUo := hU.isOptimalPrefixConditional
  obtain ⟨C, hC⟩ := sum_complexityWeight_haltSet_le U hUo
  obtain ⟨c₀, c', hlow⟩ := complexityWeight_le_haltCount U hU
  refine ⟨c₀, C + c', fun n hn ↦ ?_⟩
  classical
  -- Each bad program weighs at least the threshold, so `|bad| · threshold ≤ Σ_bad`.
  have h1 : ((badSet U n (C + c')).card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (C + c' + 1) * (2 : ℝ≥0∞)⁻¹ ^ n)
      ≤ ∑ p ∈ badSet U n (C + c'), complexityWeight (KPPlain U p) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum (fun p hp ↦ two_pow_mul_le_complexityWeight_of_mem_badSet hp)
  -- `Σ_bad ≤ Σ_{D_n}`, by extending the sum with nonnegative terms.
  have h2 : (∑ p ∈ badSet U n (C + c'), complexityWeight (KPPlain U p))
      ≤ ∑ p ∈ haltSet U n, complexityWeight (KPPlain U p) := by
    rw [badSet, Finset.sum_filter]
    exact Finset.sum_le_sum (fun p _ ↦ by split_ifs <;> simp)
  -- `Σ_{D_n} ≤ 2^C · 2^{-K(n)} ≤ 2^{C+c'} · 2^{-n} · |D_n|`.
  have h3 : complexityWeight (KPPlain U (natCode n))
      ≤ (2 : ℝ≥0∞) ^ c' * ((2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞)) :=
    le_two_pow_mul_of_inv_two_pow_mul_le (hlow n hn)
  have h4 : ((badSet U n (C + c')).card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (C + c' + 1) * (2 : ℝ≥0∞)⁻¹ ^ n)
      ≤ (haltCount U n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (C + c') * (2 : ℝ≥0∞)⁻¹ ^ n) := by
    calc _ ≤ _ := h1
      _ ≤ _ := h2
      _ ≤ (2 : ℝ≥0∞) ^ C * complexityWeight (KPPlain U (natCode n)) := hC n
      _ ≤ (2 : ℝ≥0∞) ^ C * ((2 : ℝ≥0∞) ^ c' * ((2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞))) := by
          gcongr
      _ = (haltCount U n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (C + c') * (2 : ℝ≥0∞)⁻¹ ^ n) := by ring
  -- Peel the extra factor `2` off the threshold and cancel the common `2^{C+c'} · 2^{-n}`.
  have h5 : ((2 * (badSet U n (C + c')).card : ℕ) : ℝ≥0∞)
        * ((2 : ℝ≥0∞) ^ (C + c') * (2 : ℝ≥0∞)⁻¹ ^ n)
      ≤ (haltCount U n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (C + c') * (2 : ℝ≥0∞)⁻¹ ^ n) := by
    calc ((2 * (badSet U n (C + c')).card : ℕ) : ℝ≥0∞)
          * ((2 : ℝ≥0∞) ^ (C + c') * (2 : ℝ≥0∞)⁻¹ ^ n)
        = ((badSet U n (C + c')).card : ℝ≥0∞)
            * ((2 : ℝ≥0∞) ^ (C + c' + 1) * (2 : ℝ≥0∞)⁻¹ ^ n) := by
          push_cast; ring
      _ ≤ _ := h4
  exact_mod_cast le_of_mul_two_pow_mul_inv_two_pow_le h5

/-! ### The good programs lie in the window -/

/-- A halting program of length `n` that is not bad has complexity within a fixed
window of `n`: at most `n + c₀` by `KPPlain_le_length_of_dom`, and more than
`n − c₁ − 1` by not being bad. -/
theorem sdiff_badSet_subset_windowSet (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c₀ : ℕ, ∀ n c₁ : ℕ,
      (↑(haltSet U n \ badSet U n c₁) : Set BitString) ⊆ windowSet U n (max c₀ c₁) := by
  obtain ⟨c₀, hc₀⟩ := KPPlain_le_length_of_dom U hU
  refine ⟨c₀, fun n c₁ p hp ↦ ?_⟩
  rw [Finset.mem_coe, Finset.mem_sdiff] at hp
  obtain ⟨hhalt, hnotbad⟩ := hp
  obtain ⟨hlen, hdom⟩ := mem_haltSet.mp hhalt
  have hup : KPPlain U p ≤ (n : ENat) + (c₀ : ENat) := by
    have := hc₀ p hdom; rwa [hlen] at this
  have hne : KPPlain U p ≠ ⊤ := ne_top_of_le_ne_top (by simp) hup
  have hnb : ¬ (KPPlain U p + ((c₁ + 1 : ℕ) : ENat) ≤ (n : ENat)) := fun h ↦
    hnotbad (mem_badSet.mpr ⟨hhalt, h⟩)
  -- Pass to the natural-number value `k = K(p)`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ENat) = KPPlain U p := by
    lift KPPlain U p to ℕ using hne with k hk
    exact ⟨k, rfl⟩
  have hk_up : k ≤ n + c₀ := by
    have : (k : ENat) ≤ ((n + c₀ : ℕ) : ENat) := by rw [hk]; exact_mod_cast hup
    exact_mod_cast this
  have hk_lo : n ≤ k + c₁ := by
    by_contra hcon
    apply hnb
    rw [← hk]
    exact_mod_cast (by omega : k + (c₁ + 1) ≤ n)
  refine ⟨k, hk, ?_, ?_⟩
  · calc n ≤ k + c₁ := hk_lo
      _ ≤ k + max c₀ c₁ := by gcongr; exact le_max_right _ _
  · calc k ≤ n + c₀ := hk_up
      _ ≤ n + max c₀ c₁ := by gcongr; exact le_max_left _ _

/-! ### The lower half -/

/-- **Theorem 1.7.2, second assertion, lower direction.** There are a window width
`c` and constants `c₀, c₁` such that whenever `K(n) + c₀ ≤ n`,
`2^{-c₁} · 2^{-K(n)} ≤ 2^{-n} · windowCount U n c`. -/
theorem complexityWeight_le_windowCount (U : Map) (hU : IsPrefixPrependUniversal U) :
    ∃ c c₀ c₁ : ℕ, ∀ n : ℕ, KPPlain U (natCode n) + (c₀ : ENat) ≤ (n : ENat) →
      (2 : ℝ≥0∞)⁻¹ ^ c₁ * complexityWeight (KPPlain U (natCode n))
        ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (windowCount U n c : ℝ≥0∞) := by
  have hUo := hU.isOptimalPrefixConditional
  obtain ⟨b₀, cb, hbad⟩ := two_mul_card_badSet_le U hU
  obtain ⟨g₀, hgood⟩ := sdiff_badSet_subset_windowSet U hUo
  obtain ⟨d₀, d₁, hlow⟩ := complexityWeight_le_haltCount U hU
  refine ⟨max g₀ cb, max b₀ d₀, d₁ + 1, fun n hn ↦ ?_⟩
  classical
  -- Both guards follow from the combined one.
  have hn_b : KPPlain U (natCode n) + (b₀ : ENat) ≤ (n : ENat) :=
    le_trans (by gcongr; exact_mod_cast le_max_left b₀ d₀) hn
  have hn_d : KPPlain U (natCode n) + (d₀ : ENat) ≤ (n : ENat) :=
    le_trans (by gcongr; exact_mod_cast le_max_right b₀ d₀) hn
  -- Counting: `|D_n| ≤ 2 · |good|` and `|good| ≤ windowCount`.
  have h2bad := hbad n hn_b
  have hpart : (haltSet U n \ badSet U n cb).card + (badSet U n cb).card = haltCount U n :=
    Finset.card_sdiff_add_card_eq_card (badSet_subset_haltSet U n cb)
  have h2good : haltCount U n ≤ 2 * (haltSet U n \ badSet U n cb).card := by omega
  have hgw : (haltSet U n \ badSet U n cb).card ≤ windowCount U n (max g₀ cb) := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard (hgood n cb) (windowSet_finite U n _)
  -- Assemble.
  have hlow' := hlow n hn_d
  have hcount : (haltCount U n : ℝ≥0∞) ≤ 2 * (windowCount U n (max g₀ cb) : ℝ≥0∞) := by
    have : haltCount U n ≤ 2 * windowCount U n (max g₀ cb) := by omega
    exact_mod_cast this
  calc (2 : ℝ≥0∞)⁻¹ ^ (d₁ + 1) * complexityWeight (KPPlain U (natCode n))
      = (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹ ^ d₁ * complexityWeight (KPPlain U (natCode n))) := by
        rw [pow_succ]; ring
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹ ^ n * (haltCount U n : ℝ≥0∞)) := by gcongr
    _ ≤ (2 : ℝ≥0∞)⁻¹ * ((2 : ℝ≥0∞)⁻¹ ^ n * (2 * (windowCount U n (max g₀ cb) : ℝ≥0∞))) := by
        gcongr
    _ = (2 : ℝ≥0∞)⁻¹ ^ n * (windowCount U n (max g₀ cb) : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ * 2) := by
        ring
    _ = (2 : ℝ≥0∞)⁻¹ ^ n * (windowCount U n (max g₀ cb) : ℝ≥0∞) := by
        rw [ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]

/-! ### Theorem 1.7.2, second assertion, packaged -/

/-- **Theorem 1.7.2, second assertion.** There is a window width `c` and constants
`c₀, c₁` such that for all `n` with `K(n) + c₀ ≤ n`,

  `2^{-c₁} · 2^{-K(n)} ≤ 2^{-n} · windowCount U n c ≤ 2^{c₁} · 2^{-K(n)}`,

i.e. `log windowCount U n c =⁺ n − K(n)`. The window count is Gács' moving average
`h_T(n, c)` without its normalising factor `1/(2c+1)`. -/
theorem windowCount_eq_complexityWeight (U : Map) (hU : IsPrefixPrependUniversal U) :
    ∃ c c₀ c₁ : ℕ, ∀ n : ℕ, KPPlain U (natCode n) + (c₀ : ENat) ≤ (n : ENat) →
      (2 : ℝ≥0∞)⁻¹ ^ c₁ * complexityWeight (KPPlain U (natCode n))
          ≤ (2 : ℝ≥0∞)⁻¹ ^ n * (windowCount U n c : ℝ≥0∞) ∧
      (2 : ℝ≥0∞)⁻¹ ^ n * (windowCount U n c : ℝ≥0∞)
          ≤ (2 : ℝ≥0∞) ^ c₁ * complexityWeight (KPPlain U (natCode n)) := by
  obtain ⟨c, c₀, l₁, hlow⟩ := complexityWeight_le_windowCount U hU
  obtain ⟨u₁, hup⟩ := windowCount_le_complexityWeight U hU.isOptimalPrefixConditional c
  refine ⟨c, c₀, l₁ + u₁, fun n hn ↦ ⟨?_, ?_⟩⟩
  · have hpow : (2 : ℝ≥0∞)⁻¹ ^ (l₁ + u₁) ≤ (2 : ℝ≥0∞)⁻¹ ^ l₁ :=
      pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two) (Nat.le_add_right l₁ u₁)
    calc (2 : ℝ≥0∞)⁻¹ ^ (l₁ + u₁) * complexityWeight (KPPlain U (natCode n))
        ≤ (2 : ℝ≥0∞)⁻¹ ^ l₁ * complexityWeight (KPPlain U (natCode n)) :=
          mul_le_mul' hpow le_rfl
      _ ≤ _ := hlow n hn
  · calc _ ≤ (2 : ℝ≥0∞) ^ u₁ * complexityWeight (KPPlain U (natCode n)) := hup n
      _ ≤ (2 : ℝ≥0∞) ^ (l₁ + u₁) * complexityWeight (KPPlain U (natCode n)) := by
          gcongr
          · exact one_le_two
          · exact Nat.le_add_left u₁ l₁

end Kolmogorov
