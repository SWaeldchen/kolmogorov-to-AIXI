/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.Descriptions

/-!
# Gács Theorem 2.3.3 with explicit constants `K(d) + K(P)`

The key lemma of `LevinSchnorr.lean` (`seqVal_le_of_isIntegrableSeqTest`) dominates every
integrable test on sequences by `R(ξ) = sup_n 2^{-K(ξ_{1:n})}/P(ξ_{1:n})` with an existential
constant. Here the constant is made explicit:

  `2^{-K(y_d)} 2^{-K(y_P)} T(ξ) ≤ 2^c R(ξ)`   (`seqVal_le_exact`),

with `c` independent of `P`, `T` and `ξ`, for any descriptions `y_d` of `T` and `y_P` of `P`
(`IsLSCDescription`). Additively: `d(ξ) ≤ d̄_P(ξ) + K(d) + K(P) + c`, which is Gács'
Theorem 2.3.3 (`seqVal_le_canonicalSeqTest_exact`, `seqVal_le_exact'`).

## Proof

The proof of the key lemma is run uniformly in a pair description `z = ⟨y_d, y_P⟩`:

* the approximation `exactApprox z = enumApprox (bitsToNat (decodeFirst z))` of the test is
  primitive recursive in `(z, s, x)`;
* the computability of `hitB`/`firstB`/`gamN` is re-proved with a parameter
  (`gamN_computable_param`), so `γ_z(x) = gamN (exactApprox z) x` is computable in `(z, x)`;
* the family `G(x, z) = f_{decodeSecond z}(x) · γ_z(x)` (`seqExactFamily`) is jointly lower
  semicomputable, and at `z = ⟨y_d, y_P⟩` it is `P(x) γ(x)`, a semimeasure by the layer cake
  (`tsum_mass_mul_gamN_le`);
* `indexed_domination_trim` and `K(⟨y, y'⟩) ≤⁺ K(y) + K(y')` give
  `W γ(x) ≤ 2^c 2^{-K(x)}/P(x)` with `W = 2^{-K(y_d)} 2^{-K(y_P)}`;
* the level argument of the key lemma is run with the bound `W⁻¹ 2^c R(ξ)`, and the final
  inequality is multiplied by `W ≤ 1`. The additive `2` of the converse layer cake is absorbed
  by `R(ξ) ≥ 2^{-K(Λ)}`, a constant depending only on `U`.
-/

namespace Kolmogorov.Randomness

open scoped ENNReal

/-! ### Computability of `γ` with a parameter -/

section Param

variable {α : Type*} [Primcodable α]

theorem pmApprox_computable_param {a : α → ℕ → BitString → ℕ}
    (ha : Computable (fun p : α × ℕ × BitString ↦ a p.1 p.2.1 p.2.2)) :
    Computable (fun p : α × ℕ × BitString ↦ pmApprox (a p.1) p.2.1 p.2.2) := by
  have hg : Computable (fun q : (α × ℕ × BitString) × ℕ ↦
      a q.1.1 q.1.2.1 (q.1.2.2.take q.2)) := by
    have h := ha.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (primrec_list_take.to_comp.comp
          (Computable.snd.comp (Computable.snd.comp Computable.fst))
          (Computable.snd (α := α × ℕ × BitString) (β := ℕ)))))
    exact h.of_eq fun _ ↦ rfl
  have h := computable_finset_range_sup (fun p : α × ℕ × BitString ↦ p.2.2.length + 1)
    (fun (p : α × ℕ × BitString) k ↦ a p.1 p.2.1 (p.2.2.take k))
    (Computable.succ.comp (Computable.list_length.comp (Computable.snd.comp Computable.snd))) hg
  exact h.of_eq fun _ ↦ rfl

theorem hitB_computable_param {a : α → ℕ → BitString → ℕ}
    (ha : Computable (fun p : α × ℕ × BitString ↦ a p.1 p.2.1 p.2.2)) :
    Computable (fun p : α × ℕ × BitString ↦ hitB (a p.1) p.2.1 p.2.2) := by
  have hpm := (pmApprox_computable_param ha).comp
    (Computable.pair (Computable.fst (α := α) (β := ℕ × BitString))
      (Computable.pair (Computable.list_length.comp (Computable.snd.comp Computable.snd))
        (Computable.snd.comp Computable.snd)))
  have hl := natPow_primrec.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_length.comp
        (Primrec.snd.comp (Primrec.snd (α := α) (β := ℕ × BitString)))))
  have h := natLt_primrec.to_comp.comp (Computable.pair hl.to_comp hpm)
  exact h.of_eq fun _ ↦ rfl

theorem firstB_computable_param {a : α → ℕ → BitString → ℕ}
    (ha : Computable (fun p : α × ℕ × BitString ↦ a p.1 p.2.1 p.2.2)) :
    Computable (fun p : α × ℕ × BitString ↦ firstB (a p.1) p.2.1 p.2.2) := by
  have hh := hitB_computable_param ha
  have hterm : Computable₂ (fun (p : α × ℕ × BitString) (j : ℕ) ↦
      if hitB (a p.1) p.2.1 (p.2.2.take j) then 1 else 0) := by
    have h1 := hh.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst))
        (primrec_list_take.to_comp.comp
          (Computable.snd.comp (Computable.snd.comp Computable.fst))
          (Computable.snd (α := α × ℕ × BitString) (β := ℕ)))))
    have h2 := Computable.cond h1 (Computable.const 1) (Computable.const 0)
    exact h2.of_eq fun q ↦ by
      dsimp only; cases hitB (a q.1.1) q.1.2.1 (q.1.2.2.take q.2) <;> rfl
  have hsum := computable_range_sum _ hterm (fun p ↦ p.2.2.length)
    (Computable.list_length.comp (Computable.snd.comp Computable.snd))
  have hz := (Kolmogorov.Randomness.natLe_primrec.to_comp.comp
    (Computable.pair hsum (Computable.const 0)))
  have h := Primrec.and.to_comp.comp hh hz
  exact h.of_eq fun p ↦ by simp [firstB]

theorem gamN_computable_param {a : α → ℕ → BitString → ℕ}
    (ha : Computable (fun p : α × ℕ × BitString ↦ a p.1 p.2.1 p.2.2)) :
    Computable (fun p : α × BitString ↦ gamN (a p.1) p.2) := by
  have hterm : Computable₂ (fun (p : α × BitString) (k : ℕ) ↦
      if firstB (a p.1) k p.2 then 2 ^ k else 0) := by
    have h1 := (firstB_computable_param ha).comp
      (Computable.pair (Computable.fst.comp Computable.fst)
        (Computable.pair (Computable.snd (α := α × BitString) (β := ℕ))
          (Computable.snd.comp Computable.fst)))
    have h2 := Computable.cond h1
      (natPow_primrec.to_comp.comp (Computable.const 2) Computable.snd) (Computable.const 0)
    exact h2.of_eq fun q ↦ by dsimp only; cases firstB (a q.1.1) q.2 q.1.2 <;> rfl
  have hb := (pmApprox_computable_param ha).comp
    (Computable.pair (Computable.fst (α := α) (β := BitString))
      (Computable.pair (Computable.list_length.comp Computable.snd) Computable.snd))
  have h := computable_range_sum _ hterm (fun p ↦ pmApprox (a p.1) p.2.length p.2) hb
  exact h.of_eq fun _ ↦ rfl

end Param

/-! ### The approximation read from a description, uniformly -/

/-- The enumerated approximation of the function described by `y`. -/
def descApprox (y : BitString) (s : ℕ) (x : BitString) : ℕ :=
  enumApprox (bitsToNat y) s x

/-- The approximation of the test read from the first component of a pair description. -/
def exactApprox (z : BitString) : ℕ → BitString → ℕ :=
  descApprox (decodeFirst z)

theorem exactApprox_pairCode (y y' : BitString) : exactApprox (pairCode y y') = descApprox y := by
  unfold exactApprox; rw [decodeFirst_pairCode]

theorem exactApprox_computable :
    Computable (fun p : BitString × ℕ × BitString ↦ exactApprox p.1 p.2.1 p.2.2) := by
  have h := enumApprox_primrec.to_comp.comp (Computable.pair
    (bitsToNat_computable.comp (decodeFirst_computable.comp Computable.fst))
    (Computable.snd (α := BitString) (β := ℕ × BitString)))
  exact h.of_eq fun _ ↦ rfl

theorem descApprox_mono (y : BitString) (s : ℕ) (x : BitString) :
    dyadicValue (descApprox y s x) s ≤ dyadicValue (descApprox y (s + 1) x) (s + 1) :=
  makeMono_mono _ s x []

/-! ### The family `G(x, z) = P_z(x) · γ_z(x)` -/

/-- `G(x, ⟨y_d, y_P⟩) = f_{y_P}(x) · γ_{y_d}(x)`. -/
noncomputable def seqExactFamily (x z : BitString) : ℝ≥0∞ :=
  descVal (decodeSecond z) x * (gamN (exactApprox z) x : ℝ≥0∞)

theorem seqExactFamily_isLSC : IsLSC seqExactFamily := by
  have h1 := IsLSC.comp₁ descVal_isLSC decodeFirst_computable
    (decodeSecond_computable.comp decodeSecond_computable)
  have hg : Computable (fun q : BitString ↦
      gamN (exactApprox (decodeSecond q)) (decodeFirst q)) := by
    have h := (gamN_computable_param exactApprox_computable).comp
      (Computable.pair decodeSecond_computable decodeFirst_computable)
    exact h.of_eq fun _ ↦ rfl
  refine IsLSC.congr' ((h1.mul (isLSC₁_natCast hg)).toLSC₂ pairCode_computable) fun x z ↦ ?_
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, seqExactFamily]

theorem seqExactFamily_pairCode (yd yP x : BitString) :
    seqExactFamily x (pairCode yd yP) = descVal yP x * (gamN (descApprox yd) x : ℝ≥0∞) := by
  rw [seqExactFamily, decodeSecond_pairCode, exactApprox_pairCode]

/-! ### The weights are at most one -/

theorem prefixComplexityWeight_le_one_of_optimal (U : Map) (hU : IsOptimalPrefixConditional U)
    (x : BitString) : prefixComplexityWeight U x ≤ 1 := by
  obtain ⟨k, -, hw⟩ := exists_weight_eq U hU x
  rw [hw]
  exact pow_le_one₀ zero_le (ENNReal.inv_le_one.mpr one_le_two)

/-! ### Theorem 2.3.3 with explicit constants -/

/-- **Gács Theorem 2.3.3 (key lemma) with explicit constants.** For every integrable test `T`
on sequences for `P`, and descriptions `y_d` of `T` and `y_P` of `P`,
`2^{-K(y_d)} 2^{-K(y_P)} T(ξ) ≤ 2^c sup_n 2^{-K(ξ_{1:n})} / P(ξ_{1:n})`, with `c` independent
of `P`, `T` and `ξ`. -/
theorem seqVal_le_exact (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : ComputableSeqMeasure) (T : BitString → ℝ≥0∞), IsIntegrableSeqTest P T →
      ∀ yd yP : BitString, IsLSCDescription yd T → IsLSCDescription yP P.mass → ∀ ξ,
        prefixComplexityWeight U yd * prefixComplexityWeight U yP * seqVal T ξ ≤
          2 ^ c * complexityRatioSup U P ξ := by
  obtain ⟨c₁, hc₁⟩ := indexed_domination_trim U hU seqExactFamily_isLSC
  obtain ⟨c₂, hc₂⟩ := exists_pairCode_weight U hU
  obtain ⟨c₀, hc₀⟩ := exists_inv_two_pow_le_of_pos
    (pos_iff_ne_zero.mpr (prefixComplexityWeight_ne_zero_of_optimal U hU []))
  refine ⟨max (c₀ + 1) (c₁ + c₂ + 2) + 1, fun P T hT yd yP hdT hdP ξ ↦ ?_⟩
  obtain ⟨_, hTm, hint⟩ := hT
  have hmono : ∀ s x, dyadicValue (descApprox yd s x) s ≤
      dyadicValue (descApprox yd (s + 1) x) (s + 1) := descApprox_mono yd
  have hsup : ∀ x, ⨆ s, dyadicValue (descApprox yd s x) s = T x := fun x ↦ hdT x
  -- The family at the valid index is `P γ`, a semimeasure.
  have hfam : ∀ x, seqExactFamily x (pairCode yd yP) =
      P.mass x * (gamN (descApprox yd) x : ℝ≥0∞) := fun x ↦ by
    rw [seqExactFamily_pairCode, hdP.descVal_eq]
  have hsum : ∑' x, seqExactFamily x (pairCode yd yP) ≤ 1 := by
    simp_rw [hfam]; exact tsum_mass_mul_gamN_le hsup hTm hint
  -- The weight `W = 2^{-K(y_d)} 2^{-K(y_P)}`.
  obtain ⟨W, hWdef⟩ : ∃ W, W = prefixComplexityWeight U yd * prefixComplexityWeight U yP :=
    ⟨_, rfl⟩
  rw [← hWdef]
  have hWpair : W ≤ 2 ^ c₂ * prefixComplexityWeight U (pairCode yd yP) := by
    rw [hWdef]; exact hc₂ yd yP
  have hW0 : W ≠ 0 := by
    rw [hWdef]
    exact mul_ne_zero (prefixComplexityWeight_ne_zero_of_optimal U hU yd)
      (prefixComplexityWeight_ne_zero_of_optimal U hU yP)
  have hW1 : W ≤ 1 := by
    rw [hWdef]
    exact mul_le_one' (prefixComplexityWeight_le_one_of_optimal U hU yd)
      (prefixComplexityWeight_le_one_of_optimal U hU yP)
  have hWtop : W ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hW1
  -- `W γ ≤ 2^c w / P`.
  have hγ : ∀ x, W * (gamN (descApprox yd) x : ℝ≥0∞) ≤
      2 ^ (c₁ + c₂) * (prefixComplexityWeight U x / P.mass x) := fun x ↦ by
    refine le_two_pow_mul_div (prefixComplexityWeight_ne_zero_of_optimal U hU x)
      (P.mass_ne_top x) (inv_two_pow_mul_le_of_le ?_)
    have h1 := hc₁ _ hsum x
    rw [hfam] at h1
    calc P.mass x * (W * gamN (descApprox yd) x)
        = W * (P.mass x * gamN (descApprox yd) x) := by ring
      _ ≤ (2 ^ c₂ * prefixComplexityWeight U (pairCode yd yP)) *
            (P.mass x * gamN (descApprox yd) x) := mul_le_mul' hWpair le_rfl
      _ = 2 ^ c₂ * (prefixComplexityWeight U (pairCode yd yP) *
            (P.mass x * gamN (descApprox yd) x)) := by ring
      _ ≤ 2 ^ c₂ * (2 ^ c₁ * prefixComplexityWeight U x) := mul_le_mul' le_rfl h1
      _ = 2 ^ (c₁ + c₂) * prefixComplexityWeight U x := by rw [pow_add]; ring
  set R := complexityRatioSup U P ξ with hR
  have hR0 : (2 : ℝ≥0∞)⁻¹ ^ c₀ ≤ R := by
    calc (2 : ℝ≥0∞)⁻¹ ^ c₀ ≤ prefixComplexityWeight U [] := hc₀
      _ = prefixComplexityWeight U (seqTake ξ 0) / P.mass (seqTake ξ 0) := by
          simp [seqTake, P.root]
      _ ≤ R := le_iSup (fun n ↦ prefixComplexityWeight U (seqTake ξ n) / P.mass (seqTake ξ n)) 0
  -- Every level reached by `T` along `ξ` is bounded by `W⁻¹ 2^c R`.
  have hlev : ∀ n k, (2 : ℝ≥0∞) ^ (k + 1) < T (seqTake ξ n) →
      (2 : ℝ≥0∞) ^ k ≤ W⁻¹ * (2 ^ (c₁ + c₂) * R) := by
    intro n k hk
    obtain ⟨N, hN⟩ := exists_hitB hmono hsup (isPrefixOfSeq_seqTake ξ n) hk
    obtain ⟨m, -, hm⟩ := exists_firstB hN
    have h1 : W * 2 ^ k ≤ 2 ^ (c₁ + c₂) * R := by
      calc W * 2 ^ k ≤ W * gamN (descApprox yd) (seqTake ξ m) :=
            mul_le_mul' le_rfl (two_pow_le_gamN hm)
        _ ≤ 2 ^ (c₁ + c₂) * (prefixComplexityWeight U (seqTake ξ m) / P.mass (seqTake ξ m)) :=
            hγ _
        _ ≤ 2 ^ (c₁ + c₂) * R := mul_le_mul' le_rfl
            (le_iSup (fun n ↦ prefixComplexityWeight U (seqTake ξ n) / P.mass (seqTake ξ n)) m)
    calc (2 : ℝ≥0∞) ^ k = W⁻¹ * (W * 2 ^ k) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hW0 hWtop, one_mul]
      _ ≤ W⁻¹ * (2 ^ (c₁ + c₂) * R) := mul_le_mul' le_rfl h1
  set M := max (c₀ + 1) (c₁ + c₂ + 2)
  have h1 : (2 : ℝ≥0∞) ≤ 2 ^ M * R := by
    calc (2 : ℝ≥0∞) = 2 ^ (c₀ + 1) * 2⁻¹ ^ c₀ := by
          rw [pow_succ, mul_comm (2 ^ c₀) 2, mul_assoc, ← ENNReal.inv_pow,
            ENNReal.mul_inv_cancel (two_pow_ne_zero' c₀) (two_pow_ne_top' c₀), mul_one]
      _ ≤ 2 ^ M * R := mul_le_mul' (pow_le_pow_right₀ one_le_two (le_max_left _ _)) hR0
  have h2 : 4 * (2 ^ (c₁ + c₂) * R) ≤ 2 ^ M * R := by
    calc 4 * (2 ^ (c₁ + c₂) * R) = 2 ^ (c₁ + c₂ + 2) * R := by rw [pow_add]; ring
      _ ≤ 2 ^ M * R := mul_le_mul' (pow_le_pow_right₀ one_le_two (le_max_right _ _)) le_rfl
  unfold seqVal
  rw [ENNReal.mul_iSup]
  refine iSup_le fun n ↦ ?_
  calc W * T (seqTake ξ n) ≤ W * (2 + 4 * (W⁻¹ * (2 ^ (c₁ + c₂) * R))) :=
        mul_le_mul' le_rfl (le_of_forall_levels (hlev n))
    _ = 2 * W + 4 * (W * W⁻¹) * (2 ^ (c₁ + c₂) * R) := by ring
    _ = 2 * W + 4 * (2 ^ (c₁ + c₂) * R) := by rw [ENNReal.mul_inv_cancel hW0 hWtop, mul_one]
    _ ≤ 2 * 1 + 4 * (2 ^ (c₁ + c₂) * R) := add_le_add (mul_le_mul' le_rfl hW1) le_rfl
    _ ≤ 2 ^ M * R + 2 ^ M * R := by rw [mul_one]; exact add_le_add h1 h2
    _ = 2 ^ (M + 1) * R := by rw [pow_succ]; ring

/-- **Gács Theorem 2.3.3 with explicit constants**, against the canonical universal test:
`d(ξ) ≤ d̄_P(ξ) + K(d) + K(P) + c`, multiplicatively. -/
theorem seqVal_le_canonicalSeqTest_exact (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : ComputableSeqMeasure) (T : BitString → ℝ≥0∞), IsIntegrableSeqTest P T →
      ∀ yd yP : BitString, IsLSCDescription yd T → IsLSCDescription yP P.mass → ∀ ξ,
        prefixComplexityWeight U yd * prefixComplexityWeight U yP * seqVal T ξ ≤
          2 ^ c * seqVal (canonicalSeqTest U P) ξ := by
  obtain ⟨c, hc⟩ := seqVal_le_exact U hU
  exact ⟨c, fun P T hT yd yP hd hP ξ ↦ by
    rw [seqVal_canonicalSeqTest]; exact hc P T hT yd yP hd hP ξ⟩

/-- **Theorem 2.3.3 with constants, additive exponents.** If `K(y_d) = k_d` and
`K(y_P) = k_P`, then `T(ξ) ≤ 2^{c + k_d + k_P} R(ξ)`. -/
theorem seqVal_le_exact' (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : ComputableSeqMeasure) (T : BitString → ℝ≥0∞), IsIntegrableSeqTest P T →
      ∀ (yd yP : BitString) (kd kP : ℕ), IsLSCDescription yd T → IsLSCDescription yP P.mass →
        KP U yd [] = kd → KP U yP [] = kP → ∀ ξ,
          seqVal T ξ ≤ 2 ^ (c + kd + kP) * complexityRatioSup U P ξ := by
  obtain ⟨c, hc⟩ := seqVal_le_exact U hU
  refine ⟨c, fun P T hT yd yP kd kP hd hP hkd hkP ξ ↦ ?_⟩
  have h := hc P T hT yd yP hd hP ξ
  rw [prefixComplexityWeight, prefixComplexityWeight, hkd, hkP, complexityWeight_coe,
    complexityWeight_coe, ← pow_add] at h
  rw [show c + kd + kP = (kd + kP) + c by ring, pow_add, mul_assoc]
  exact le_two_pow_mul_of_inv h

end Kolmogorov.Randomness
