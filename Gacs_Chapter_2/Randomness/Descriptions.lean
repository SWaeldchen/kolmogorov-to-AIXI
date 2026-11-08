/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.RandomizedConservation
import Gacs_Chapter_2.Randomness.RandomnessViaM
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Prefix.Properties

/-!
# Descriptions of lower semicomputable functions and `K`-dependent constants

Gács states his universality results with explicit constants: `d(x) ≤⁺ d̄_P(x) + K(d) + K(P)`
(Theorems 2.2.1, 2.3.3), `m(x) ≥ 2^{-K(ν)} ν(x)` (his `(1.6.x)` "exact domination"). This file
supplies the notion of a *description* and the domination lemma behind all of them.

## Descriptions

A bit string `y` **describes** a lower semicomputable `f : BitString → ℝ≥0∞`
(`IsLSCDescription y f`) when the `bitsToNat y`-th component of the repository's standard
enumeration of lower semicomputable approximations (`enumApprox`, built from `approxEnum`,
i.e. from `Nat.Partrec.Code`s) converges to `f`. `K(f)` in Gács' statements is read as
`K(y)` for a description `y`; every lower semicomputable function has one
(`exists_lscDescription`). Statements below are universally quantified over descriptions,
so they hold in particular for a shortest one.

## Indexed domination

* `indexed_domination`: if `G(x, z)` is jointly lower semicomputable and `G(·, z)` is a
  semimeasure for every `z`, then `2^{-K(z)} G(x, z) ≤ 2^c 2^{-K(x)}` with one `c` for all
  `z`. Proof: `x ↦ ∑_z 2^{-K(z)} G(x, z)` is a lower semicomputable semimeasure (Kraft), so
  the coding theorem applies.
* `indexed_domination_trim`: the same conclusion at every `z` where `G(·, z)` *is* a
  semimeasure, for an arbitrary jointly lower semicomputable `G`; the other indices are
  repaired by the repository's uniform trimming `truncG`.
* `contIndexed_domination`: the continuous analogue, against a universal continuous
  semimeasure `M`.

## Consequences proved here

* `semimeasure_le_exact`: `2^{-K(ν)} ν(x) ≤ 2^c 2^{-K(x)}` for every lower semicomputable
  semimeasure `ν` with description `y` (Gács' exact form of the coding theorem).
* `contSemimeasure_le_univ_exact`: `2^{-K(ν)} ν(x) ≤ 2^c M(x)` for every lower
  semicomputable continuous semimeasure (the form Solomonoff's bound uses).
* **Theorem 2.2.1 with constants** (`integrableTest_le_canonical_exact`):
  `2^{-K(d)} 2^{-K(P)} t(x) ≤ 2^c t_P(x)`, i.e. `d(x) ≤ d̄_P(x) + K(d) + K(P) + c`, via the
  family `G(x, ⟨y, y'⟩) = f_y(x) f_{y'}(x)` and `K(⟨y, y'⟩) ≤⁺ K(y) + K(y')`
  (`exists_pairCode_weight`).
-/

namespace Kolmogorov.Randomness

open scoped ENNReal

/-! ### Small lsc plumbing -/

theorem IsLSC.congr' {F F' : BitString → BitString → ℝ≥0∞} (hF : IsLSC F)
    (e : ∀ x z, F x z = F' x z) : IsLSC F' := by
  obtain ⟨a, h1, h2, h3⟩ := hF
  exact ⟨a, h1, fun x z ↦ (h2 x z).trans (e x z), h3⟩

/-- Reading a jointly lsc function along computable maps gives a unary lsc function. -/
theorem IsLSC.comp₁ {F : BitString → BitString → ℝ≥0∞} (hF : IsLSC F)
    {g h : BitString → BitString} (hg : Computable g) (hh : Computable h) :
    IsLSC₁ (fun q ↦ F (g q) (h q)) := by
  obtain ⟨a, h1, h2, h3⟩ := hF
  refine ⟨fun s q ↦ a s (g q) (h q), fun s q ↦ h1 s _ _, fun q ↦ h2 _ _, ?_⟩
  have := h3.comp (Computable.pair Computable.fst
    (Computable.pair (hg.comp Computable.snd) (hh.comp Computable.snd)))
  exact this.of_eq fun _ ↦ rfl

/-- A unary lsc function read at a computable pairing of two strings is jointly lsc. -/
theorem IsLSC₁.toLSC₂ {Φ : BitString → ℝ≥0∞} (hΦ : IsLSC₁ Φ)
    {e : BitString → BitString → BitString}
    (he : Computable (fun p : BitString × BitString ↦ e p.1 p.2)) :
    IsLSC (fun x z ↦ Φ (e x z)) := by
  obtain ⟨a, h1, h2, h3⟩ := hΦ
  refine ⟨fun s x z ↦ a s (e x z), fun s x z ↦ h1 s _, fun x z ↦ h2 _, ?_⟩
  have := h3.comp (Computable.pair Computable.fst (he.comp Computable.snd))
  exact this.of_eq fun _ ↦ rfl

/-- `2^{-c} a ≤ b` from `a ≤ 2^c b`. -/
theorem inv_two_pow_mul_le_of_le {a b : ℝ≥0∞} {c : ℕ} (h : a ≤ 2 ^ c * b) :
    2⁻¹ ^ c * a ≤ b := by
  calc 2⁻¹ ^ c * a ≤ 2⁻¹ ^ c * (2 ^ c * b) := mul_le_mul' le_rfl h
    _ = b := by
      rw [← mul_assoc, ← ENNReal.inv_pow,
        ENNReal.inv_mul_cancel (two_pow_ne_zero' c) (two_pow_ne_top' c), one_mul]

/-- `a ≤ 2^c b` from `2^{-c} a ≤ b`. -/
theorem le_two_pow_mul_of_inv {a b : ℝ≥0∞} {c : ℕ} (h : 2⁻¹ ^ c * a ≤ b) :
    a ≤ 2 ^ c * b := by
  calc a = 2 ^ c * (2⁻¹ ^ c * a) := by
        rw [← mul_assoc, ← ENNReal.inv_pow,
          ENNReal.mul_inv_cancel (two_pow_ne_zero' c) (two_pow_ne_top' c), one_mul]
    _ ≤ 2 ^ c * b := mul_le_mul' le_rfl h

/-! ### Descriptions -/

/-- `y` **describes** `f`: the `bitsToNat y`-th enumerated approximation converges to `f`. -/
def IsLSCDescription (y : BitString) (f : BitString → ℝ≥0∞) : Prop :=
  ∀ x, ⨆ s, dyadicValue (enumApprox (bitsToNat y) s x) s = f x

/-- The function described by `y`. -/
noncomputable def descVal (y x : BitString) : ℝ≥0∞ :=
  ⨆ s, dyadicValue (enumApprox (bitsToNat y) s x) s

theorem IsLSCDescription.descVal_eq {y : BitString} {f : BitString → ℝ≥0∞}
    (h : IsLSCDescription y f) (x : BitString) : descVal y x = f x := h x

/-- **Every lower semicomputable function has a description.** -/
theorem exists_lscDescription {f : BitString → ℝ≥0∞} (hf : IsLSC₁ f) :
    ∃ y, IsLSCDescription y f := by
  obtain ⟨a, _, hsup, hcomp⟩ := hf
  obtain ⟨i, hi⟩ := exists_approxEnum (fun s x _ ↦ a s x)
    (hcomp.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd)))
  refine ⟨Nat.bits i, fun x ↦ ?_⟩
  rw [bitsToNat_bits]
  unfold enumApprox
  rw [iSup_makeMono_eq_iSup, hi x [], hsup x]

/-- A described function is lower semicomputable. -/
theorem IsLSCDescription.isLSC₁ {y : BitString} {f : BitString → ℝ≥0∞}
    (h : IsLSCDescription y f) : IsLSC₁ f := by
  refine ⟨fun s x ↦ enumApprox (bitsToNat y) s x, fun s x ↦ makeMono_mono _ s x [], h, ?_⟩
  have := enumApprox_primrec.comp (Primrec.pair (Primrec.const (bitsToNat y)) Primrec.id)
  exact this.to_comp.of_eq fun _ ↦ rfl

/-- **The described function is jointly lower semicomputable in the description.** -/
theorem descVal_isLSC : IsLSC (fun x y ↦ descVal y x) := by
  refine ⟨fun s x y ↦ enumApprox (bitsToNat y) s x, fun s x y ↦ makeMono_mono _ s x [],
    fun x y ↦ rfl, ?_⟩
  have := enumApprox_primrec.comp (Primrec.pair
    (bitsToNat_primrec.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
  exact this.to_comp.of_eq fun _ ↦ rfl

/-! ### Weights of optimal prefix complexity -/

theorem exists_weight_eq (U : Map) (hU : IsOptimalPrefixConditional U) (x : BitString) :
    ∃ k : ℕ, KP U x [] = k ∧ prefixComplexityWeight U x = 2⁻¹ ^ k := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, KP U x [] = (k : ENat) :=
    ⟨_, (ENat.coe_toNat (KP_ne_top_of_optimal U hU x [])).symm⟩
  exact ⟨k, hk, by rw [prefixComplexityWeight, hk, complexityWeight_coe]⟩

/-- `K(⟨y₁, y₂⟩) ≤⁺ K(y₁) + K(y₂)`, multiplicatively. -/
theorem exists_pairCode_weight (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ y₁ y₂, prefixComplexityWeight U y₁ * prefixComplexityWeight U y₂ ≤
      2 ^ c * prefixComplexityWeight U (pairCode y₁ y₂) := by
  obtain ⟨c₁, h₁⟩ := KPPair_le_KPPlain_add_KP U hU
  obtain ⟨c₂, h₂⟩ := KP_le_KPPlain U hU
  refine ⟨c₁ + c₂, fun y₁ y₂ ↦ ?_⟩
  obtain ⟨k₁, hk₁, hw₁⟩ := exists_weight_eq U hU y₁
  obtain ⟨k₂, hk₂, hw₂⟩ := exists_weight_eq U hU y₂
  obtain ⟨kp, hkp, hwp⟩ := exists_weight_eq U hU (pairCode y₁ y₂)
  have hle : kp ≤ k₁ + k₂ + (c₁ + c₂) := by
    have h := h₁ y₁ y₂
    have h' := h₂ y₂ y₁
    unfold KPPair at h
    unfold KPPlain at h h'
    rw [hkp, hk₁] at h
    rw [hk₂] at h'
    have : (kp : ENat) ≤ k₁ + k₂ + (c₁ + c₂) := by
      calc (kp : ENat) ≤ k₁ + KP U y₂ y₁ + c₁ := h
        _ ≤ k₁ + (k₂ + c₂) + c₁ := by gcongr
        _ = ((k₁ + k₂ + (c₁ + c₂) : ℕ) : ENat) := by push_cast; ring
    exact_mod_cast this
  rw [hw₁, hw₂, hwp, ← pow_add]
  calc (2 : ℝ≥0∞)⁻¹ ^ (k₁ + k₂) = 2 ^ (c₁ + c₂) * 2⁻¹ ^ (k₁ + k₂ + (c₁ + c₂)) := by
        rw [pow_add (2⁻¹ : ℝ≥0∞) (k₁ + k₂), ← mul_assoc, mul_comm (2 ^ (c₁ + c₂)), mul_assoc,
          ← ENNReal.inv_pow (n := c₁ + c₂),
          ENNReal.mul_inv_cancel (two_pow_ne_zero' _) (two_pow_ne_top' _), mul_one]
    _ ≤ 2 ^ (c₁ + c₂) * 2⁻¹ ^ kp :=
        mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' (by norm_num) hle)

/-! ### Indexed domination -/

/-- **Indexed domination.** A jointly lower semicomputable family of semimeasures `G(·, z)`
satisfies `2^{-K(z)} G(x, z) ≤ 2^c 2^{-K(x)}`, with `c` independent of `z`. -/
theorem indexed_domination (U : Map) (hU : IsOptimalPrefixConditional U)
    {G : BitString → BitString → ℝ≥0∞} (hG : IsLSC G) (hsum : ∀ z, ∑' x, G x z ≤ 1) :
    ∃ c : ℕ, ∀ z x, prefixComplexityWeight U z * G x z ≤ 2 ^ c * prefixComplexityWeight U x := by
  have hlsc := isLSC₁_tsum_mul hG (prefixComplexityWeight_isLSC₁ U hU.isDecompressor)
  have hsemi : IsSemimeasure (fun x ↦ ∑' z, G x z * prefixComplexityWeight U z) := by
    change ∑' x, ∑' z, G x z * prefixComplexityWeight U z ≤ 1
    rw [ENNReal.tsum_comm]
    calc ∑' z, ∑' x, G x z * prefixComplexityWeight U z
        = ∑' z, (∑' x, G x z) * prefixComplexityWeight U z := by
          simp_rw [ENNReal.tsum_mul_right]
      _ ≤ ∑' z, prefixComplexityWeight U z :=
          ENNReal.tsum_le_tsum fun z ↦ (mul_le_mul' (hsum z) le_rfl).trans (one_mul _).le
      _ ≤ 1 := KP_kraft_sum_le_one U hU.isPrefixDecompressor []
  obtain ⟨c, hc⟩ := lowerSemicomputableSemimeasure_le_prefixComplexityWeight
    ⟨hsemi, hlsc.toCond⟩ hU
  refine ⟨c, fun z x ↦ le_two_pow_mul_of_inv ?_⟩
  calc 2⁻¹ ^ c * (prefixComplexityWeight U z * G x z)
      ≤ 2⁻¹ ^ c * ∑' z, G x z * prefixComplexityWeight U z := by
        refine mul_le_mul' le_rfl ?_
        rw [mul_comm]
        exact ENNReal.le_tsum (f := fun z ↦ G x z * prefixComplexityWeight U z) z
    _ ≤ prefixComplexityWeight U x := hc x

/-- **Indexed domination with trimming.** For an arbitrary jointly lower semicomputable `G`,
the bound holds at every index `z` at which `G(·, z)` is a semimeasure. -/
theorem indexed_domination_trim (U : Map) (hU : IsOptimalPrefixConditional U)
    {G : BitString → BitString → ℝ≥0∞} (hG : IsLSC G) :
    ∃ c : ℕ, ∀ z, (∑' x, G x z ≤ 1) →
      ∀ x, prefixComplexityWeight U z * G x z ≤ 2 ^ c * prefixComplexityWeight U x := by
  obtain ⟨a, hmono, hsup, hcomp⟩ := hG
  have hT : IsLSC (truncG a 0) := ⟨truncGapprox a 0, fun S out ctx ↦ truncGapprox_mono 0 S out ctx,
    fun _ _ ↦ rfl, truncGapprox_computable hcomp 0⟩
  obtain ⟨c, hc⟩ := indexed_domination U hU hT
    (fun z ↦ by simpa using tsum_truncG_le (approx := a) 0 z)
  refine ⟨c, fun z hz x ↦ ?_⟩
  rw [← truncG_eq_f_of_le hmono hsup 0 z (by simpa using hz) x]
  exact hc z x

/-- **Gács' exact coding theorem.** `2^{-K(ν)} ν(x) ≤ 2^c 2^{-K(x)}` for every lower
semicomputable semimeasure `ν` with description `y`, with `c` independent of `ν`. -/
theorem semimeasure_le_exact (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (ν : BitString → ℝ≥0∞) (y : BitString), IsSemimeasure ν →
      IsLSCDescription y ν → ∀ x,
        prefixComplexityWeight U y * ν x ≤ 2 ^ c * prefixComplexityWeight U x := by
  obtain ⟨c, hc⟩ := indexed_domination_trim U hU descVal_isLSC
  refine ⟨c, fun ν y hν hy x ↦ ?_⟩
  have hsum : ∑' x, descVal y x ≤ 1 := by
    simp_rw [hy.descVal_eq]; exact hν
  have := hc y hsum x
  rwa [hy.descVal_eq] at this

/-! ### The continuous case -/

/-- **Indexed domination for continuous semimeasures.** -/
theorem contIndexed_domination {M : BitString → ℝ≥0∞} (hM : IsUniversalContSemimeasure M)
    (U : Map) (hU : IsOptimalPrefixConditional U)
    {G : BitString → BitString → ℝ≥0∞} (hG : IsLSC G)
    (hcont : ∀ z, IsContSemimeasure (fun x ↦ G x z)) :
    ∃ c : ℕ, ∀ z x, prefixComplexityWeight U z * G x z ≤ 2 ^ c * M x := by
  have hlsc := isLSC₁_tsum_mul hG (prefixComplexityWeight_isLSC₁ U hU.isDecompressor)
  have hkraft := KP_kraft_sum_le_one U hU.isPrefixDecompressor []
  have hcs : IsContSemimeasure (fun x ↦ ∑' z, G x z * prefixComplexityWeight U z) := by
    refine ⟨?_, fun x ↦ ?_⟩
    · calc ∑' z, G [] z * prefixComplexityWeight U z ≤ ∑' z, prefixComplexityWeight U z :=
            ENNReal.tsum_le_tsum fun z ↦ (mul_le_mul' (hcont z).1 le_rfl).trans (one_mul _).le
        _ ≤ 1 := hkraft
    · rw [← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun z ↦ ?_
      rw [← add_mul]
      exact mul_le_mul' ((hcont z).2 x) le_rfl
  obtain ⟨c, hc⟩ := hM.2.2 _ hcs hlsc
  refine ⟨c, fun z x ↦ le_two_pow_mul_of_inv ?_⟩
  calc 2⁻¹ ^ c * (prefixComplexityWeight U z * G x z)
      ≤ 2⁻¹ ^ c * ∑' z, G x z * prefixComplexityWeight U z := by
        refine mul_le_mul' le_rfl ?_
        rw [mul_comm]
        exact ENNReal.le_tsum (f := fun z ↦ G x z * prefixComplexityWeight U z) z
    _ ≤ M x := hc x

/-- The enumerated continuous semimeasures, indexed by descriptions, form a jointly lower
semicomputable family. -/
theorem enumSemimeasure_desc_isLSC :
    IsLSC (fun x y ↦ enumSemimeasure (bitsToNat y) x) := by
  refine ⟨fun s x y ↦ trimSt (enumApprox (bitsToNat y)) s x,
    fun s x y ↦ trimSt_dyadic_mono (fun s y' ↦ enumApprox_double _ s y') s x,
    fun x y ↦ rfl, ?_⟩
  have := trimSt_enumApprox_primrec.comp (Primrec.pair
    (Primrec.pair (bitsToNat_primrec.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst)
    (Primrec.fst.comp Primrec.snd))
  exact this.to_comp.of_eq fun _ ↦ rfl

/-- **`M ≥ 2^{-K(ν)} ν`.** Every lower semicomputable continuous semimeasure `ν` with
description `y` satisfies `2^{-K(y)} ν(x) ≤ 2^c M(x)`, with `c` independent of `ν`. This is the
domination Solomonoff's convergence bound `∑ … ≤ ln 2 · K(μ)` rests on. -/
theorem contSemimeasure_le_univ_exact {M : BitString → ℝ≥0∞}
    (hM : IsUniversalContSemimeasure M) (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (ν : BitString → ℝ≥0∞) (y : BitString), IsContSemimeasure ν →
      IsLSCDescription y ν → ∀ x, prefixComplexityWeight U y * ν x ≤ 2 ^ c * M x := by
  obtain ⟨c, hc⟩ := contIndexed_domination hM U hU enumSemimeasure_desc_isLSC
    (fun y ↦ enumSemimeasure_isContSemimeasure (bitsToNat y))
  refine ⟨c, fun ν y hν hy x ↦ ?_⟩
  have hle : ∀ s x, dyadicValue (enumApprox (bitsToNat y) s x) s ≤ ν x := fun s x ↦ by
    rw [← hy x]; exact le_iSup (fun s ↦ dyadicValue (enumApprox (bitsToNat y) s x) s) s
  have heq : enumSemimeasure (bitsToNat y) x = ν x :=
    iSup_trimSt_eq hν (fun s y' ↦ enumApprox_double _ s y') hle hy x
  have := hc y x
  rwa [heq] at this

/-! ### Theorem 2.2.1 with the constant `K(d) + K(P)` -/

/-- The product family `G(x, ⟨y, y'⟩) = f_y(x) · f_{y'}(x)`. -/
noncomputable def descProd (x z : BitString) : ℝ≥0∞ :=
  descVal (decodeFirst z) x * descVal (decodeSecond z) x

theorem descProd_isLSC : IsLSC descProd := by
  have h1 := IsLSC.comp₁ descVal_isLSC decodeFirst_computable
    (decodeFirst_computable.comp decodeSecond_computable)
  have h2 := IsLSC.comp₁ descVal_isLSC decodeFirst_computable
    (decodeSecond_computable.comp decodeSecond_computable)
  refine IsLSC.congr' ((h1.mul h2).toLSC₂ pairCode_computable) fun x z ↦ ?_
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, descProd]

theorem descProd_pairCode (y y' x : BitString) :
    descProd x (pairCode y y') = descVal y x * descVal y' x := by
  simp only [descProd, decodeFirst_pairCode, decodeSecond_pairCode]

/-- **Gács Theorem 2.2.1 with explicit constants.** For every integrable test `t` for `P`,
and descriptions `y_d` of `t` and `y_P` of `P`,
`2^{-K(y_d)} 2^{-K(y_P)} t(x) ≤ 2^c t_P(x)`, i.e. `d(x) ≤ d̄_P(x) + K(d) + K(P) + c`,
with `c` independent of `P`, `t` and `x`. -/
theorem integrableTest_le_canonical_exact (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : ComputableMeasure) (t : BitString → ℝ≥0∞), IsIntegrableTest P t →
      ∀ yd yP : BitString, IsLSCDescription yd t → IsLSCDescription yP P.mass → ∀ x,
        prefixComplexityWeight U yd * prefixComplexityWeight U yP * t x ≤
          2 ^ c * canonicalIntegrableTest U P x := by
  obtain ⟨c₁, hc₁⟩ := indexed_domination_trim U hU descProd_isLSC
  obtain ⟨c₂, hc₂⟩ := exists_pairCode_weight U hU
  refine ⟨c₁ + c₂, fun P t ht yd yP hd hP x ↦ ?_⟩
  have hG : ∀ x, descProd x (pairCode yd yP) = P.mass x * t x := fun x ↦ by
    rw [descProd_pairCode, hd.descVal_eq, hP.descVal_eq, mul_comm]
  have hsum : ∑' x, descProd x (pairCode yd yP) ≤ 1 := by simp_rw [hG]; exact ht.2
  have h1 := hc₁ _ hsum x
  rw [hG] at h1
  refine le_two_pow_mul_div (prefixComplexityWeight_ne_zero_of_optimal U hU x)
    (P.mass_ne_top x) ?_
  refine inv_two_pow_mul_le_of_le ?_
  calc P.mass x * (prefixComplexityWeight U yd * prefixComplexityWeight U yP * t x)
      = (prefixComplexityWeight U yd * prefixComplexityWeight U yP) * (P.mass x * t x) := by
        ring
    _ ≤ (2 ^ c₂ * prefixComplexityWeight U (pairCode yd yP)) * (P.mass x * t x) :=
        mul_le_mul' (hc₂ yd yP) le_rfl
    _ = 2 ^ c₂ * (prefixComplexityWeight U (pairCode yd yP) * (P.mass x * t x)) := by ring
    _ ≤ 2 ^ c₂ * (2 ^ c₁ * prefixComplexityWeight U x) := mul_le_mul' le_rfl h1
    _ = 2 ^ (c₁ + c₂) * prefixComplexityWeight U x := by rw [pow_add]; ring

/-- **Theorem 2.2.1 with constants, additive exponents.** If `K(y_d) = k_d` and
`K(y_P) = k_P`, then `t(x) ≤ 2^{c + k_d + k_P} t_P(x)`. -/
theorem integrableTest_le_canonical_exact' (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (P : ComputableMeasure) (t : BitString → ℝ≥0∞), IsIntegrableTest P t →
      ∀ (yd yP : BitString) (kd kP : ℕ), IsLSCDescription yd t → IsLSCDescription yP P.mass →
        KP U yd [] = kd → KP U yP [] = kP → ∀ x,
          t x ≤ 2 ^ (c + kd + kP) * canonicalIntegrableTest U P x := by
  obtain ⟨c, hc⟩ := integrableTest_le_canonical_exact U hU
  refine ⟨c, fun P t ht yd yP kd kP hd hP hkd hkP x ↦ ?_⟩
  have h := hc P t ht yd yP hd hP x
  rw [prefixComplexityWeight, prefixComplexityWeight, hkd, hkP, complexityWeight_coe,
    complexityWeight_coe, ← pow_add] at h
  rw [show c + kd + kP = (kd + kP) + c by ring, pow_add, mul_assoc]
  exact le_two_pow_mul_of_inv h

end Kolmogorov.Randomness
