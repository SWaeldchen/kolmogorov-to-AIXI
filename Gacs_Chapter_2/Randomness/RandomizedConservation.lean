/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.Conservation

/-!
# Conservation of randomness under randomized transitions (Gács Thm 2.2.3, Cor 2.2.8)

A randomized transformation is a probability transition `T(x, y) ≥ 0` with
`∑_y T(x, y) = 1` (`ComputableTransition`). It carries a computable measure `P` to its
image `(T^*P)(y) = ∑_x P(x) T(x, y)` (`ComputableTransition.image`).

* **Theorem 2.2.3**: `∑_y T(x, y) · t_{T^*P}(y) ≤ 2^c · t_P(x)`, i.e.
  `log ∑_y T(x, y) 2^{d_{T^*P}(y)} ≤⁺ d_P(x)` (`transTest_le_canonical`). As in Gács' proof,
  the left side is itself an integrable test for `P`: its expectation regroups to
  `∑_y (T^*P)(y) · 2^{-K(y)} / (T^*P)(y) ≤ ∑_y 2^{-K(y)} ≤ 1`.
* **Corollary 2.2.8**: by Markov's inequality for the distribution `T(x, ·)`, the
  `T(x, ·)`-probability that the deficiency of `y` exceeds that of `x` by more than `k` is at
  most `2^{c - k}` (`transition_deficiency_tail`).
* As a sanity check, a deterministic computable map `f` is the transition
  `T(x, y) = 1[y = f x]` (`detTransition`), and Theorem 2.2.3 then specialises to Gács'
  Theorem 2.2.2 for the image measure (`det_canonical_image_le`).

## Hypothesis on `T`

Gács asks for a *computable* transition. The proof only consumes lower semicomputability of
`(x, y) ↦ T(x, y)` (the repository's two-argument `IsLSC`): it makes `T^*P` lower
semicomputable, hence computable by Proposition 1.6.8 since its total mass is `1`, and it
makes the test `x ↦ ∑_y T(x, y) t_{T^*P}(y)` lower semicomputable. Together with the row
normalisation `∑_y T(x, y) = 1`, lower semicomputability already implies computability
(the argument of Proposition 1.6.8, run row by row), so nothing is lost by the weaker
hypothesis.

## Tier 1

The constants depend on `T` and `P`; Gács' explicit `K(T) + K(P)` is not tracked.
-/

namespace Kolmogorov.Randomness

open scoped ENNReal

/-! ### Lower semicomputability of `x ↦ ∑_y g(x, y) h(y)` -/

/-- Monotone finite partial sums over `boundedPrograms s` exhaust the `tsum`. -/
theorem iSup_sum_boundedPrograms {u : ℕ → BitString → ℝ≥0∞} {v : BitString → ℝ≥0∞}
    (hmono : ∀ y, Monotone (fun s ↦ u s y)) (hsup : ∀ y, ⨆ s, u s y = v y) :
    ⨆ s, ∑ y ∈ (boundedPrograms s).toFinset, u s y = ∑' y, v y := by
  apply le_antisymm
  · refine iSup_le fun s ↦ ?_
    calc ∑ y ∈ (boundedPrograms s).toFinset, u s y
        ≤ ∑ y ∈ (boundedPrograms s).toFinset, v y :=
          Finset.sum_le_sum fun y _ ↦ by rw [← hsup y]; exact le_iSup (fun s ↦ u s y) s
      _ ≤ ∑' y, v y := ENNReal.sum_le_tsum _
  · rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun F ↦ ?_
    set N := F.sup List.length
    calc ∑ y ∈ F, v y ≤ ∑ y ∈ (boundedPrograms N).toFinset, v y :=
          Finset.sum_le_sum_of_subset (subset_boundedPrograms F)
      _ = ⨆ s, ∑ y ∈ (boundedPrograms N).toFinset, u s y := by
          rw [← ENNReal.finsetSum_iSup_of_monotone hmono]
          exact Finset.sum_congr rfl fun y _ ↦ (hsup y).symm
      _ ≤ ⨆ s, ∑ y ∈ (boundedPrograms s).toFinset, u s y := by
          refine iSup_le fun s ↦ le_iSup_of_le (max s N) ?_
          calc ∑ y ∈ (boundedPrograms N).toFinset, u s y
              ≤ ∑ y ∈ (boundedPrograms N).toFinset, u (max s N) y :=
                Finset.sum_le_sum fun y _ ↦ hmono y (le_max_left s N)
            _ ≤ _ := Finset.sum_le_sum_of_subset fun y hy ↦ by
                rw [List.mem_toFinset, mem_boundedPrograms_iff] at hy ⊢
                exact hy.trans (le_max_right s N)

/-- Stage-`s` numerator of `∑_y g(x, y) h(y)` over the strings of length `≤ s`, at scale
`2^s · 2^s`. -/
def tsumMulApprox (a : ℕ → BitString → BitString → ℕ) (c : ℕ → BitString → ℕ) (s : ℕ)
    (x : BitString) : ℕ :=
  ∑ i ∈ Finset.range (boundedPrograms s).length,
    a s x ((boundedPrograms s).getD i []) * c s ((boundedPrograms s).getD i [])

theorem tsumMulApprox_computable {a : ℕ → BitString → BitString → ℕ} {c : ℕ → BitString → ℕ}
    (ha : Computable (fun p : ℕ × BitString × BitString ↦ a p.1 p.2.1 p.2.2))
    (hc : Computable (fun p : ℕ × BitString ↦ c p.1 p.2)) :
    Computable (fun p : ℕ × BitString ↦ tsumMulApprox a c p.1 p.2) := by
  have hget : Computable (fun q : (ℕ × BitString) × ℕ ↦ (boundedPrograms q.1.1).getD q.2 []) :=
    ((Primrec.list_getD ([] : BitString)).comp
      (primrec_boundedPrograms.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to_comp
  have h2 : Computable₂ (fun (p : ℕ × BitString) (i : ℕ) ↦
      a p.1 p.2 ((boundedPrograms p.1).getD i []) * c p.1 ((boundedPrograms p.1).getD i [])) := by
    have : Computable (fun q : (ℕ × BitString) × ℕ ↦
        a q.1.1 q.1.2 ((boundedPrograms q.1.1).getD q.2 []) *
          c q.1.1 ((boundedPrograms q.1.1).getD q.2 [])) :=
      Primrec.nat_mul.to_comp.comp
        (ha.comp (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.pair (Computable.snd.comp Computable.fst) hget)))
        (hc.comp (Computable.pair (Computable.fst.comp Computable.fst) hget))
    exact this
  exact (computable_range_sum _ h2 (fun p ↦ (boundedPrograms p.1).length)
    ((Primrec.list_length.comp (primrec_boundedPrograms.comp Primrec.fst)).to_comp)).of_eq
    (fun _ ↦ rfl)

theorem ratVal_tsumMulApprox (a : ℕ → BitString → BitString → ℕ) (c : ℕ → BitString → ℕ)
    (s : ℕ) (x : BitString) :
    ratVal (tsumMulApprox a c s x, 2 ^ s * 2 ^ s)
      = ∑ y ∈ (boundedPrograms s).toFinset, dyadicValue (a s x y) s * dyadicValue (c s y) s := by
  unfold tsumMulApprox
  rw [sum_range_getD_eq _ (boundedPrograms_nodup s) (fun y ↦ a s x y * c s y)]
  simp only [← ratVal_mul_pow]
  simp only [ratVal, Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]

/-- **`x ↦ ∑_y g(x, y) · h(y)` is lower semicomputable** when `g` is jointly lower
semicomputable (the repository's two-argument `IsLSC`) and `h` is. -/
theorem isLSC₁_tsum_mul {g : BitString → BitString → ℝ≥0∞} {h : BitString → ℝ≥0∞}
    (hg : IsLSC g) (hh : IsLSC₁ h) : IsLSC₁ (fun x ↦ ∑' y, g x y * h y) := by
  obtain ⟨a, ha1, ha2, ha3⟩ := hg
  obtain ⟨c, hc1, hc2, hc3⟩ := hh
  have hmono : ∀ x y, Monotone (fun s ↦ dyadicValue (a s x y) s * dyadicValue (c s y) s) :=
    fun x y ↦ monotone_nat_of_le_succ fun s ↦ mul_le_mul' (ha1 s x y) (hc1 s y)
  have hsup : ∀ x y, ⨆ s, dyadicValue (a s x y) s * dyadicValue (c s y) s = g x y * h y := by
    intro x y
    rw [← ha2 x y, ← hc2 y]
    exact (iSup_mul_iSup_of_monotone (monotone_nat_of_le_succ fun s ↦ ha1 s x y)
      (monotone_nat_of_le_succ fun s ↦ hc1 s y)).symm
  refine IsLSC₁.of_ratApprox (fun s x ↦ (tsumMulApprox a c s x, 2 ^ s * 2 ^ s))
    (fun s x ↦ by positivity) (fun s x ↦ ?_) (fun x ↦ ?_) ?_
  · rw [ratVal_tsumMulApprox, ratVal_tsumMulApprox]
    calc ∑ y ∈ (boundedPrograms s).toFinset, dyadicValue (a s x y) s * dyadicValue (c s y) s
        ≤ ∑ y ∈ (boundedPrograms s).toFinset,
            dyadicValue (a (s + 1) x y) (s + 1) * dyadicValue (c (s + 1) y) (s + 1) :=
          Finset.sum_le_sum fun y _ ↦ hmono x y (Nat.le_succ s)
      _ ≤ _ := Finset.sum_le_sum_of_subset fun y hy ↦ by
          rw [List.mem_toFinset, mem_boundedPrograms_iff] at hy ⊢; omega
  · simp only [ratVal_tsumMulApprox]
    exact iSup_sum_boundedPrograms (hmono x) (hsup x)
  · exact Computable.pair (tsumMulApprox_computable ha3 hc3)
      (Primrec.nat_mul.to_comp.comp
        (natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst)
        (natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst))

/-- Swapping the two arguments preserves joint lower semicomputability. -/
theorem isLSC_swap {g : BitString → BitString → ℝ≥0∞} (hg : IsLSC g) :
    IsLSC (fun y x ↦ g x y) := by
  obtain ⟨a, h1, h2, h3⟩ := hg
  exact ⟨fun s y x ↦ a s x y, fun s y x ↦ h1 s x y, fun y x ↦ h2 x y,
    h3.comp (Computable.pair Computable.fst (Computable.pair
      (Computable.snd.comp Computable.snd) (Computable.fst.comp Computable.snd)))⟩

/-! ### Transitions and image measures -/

/-- **A probability transition** `T(x, y)` (Gács §2.2.3): rows sum to one, and `T` is jointly
lower semicomputable. See the module docstring for why lower semicomputability suffices. -/
structure ComputableTransition where
  /-- The transition probabilities `T(x, y)`. -/
  kernel : BitString → BitString → ℝ≥0∞
  /-- Each row is a probability distribution. -/
  row_sum : ∀ x, ∑' y, kernel x y = 1
  /-- Joint lower semicomputability. -/
  lsc : IsLSC kernel

namespace ComputableTransition

variable (T : ComputableTransition) (P : ComputableMeasure)

/-- The mass of the image measure, `(T^*P)(y) = ∑_x P(x) T(x, y)`. -/
noncomputable def imageMass (y : BitString) : ℝ≥0∞ :=
  ∑' x, P.mass x * T.kernel x y

theorem tsum_imageMass : ∑' y, T.imageMass P y = 1 := by
  unfold imageMass
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left, T.row_sum, mul_one]
  exact P.tsum_eq

theorem imageMass_isLSC₁ : IsLSC₁ (T.imageMass P) :=
  (isLSC₁_tsum_mul (isLSC_swap T.lsc) P.computable.isLSC₁).congr fun y ↦ by
    unfold imageMass; exact tsum_congr fun x ↦ mul_comm _ _

/-- **The image `T^*P` of a computable measure is a computable measure** (lower
semicomputable with total mass `1`, then Proposition 1.6.8). -/
noncomputable def image : ComputableMeasure where
  mass := T.imageMass P
  tsum_eq := T.tsum_imageMass P
  computable := (T.imageMass_isLSC₁ P).isComputable_of_tsum_eq_one (T.tsum_imageMass P)

end ComputableTransition

/-! ### Theorem 2.2.3 -/

/-- Gács' `t_P(x)` in the proof of Theorem 2.2.3: the `T(x, ·)`-expectation of the canonical
test of the image measure, `∑_y T(x, y) t_{T^*P}(y)`. -/
noncomputable def transTest (U : Map) (T : ComputableTransition) (P : ComputableMeasure)
    (x : BitString) : ℝ≥0∞ :=
  ∑' y, T.kernel x y * canonicalIntegrableTest U (T.image P) y

/-- The expected image test is an integrable test for `P`. -/
theorem transTest_isIntegrableTest (U : Map) (hU : IsOptimalPrefixConditional U)
    (T : ComputableTransition) (P : ComputableMeasure) :
    IsIntegrableTest P (transTest U T P) := by
  refine ⟨isLSC₁_tsum_mul T.lsc (canonicalIntegrableTest_isIntegrableTest U hU (T.image P)).1,
    ?_⟩
  have hregroup : ∑' x, P.mass x * transTest U T P x
      = ∑' y, T.imageMass P y * canonicalIntegrableTest U (T.image P) y := by
    unfold transTest ComputableTransition.imageMass
    simp_rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun y ↦ tsum_congr fun x ↦ by ring
  rw [hregroup]
  calc ∑' y, T.imageMass P y * canonicalIntegrableTest U (T.image P) y
      ≤ ∑' y, prefixComplexityWeight U y :=
        ENNReal.tsum_le_tsum fun y ↦ ENNReal.mul_div_le
    _ ≤ 1 := KP_kraft_sum_le_one U hU.isPrefixDecompressor []

/-- **Gács Theorem 2.2.3.** `log ∑_y T(x, y) 2^{d_{T^*P}(y)} ≤⁺ d_P(x)`, multiplicatively:
`∑_y T(x, y) t_{T^*P}(y) ≤ 2^c · t_P(x)`. -/
theorem transTest_le_canonical (U : Map) (hU : IsOptimalPrefixConditional U)
    (T : ComputableTransition) (P : ComputableMeasure) :
    ∃ c : ℕ, ∀ x, transTest U T P x ≤ 2 ^ c * canonicalIntegrableTest U P x :=
  integrableTest_le_canonical U hU P (transTest_isIntegrableTest U hU T P)

/-! ### Corollary 2.2.8 -/

/-- The canonical test never vanishes: `2^{-K(x)} > 0` and `P(x) < ∞`. -/
theorem canonicalIntegrableTest_ne_zero (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableMeasure) (x : BitString) : canonicalIntegrableTest U P x ≠ 0 := by
  have hw0 : prefixComplexityWeight U x ≠ 0 := by
    unfold prefixComplexityWeight
    obtain ⟨k, hk⟩ : ∃ k : ℕ, KP U x [] = (k : ENat) :=
      ⟨_, (ENat.coe_toNat (KP_ne_top_of_optimal U hU x [])).symm⟩
    rw [hk, complexityWeight_coe]
    exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
  exact (ENNReal.div_pos_iff.mpr ⟨hw0, P.mass_ne_top x⟩).ne'

/-- **Gács Corollary 2.2.8.** For every `x` and `k`, the `T(x, ·)`-probability of the outcomes
`y` with `d_{T^*P}(y) > d_P(x) + k` is at most `2^{c - k}`; multiplicatively, the event is
`2^k · t_P(x) < t_{T^*P}(y)`. -/
theorem transition_deficiency_tail (U : Map) (hU : IsOptimalPrefixConditional U)
    (T : ComputableTransition) (P : ComputableMeasure) :
    ∃ c : ℕ, ∀ (k : ℕ) (x : BitString),
      ∑' y, (if 2 ^ k * canonicalIntegrableTest U P x < canonicalIntegrableTest U (T.image P) y
        then T.kernel x y else 0) ≤ 2 ^ c * 2⁻¹ ^ k := by
  obtain ⟨c, hc⟩ := transTest_le_canonical U hU T P
  refine ⟨c, fun k x ↦ ?_⟩
  set A := canonicalIntegrableTest U P x with hA
  set t' := canonicalIntegrableTest U (T.image P) with ht'
  have hA0 : A ≠ 0 := canonicalIntegrableTest_ne_zero U hU P x
  by_cases hAtop : A = ⊤
  · -- The event is empty.
    have hzero : ∀ y, (if 2 ^ k * A < t' y then T.kernel x y else 0) = 0 := fun y ↦ by
      rw [if_neg]
      rw [hAtop, ENNReal.mul_top (two_pow_ne_zero' k)]
      exact not_top_lt
    simp only [hzero, tsum_zero]
    exact zero_le
  · -- Markov's inequality for `T(x, ·)`.
    have hterm : ∀ y, (if 2 ^ k * A < t' y then T.kernel x y else 0) * (2 ^ k * A)
        ≤ T.kernel x y * t' y := fun y ↦ by
      split_ifs with h
      · exact mul_le_mul' le_rfl h.le
      · rw [zero_mul]; exact zero_le
    have hsum : (∑' y, if 2 ^ k * A < t' y then T.kernel x y else 0) * 2 ^ k * A
        ≤ 2 ^ c * A := by
      rw [mul_assoc, ← ENNReal.tsum_mul_right]
      exact (ENNReal.tsum_le_tsum hterm).trans (hc x)
    have hcancel : (∑' y, if 2 ^ k * A < t' y then T.kernel x y else 0) * 2 ^ k ≤ 2 ^ c :=
      (ENNReal.mul_le_mul_iff_left hA0 hAtop).mp hsum
    have h := (ENNReal.le_div_iff_mul_le (Or.inl (two_pow_ne_zero' k))
      (Or.inl (two_pow_ne_top' k))).mpr hcancel
    rwa [div_eq_mul_inv, ENNReal.inv_pow] at h

/-! ### Deterministic maps as transitions -/

theorem dyadicValue_two_pow_self (s : ℕ) : dyadicValue (2 ^ s) s = 1 := by
  unfold dyadicValue; push_cast; exact ENNReal.div_self (two_pow_ne_zero' s) (two_pow_ne_top' s)

/-- A computable map `f` as the transition `T(x, y) = 1[y = f x]`. -/
noncomputable def detTransition (f : BitString → BitString) (hf : Computable f) :
    ComputableTransition where
  kernel x y := if y = f x then 1 else 0
  row_sum x := by rw [tsum_ite_eq]
  lsc := by
    refine ⟨fun s x y ↦ if y = f x then 2 ^ s else 0, fun s x y ↦ ?_, fun x y ↦ ?_, ?_⟩
    · dsimp only; split_ifs <;> simp [dyadicValue_two_pow_self, dyadicValue_zero]
    · dsimp only; split_ifs <;> simp [dyadicValue_two_pow_self, dyadicValue_zero]
    · have htest : Computable (fun p : ℕ × BitString × BitString ↦ decide (p.2.2 = f p.2.1)) :=
        (bitStringEq_primrec.to_comp.comp (Computable.pair (Computable.snd.comp Computable.snd)
          (hf.comp (Computable.fst.comp Computable.snd)))).of_eq (fun _ ↦ rfl)
      exact (Computable.cond htest
        (natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst)
        (Computable.const 0)).of_eq (fun p ↦ Bool.cond_decide _ _ _)

/-- The image under a deterministic transition is the pushforward. -/
theorem detTransition_imageMass (f : BitString → BitString) (hf : Computable f)
    (P : ComputableMeasure) (y : BitString) :
    (detTransition f hf).imageMass P y = pushMass f P y := by
  unfold ComputableTransition.imageMass pushMass detTransition
  refine tsum_congr fun x ↦ ?_
  by_cases h : f x = y
  · simp [h]
  · simp [h, Ne.symm h]

/-- **Theorem 2.2.2 recovered from Theorem 2.2.3.** For a deterministic transition the
expected image test is the image test at `f x`, so `t_{f_*P}(f x) ≤ 2^c · t_P(x)`. -/
theorem det_canonical_image_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) (P : ComputableMeasure) :
    ∃ c : ℕ, ∀ x, canonicalIntegrableTest U ((detTransition f hf).image P) (f x)
      ≤ 2 ^ c * canonicalIntegrableTest U P x := by
  obtain ⟨c, hc⟩ := transTest_le_canonical U hU (detTransition f hf) P
  refine ⟨c, fun x ↦ le_of_eq_of_le ?_ (hc x)⟩
  unfold transTest
  rw [tsum_eq_single (f x) fun y hy ↦ by simp [detTransition, hy]]
  simp [detTransition]

end Kolmogorov.Randomness
