/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.Descriptions

/-!
# Conservation of randomness with explicit constants (Gács Thms 2.2.2, 2.2.3, Cor 2.2.8)

`RandomizedConservation.lean` proves Theorem 2.2.3 and Corollary 2.2.8 with a constant
depending on the transition `T` and the measure `P`. Here the constant is Gács' `K(T) + K(P)`
(and `K(f) + K(P)` for Theorem 2.2.2), up to one universal additive constant:

* **Theorem 2.2.3** (`transTest_le_canonical_exact`):
  `2^{-K(y_T)} 2^{-K(y_P)} ∑_y T(x, y) t_{T^*P}(y) ≤ 2^c t_P(x)`.
* **Corollary 2.2.8** (`transition_deficiency_tail_exact`): the `T(x, ·)`-probability of
  `d_{T^*P}(y) − d_P(x) > k + K(T) + K(P)` is at most `2^{c - k}`.
* **Theorem 2.2.2** (`det_canonical_image_le_exact`):
  `2^{-K(y_f)} 2^{-K(y_P)} t_{f_*P}(f x) ≤ 2^c t_P(x)`.

## Descriptions of transitions and maps

`K(P)` is the complexity of a description of `P.mass` (`IsLSCDescription`). A transition
`T` is described by a description `y_T` of the unary function
`q ↦ T(decodeFirst q, decodeSecond q)`, i.e. of `T` on encoded pairs; a computable map `f` by
a description of its graph indicator `q ↦ 1[decodeSecond q = f (decodeFirst q)]`. These are the
natural "programs" up to `O(1)`: a program computing (lower approximations of) `T`, resp.
computing `f`, is turned by a fixed computable wrapper (decode the pair, run the program,
compare the outputs) into such a description, and conversely the description determines
`T`, resp. the graph of `f`, from which `f` is recovered by search. Statements are universally
quantified over descriptions, so they hold in particular for shortest ones.

## Proof

As in `Descriptions.lean`, everything goes through one jointly lower semicomputable family
indexed by `z = ⟨y_T, y_P⟩`:

  `G(x, z) = P_z(x) · ∑_y T_z(x, y) · 2^{-K(y)} · (1 − R_z(y))⁻¹`,

where `P_z`, `T_z` are the described functions, `Q_z(y) = ∑_x P_z(x) T_z(x, y)` is the image,
and `R_z(y) = ∑_{y' ≠ y} Q_z(y')`. The point of `(1 − R)⁻¹` is lower semicomputability:
`1/Q` is only *upper* semicomputable, but when `Q` has total mass one,
`Q(y) = 1 − R(y)` and `a ↦ (1 − a)⁻¹` is monotone and continuous from below
(`exact_isLSC₁_one_sub_inv`). At a valid index `G(·, z) = P · transTest`, whose sum is at
most one (Theorem 2.2.3's test property), so `indexed_domination_trim` and
`exists_pairCode_weight` finish exactly as for Theorem 2.2.1.
-/

namespace Kolmogorov.Randomness

open scoped ENNReal

/-! ### `a ↦ (1 − a)⁻¹` preserves lower semicomputability -/

theorem exact_dyadicValue_lt_one_iff (n s : ℕ) : dyadicValue n s < 1 ↔ n < 2 ^ s := by
  rw [← dyadicValue_two_pow_self s, dyadicValue_lt_dyadicValue_iff]
  exact Nat.mul_lt_mul_right (Nat.two_pow_pos s)

theorem exact_ratVal_one_sub_inv (n s : ℕ) :
    ratVal (2 ^ s, 2 ^ s - n) = (1 - dyadicValue n s)⁻¹ := by
  have h0 : (2 : ℝ≥0∞) ^ s ≠ 0 := two_pow_ne_zero' s
  have ht : (2 : ℝ≥0∞) ^ s ≠ ⊤ := two_pow_ne_top' s
  have hsub : (1 : ℝ≥0∞) - dyadicValue n s = ((2 : ℝ≥0∞) ^ s - n) / 2 ^ s := by
    rw [ENNReal.sub_div (fun _ _ ↦ h0), ENNReal.div_self h0 ht]
    rfl
  rw [hsub, ENNReal.inv_div (Or.inl ht) (Or.inl h0)]
  unfold ratVal
  simp only [ENNReal.natCast_sub, Nat.cast_pow, Nat.cast_ofNat]

/-- Stage approximation of `(1 − a)⁻¹` from a stage approximation `a_s` of `a`. -/
def exactOneSubInvApprox (a : ℕ → BitString → ℕ) (s : ℕ) (x : BitString) : ℕ × ℕ :=
  if a s x < 2 ^ s then (2 ^ s, 2 ^ s - a s x) else (s, 1)

/-- **`a ↦ (1 − a)⁻¹` preserves lower semicomputability.** -/
theorem exact_isLSC₁_one_sub_inv {R : BitString → ℝ≥0∞} (hR : IsLSC₁ R) :
    IsLSC₁ (fun x ↦ (1 - R x)⁻¹) := by
  obtain ⟨a, hmono, hsup, ha⟩ := hR
  have hle : ∀ s x, dyadicValue (a s x) s ≤ R x := fun s x ↦ by
    rw [← hsup x]; exact le_iSup (fun s ↦ dyadicValue (a s x) s) s
  have htop : ∀ s x, ¬ a s x < 2 ^ s → (1 - R x)⁻¹ = ⊤ := fun s x h ↦ by
    have h1 : 1 ≤ R x :=
      (not_lt.mp ((exact_dyadicValue_lt_one_iff _ _).not.mpr h)).trans (hle s x)
    rw [tsub_eq_zero_of_le h1, ENNReal.inv_zero]
  refine IsLSC₁.of_ratSeq (exactOneSubInvApprox a) (fun s x ↦ ?_) (fun s x ↦ ?_) (fun x ↦ ?_) ?_
  · unfold exactOneSubInvApprox
    split_ifs with h
    · exact Nat.sub_pos_of_lt h
    · exact one_pos
  · unfold exactOneSubInvApprox
    split_ifs with h
    · rw [exact_ratVal_one_sub_inv]
      exact ENNReal.inv_le_inv.mpr (tsub_le_tsub_left (hle s x) 1)
    · rw [htop s x h]; exact le_top
  · have hmon : Monotone (fun s ↦ dyadicValue (a s x) s) :=
      monotone_nat_of_le_succ fun s ↦ hmono s x
    rw [← hsup x, ENNReal.sub_iSup ENNReal.one_ne_top, ENNReal.inv_iInf]
    refine iSup_le fun s ↦ ?_
    by_cases h : a s x < 2 ^ s
    · refine le_iSup_of_le s (le_of_eq ?_)
      unfold exactOneSubInvApprox
      rw [if_pos h, exact_ratVal_one_sub_inv]
    · -- From stage `s` on the approximation is `(s', 1)`, unbounded.
      have hge : ∀ s', s ≤ s' → ¬ a s' x < 2 ^ s' := fun s' hs' h' ↦ by
        have h1 := (exact_dyadicValue_lt_one_iff _ _).mpr h'
        have h2 := (exact_dyadicValue_lt_one_iff _ _).not.mpr h
        exact h2 ((hmon hs').trans_lt h1)
      have hsupt : (⨆ s', ratVal (exactOneSubInvApprox a s' x)) = ⊤ := by
        refine eq_top_of_forall_two_pow_le fun K ↦ ?_
        set s' := max s (2 ^ K)
        refine le_iSup_of_le s' ?_
        unfold exactOneSubInvApprox
        rw [if_neg (hge s' (le_max_left _ _))]
        unfold ratVal
        simp only [Nat.cast_one, div_one]
        exact_mod_cast le_max_right s (2 ^ K)
      rw [hsupt]; exact le_top
  · have hlt := natLt_primrec.to_comp.comp (Computable.pair ha
      (natPow_primrec.to_comp.comp (Computable.const 2) (Computable.fst (β := BitString))))
    have hyes := Computable.pair
      (natPow_primrec.to_comp.comp (Computable.const 2) (Computable.fst (β := BitString)))
      (Primrec.nat_sub.to_comp.comp
        (natPow_primrec.to_comp.comp (Computable.const 2) (Computable.fst (β := BitString))) ha)
    have hno := Computable.pair (Computable.fst (α := ℕ) (β := BitString)) (Computable.const 1)
    have h := Computable.cond hlt hyes hno
    exact h.of_eq fun p ↦ by
      dsimp only
      unfold exactOneSubInvApprox
      by_cases hp : a p.1 p.2 < 2 ^ p.1 <;> simp [hp]

/-! ### Plumbing -/

theorem exact_isLSC₁_one : IsLSC₁ (fun _ : BitString ↦ (1 : ℝ≥0∞)) :=
  (isLSC₁_natCast (Computable.const 1)).congr fun _ ↦ Nat.cast_one

/-- A unary lsc function read at `pairCode q x` is jointly lsc in `(q, x)`. -/
theorem exact_isLSC_of_pair {Φ : BitString → ℝ≥0∞} {F : BitString → BitString → ℝ≥0∞}
    (hΦ : IsLSC₁ Φ) (h : ∀ q x, Φ (pairCode q x) = F q x) : IsLSC F :=
  IsLSC.congr' (hΦ.toLSC₂ pairCode_computable) h

theorem exact_pairCode_comp {f g : BitString → BitString} (hf : Computable f)
    (hg : Computable g) : Computable (fun r ↦ pairCode (f r) (g r)) := by
  have h := pairCode_computable.comp (Computable.pair hf hg)
  exact h.of_eq fun _ ↦ rfl

theorem exact_descVal_comp {g h : BitString → BitString} (hg : Computable g)
    (hh : Computable h) : IsLSC₁ (fun r ↦ descVal (h r) (g r)) :=
  IsLSC.comp₁ descVal_isLSC hg hh

/-! ### The family -/

/-- The image of the described measure under the described transition, at index `z`. -/
noncomputable def exactQ (z y : BitString) : ℝ≥0∞ :=
  ∑' x, descVal (decodeSecond z) x * descVal (decodeFirst z) (pairCode x y)

/-- The mass of the image outside `y`. -/
noncomputable def exactR (z y : BitString) : ℝ≥0∞ :=
  ∑' y', if y' = y then 0 else exactQ z y'

/-- `(1 − R_z(y))⁻¹`, equal to `1 / Q_z(y)` when `Q_z` has total mass one. -/
noncomputable def exactI (z y : BitString) : ℝ≥0∞ := (1 - exactR z y)⁻¹

/-- The expected image test `∑_y T_z(x, y) 2^{-K(y)} / Q_z(y)`. -/
noncomputable def exactT (U : Map) (z x : BitString) : ℝ≥0∞ :=
  ∑' y, descVal (decodeFirst z) (pairCode x y) * (prefixComplexityWeight U y * exactI z y)

/-- The family `G(x, z) = P_z(x) · t_z(x)`. -/
noncomputable def exactG (U : Map) (x z : BitString) : ℝ≥0∞ :=
  descVal (decodeSecond z) x * exactT U z x

theorem exactQ_isLSC : IsLSC (fun y z ↦ exactQ z y) := by
  have f1 : IsLSC₁ (fun r ↦
      descVal (decodeSecond (decodeSecond (decodeFirst r))) (decodeSecond r)) :=
    exact_descVal_comp (g := fun r ↦ decodeSecond r)
      (h := fun r ↦ decodeSecond (decodeSecond (decodeFirst r))) decodeSecond_computable
      (decodeSecond_computable.comp (decodeSecond_computable.comp decodeFirst_computable))
  have f2 : IsLSC₁ (fun r ↦ descVal (decodeFirst (decodeSecond (decodeFirst r)))
      (pairCode (decodeSecond r) (decodeFirst (decodeFirst r)))) :=
    exact_descVal_comp (g := fun r ↦ pairCode (decodeSecond r) (decodeFirst (decodeFirst r)))
      (h := fun r ↦ decodeFirst (decodeSecond (decodeFirst r)))
      (exact_pairCode_comp decodeSecond_computable
        (decodeFirst_computable.comp decodeFirst_computable))
      (decodeFirst_computable.comp (decodeSecond_computable.comp decodeFirst_computable))
  have hΦ := f1.mul f2
  have hg : IsLSC (fun q x ↦ descVal (decodeSecond (decodeSecond q)) x *
      descVal (decodeFirst (decodeSecond q)) (pairCode x (decodeFirst q))) :=
    exact_isLSC_of_pair hΦ fun q x ↦ by simp only [decodeFirst_pairCode, decodeSecond_pairCode]
  have h1 : IsLSC₁ (fun q ↦ exactQ (decodeSecond q) (decodeFirst q)) :=
    (isLSC₁_tsum_mul hg exact_isLSC₁_one).congr fun q ↦ by simp only [mul_one, exactQ]
  exact exact_isLSC_of_pair h1 fun y z ↦ by simp only [decodeFirst_pairCode, decodeSecond_pairCode]

theorem exactI_isLSC : IsLSC (fun y z ↦ exactI z y) := by
  have hind : Computable (fun r : BitString ↦
      if decodeSecond r = decodeFirst (decodeFirst r) then 0 else 1) := by
    have heq := bitStringEq_primrec.to_comp.comp (Computable.pair decodeSecond_computable
      (decodeFirst_computable.comp decodeFirst_computable))
    have h := Computable.cond heq (Computable.const 0) (Computable.const 1)
    exact h.of_eq fun r ↦ Bool.cond_decide _ _ _
  have f2 : IsLSC₁ (fun r ↦ exactQ (decodeSecond (decodeFirst r)) (decodeSecond r)) :=
    IsLSC.comp₁ (g := fun r ↦ decodeSecond r) (h := fun r ↦ decodeSecond (decodeFirst r))
      exactQ_isLSC decodeSecond_computable (decodeSecond_computable.comp decodeFirst_computable)
  have hΦ := (isLSC₁_natCast hind).mul f2
  have hg : IsLSC (fun q y' ↦ ((if y' = decodeFirst q then 0 else 1 : ℕ) : ℝ≥0∞) *
      exactQ (decodeSecond q) y') :=
    exact_isLSC_of_pair hΦ fun q x ↦ by simp only [decodeFirst_pairCode, decodeSecond_pairCode]
  have hR : IsLSC₁ (fun q ↦ exactR (decodeSecond q) (decodeFirst q)) :=
    (isLSC₁_tsum_mul hg exact_isLSC₁_one).congr fun q ↦ by
      unfold exactR
      refine tsum_congr fun y' ↦ ?_
      split_ifs <;> simp
  have hI : IsLSC₁ (fun q ↦ exactI (decodeSecond q) (decodeFirst q)) :=
    exact_isLSC₁_one_sub_inv hR
  exact exact_isLSC_of_pair hI fun y z ↦ by simp only [decodeFirst_pairCode, decodeSecond_pairCode]

theorem exactG_isLSC (U : Map) (hU : IsOptimalPrefixConditional U) :
    IsLSC (exactG U) := by
  have f1 : IsLSC₁ (fun r ↦ descVal (decodeFirst (decodeSecond (decodeFirst r)))
      (pairCode (decodeFirst (decodeFirst r)) (decodeSecond r))) :=
    exact_descVal_comp (g := fun r ↦ pairCode (decodeFirst (decodeFirst r)) (decodeSecond r))
      (h := fun r ↦ decodeFirst (decodeSecond (decodeFirst r)))
      (exact_pairCode_comp (decodeFirst_computable.comp decodeFirst_computable)
        decodeSecond_computable)
      (decodeFirst_computable.comp (decodeSecond_computable.comp decodeFirst_computable))
  have f2 : IsLSC₁ (fun r ↦ exactI (decodeSecond (decodeFirst r)) (decodeSecond r)) :=
    IsLSC.comp₁ (g := fun r ↦ decodeSecond r) (h := fun r ↦ decodeSecond (decodeFirst r))
      exactI_isLSC decodeSecond_computable (decodeSecond_computable.comp decodeFirst_computable)
  have hΦ := f1.mul f2
  have hg : IsLSC (fun q y ↦ descVal (decodeFirst (decodeSecond q)) (pairCode (decodeFirst q) y) *
      exactI (decodeSecond q) y) :=
    exact_isLSC_of_pair hΦ fun q x ↦ by simp only [decodeFirst_pairCode, decodeSecond_pairCode]
  have ht : IsLSC₁ (fun q ↦ exactT U (decodeSecond q) (decodeFirst q)) :=
    (isLSC₁_tsum_mul hg (prefixComplexityWeight_isLSC₁ U hU.isDecompressor)).congr fun q ↦ by
      unfold exactT
      exact tsum_congr fun y ↦ by ring
  have f3 : IsLSC₁ (fun q ↦ descVal (decodeSecond (decodeSecond q)) (decodeFirst q)) :=
    exact_descVal_comp (g := fun q ↦ decodeFirst q) (h := fun q ↦ decodeSecond (decodeSecond q))
      decodeFirst_computable (decodeSecond_computable.comp decodeSecond_computable)
  have hΨ := f3.mul ht
  exact exact_isLSC_of_pair hΨ fun x z ↦ by
    simp only [decodeFirst_pairCode, decodeSecond_pairCode, exactG]

/-! ### The family at a valid index -/

section Valid

variable {T : ComputableTransition} {P : ComputableMeasure} {yT yP : BitString}

theorem exactQ_valid
    (hT : IsLSCDescription yT (fun q ↦ T.kernel (decodeFirst q) (decodeSecond q)))
    (hP : IsLSCDescription yP P.mass) (y : BitString) :
    exactQ (pairCode yT yP) y = T.imageMass P y := by
  unfold exactQ ComputableTransition.imageMass
  refine tsum_congr fun x ↦ ?_
  rw [decodeFirst_pairCode, decodeSecond_pairCode, hP.descVal_eq, hT.descVal_eq,
    decodeFirst_pairCode, decodeSecond_pairCode]

theorem exactI_valid
    (hT : IsLSCDescription yT (fun q ↦ T.kernel (decodeFirst q) (decodeSecond q)))
    (hP : IsLSCDescription yP P.mass) (y : BitString) :
    exactI (pairCode yT yP) y = (T.imageMass P y)⁻¹ := by
  have hsplit : 1 = T.imageMass P y + ∑' y', if y' = y then 0 else T.imageMass P y' := by
    have h := ENNReal.tsum_eq_add_tsum_ite (f := T.imageMass P) y
    rw [T.tsum_imageMass P] at h
    refine h.trans ?_
    congr 1
    exact tsum_congr fun y' ↦ by split_ifs <;> rfl
  have hR : exactR (pairCode yT yP) y = ∑' y', if y' = y then 0 else T.imageMass P y' := by
    unfold exactR
    refine tsum_congr fun y' ↦ ?_
    split_ifs
    · rfl
    · exact exactQ_valid hT hP y'
  have hRtop : (∑' y', if y' = y then 0 else T.imageMass P y') ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans_eq hsplit.symm)
  unfold exactI
  rw [hR]
  congr 1
  conv_lhs => rw [hsplit]
  exact ENNReal.add_sub_cancel_right hRtop

theorem exactG_valid (U : Map)
    (hT : IsLSCDescription yT (fun q ↦ T.kernel (decodeFirst q) (decodeSecond q)))
    (hP : IsLSCDescription yP P.mass) (x : BitString) :
    exactG U x (pairCode yT yP) = P.mass x * transTest U T P x := by
  unfold exactG exactT transTest
  rw [decodeSecond_pairCode, hP.descVal_eq]
  congr 1
  refine tsum_congr fun y ↦ ?_
  rw [decodeFirst_pairCode, hT.descVal_eq, decodeFirst_pairCode, decodeSecond_pairCode,
    exactI_valid hT hP y]
  rfl

end Valid

/-! ### Theorem 2.2.3 and Corollary 2.2.8 with explicit constants -/

/-- **Gács Theorem 2.2.3 with explicit constants.**
`log ∑_y T(x, y) 2^{d_{T^*P}(y)} ≤ d_P(x) + K(T) + K(P) + c`, multiplicatively, with `c`
independent of `T`, `P` and `x`. -/
theorem transTest_le_canonical_exact (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (T : ComputableTransition) (P : ComputableMeasure) (yT yP : BitString),
      IsLSCDescription yT (fun q ↦ T.kernel (decodeFirst q) (decodeSecond q)) →
      IsLSCDescription yP P.mass → ∀ x,
        prefixComplexityWeight U yT * prefixComplexityWeight U yP * transTest U T P x ≤
          2 ^ c * canonicalIntegrableTest U P x := by
  obtain ⟨c₁, hc₁⟩ := indexed_domination_trim U hU (exactG_isLSC U hU)
  obtain ⟨c₂, hc₂⟩ := exists_pairCode_weight U hU
  refine ⟨c₁ + c₂, fun T P yT yP hT hP x ↦ ?_⟩
  have hsum : ∑' x, exactG U x (pairCode yT yP) ≤ 1 := by
    simp_rw [exactG_valid U hT hP]
    exact (transTest_isIntegrableTest U hU T P).2
  have h1 := hc₁ _ hsum x
  rw [exactG_valid U hT hP] at h1
  refine le_two_pow_mul_div (prefixComplexityWeight_ne_zero_of_optimal U hU x)
    (P.mass_ne_top x) (inv_two_pow_mul_le_of_le ?_)
  calc P.mass x *
        (prefixComplexityWeight U yT * prefixComplexityWeight U yP * transTest U T P x)
      = (prefixComplexityWeight U yT * prefixComplexityWeight U yP) *
          (P.mass x * transTest U T P x) := by ring
    _ ≤ (2 ^ c₂ * prefixComplexityWeight U (pairCode yT yP)) *
          (P.mass x * transTest U T P x) := mul_le_mul' (hc₂ yT yP) le_rfl
    _ = 2 ^ c₂ * (prefixComplexityWeight U (pairCode yT yP) *
          (P.mass x * transTest U T P x)) := by ring
    _ ≤ 2 ^ c₂ * (2 ^ c₁ * prefixComplexityWeight U x) := mul_le_mul' le_rfl h1
    _ = 2 ^ (c₁ + c₂) * prefixComplexityWeight U x := by rw [pow_add]; ring

/-- **Gács Corollary 2.2.8 with explicit constants.** The `T(x, ·)`-probability of the outcomes
`y` with `d_{T^*P}(y) − K(T) − K(P) > d_P(x) + k` is at most `2^{c - k}`; multiplicatively, the
event is `2^k · t_P(x) < 2^{-K(y_T)} 2^{-K(y_P)} · t_{T^*P}(y)`. -/
theorem transition_deficiency_tail_exact (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (T : ComputableTransition) (P : ComputableMeasure) (yT yP : BitString),
      IsLSCDescription yT (fun q ↦ T.kernel (decodeFirst q) (decodeSecond q)) →
      IsLSCDescription yP P.mass → ∀ (k : ℕ) (x : BitString),
        ∑' y, (if 2 ^ k * canonicalIntegrableTest U P x <
            prefixComplexityWeight U yT * prefixComplexityWeight U yP *
              canonicalIntegrableTest U (T.image P) y
          then T.kernel x y else 0) ≤ 2 ^ c * 2⁻¹ ^ k := by
  obtain ⟨c, hc⟩ := transTest_le_canonical_exact U hU
  refine ⟨c, fun T P yT yP hT hP k x ↦ ?_⟩
  set A := canonicalIntegrableTest U P x with hA
  set B := prefixComplexityWeight U yT * prefixComplexityWeight U yP with hB
  set t' := canonicalIntegrableTest U (T.image P) with ht'
  have hA0 : A ≠ 0 := canonicalIntegrableTest_ne_zero U hU P x
  by_cases hAtop : A = ⊤
  · have hzero : ∀ y, (if 2 ^ k * A < B * t' y then T.kernel x y else 0) = 0 := fun y ↦ by
      rw [if_neg]
      rw [hAtop, ENNReal.mul_top (two_pow_ne_zero' k)]
      exact not_top_lt
    simp only [hzero, tsum_zero]
    exact zero_le
  · have hterm : ∀ y, (if 2 ^ k * A < B * t' y then T.kernel x y else 0) * (2 ^ k * A)
        ≤ B * (T.kernel x y * t' y) := fun y ↦ by
      split_ifs with h
      · calc T.kernel x y * (2 ^ k * A) ≤ T.kernel x y * (B * t' y) := mul_le_mul' le_rfl h.le
          _ = B * (T.kernel x y * t' y) := by ring
      · rw [zero_mul]; exact zero_le
    have hsum : (∑' y, if 2 ^ k * A < B * t' y then T.kernel x y else 0) * 2 ^ k * A
        ≤ 2 ^ c * A := by
      rw [mul_assoc, ← ENNReal.tsum_mul_right]
      calc ∑' y, (if 2 ^ k * A < B * t' y then T.kernel x y else 0) * (2 ^ k * A)
          ≤ ∑' y, B * (T.kernel x y * t' y) := ENNReal.tsum_le_tsum hterm
        _ = B * transTest U T P x := by rw [ENNReal.tsum_mul_left]; rfl
        _ ≤ 2 ^ c * A := hc T P yT yP hT hP x
    have hcancel : (∑' y, if 2 ^ k * A < B * t' y then T.kernel x y else 0) * 2 ^ k ≤ 2 ^ c :=
      (ENNReal.mul_le_mul_iff_left hA0 hAtop).mp hsum
    have h := (ENNReal.le_div_iff_mul_le (Or.inl (two_pow_ne_zero' k))
      (Or.inl (two_pow_ne_top' k))).mpr hcancel
    rwa [div_eq_mul_inv, ENNReal.inv_pow] at h

/-! ### Theorem 2.2.2 with explicit constants -/

/-- **Gács Theorem 2.2.2 with explicit constants.** For a computable map `f` described (via its
graph indicator) by `y_f`, `d_{f_*P}(f(x)) ≤ d_P(x) + K(f) + K(P) + c`, multiplicatively, with
`c` independent of `f`, `P` and `x`. -/
theorem det_canonical_image_le_exact (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (f : BitString → BitString) (hf : Computable f) (P : ComputableMeasure)
      (yf yP : BitString),
      IsLSCDescription yf (fun q ↦ if decodeSecond q = f (decodeFirst q) then 1 else 0) →
      IsLSCDescription yP P.mass → ∀ x,
        prefixComplexityWeight U yf * prefixComplexityWeight U yP *
            canonicalIntegrableTest U ((detTransition f hf).image P) (f x) ≤
          2 ^ c * canonicalIntegrableTest U P x := by
  obtain ⟨c, hc⟩ := transTest_le_canonical_exact U hU
  refine ⟨c, fun f hf P yf yP hyf hP x ↦ ?_⟩
  have hdesc : IsLSCDescription yf
      (fun q ↦ (detTransition f hf).kernel (decodeFirst q) (decodeSecond q)) := hyf
  have htt : transTest U (detTransition f hf) P x =
      canonicalIntegrableTest U ((detTransition f hf).image P) (f x) := by
    unfold transTest
    rw [tsum_eq_single (f x) fun y hy ↦ by simp [detTransition, hy]]
    simp [detTransition]
  rw [← htt]
  exact hc _ P yf yP hdesc hP x

end Kolmogorov.Randomness
