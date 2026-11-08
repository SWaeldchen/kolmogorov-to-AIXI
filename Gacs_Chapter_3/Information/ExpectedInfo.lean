/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Information.Basic
import Gacs_Chapter_3.Classical.ExpectedComplexity
import Gacs_Chapter_3.Classical.Information

/-!
# Gács Lemma 3.1.10: classical information is expected algorithmic information

For a computable joint distribution `p(x, y)` with description `y_p` (a description of
`w ↦ p(decodeFirst w, decodeSecond w)`, i.e. of `p` on encoded pairs; `K(p) = K(y_p)`):

  `I(X : Y) − K(p) ≤⁺ ∑ p(x,y) I*(x : y) ≤⁺ I(X : Y) + 2 K(p)`   (`expected_infoStar`),

where `I*(x : y) = K(x) + K(y) − K(x, y)`. The statement is kept in `ℝ≥0∞` without
subtraction: `E[I*] = E[K(x)] + E[K(y)] − E[K(x,y)]` and the two inequalities are rearranged
accordingly, so no finiteness hypothesis is needed. `I(X : Y)` is the Kullback–Leibler form
`mutualInfoKL`, which equals Gács' `H(Y) − H(Y ∣ X)` when the entropies are finite
(`Classical.mutualInfo_eq_mutualInfoKL`).

## Proof

Gács: by Theorem 3.1.3 applied to `p`, `p₁`, `p₂`, with `K(p_i) ≤⁺ K(p)`, and
`I = H(p₁) + H(p₂) − H(p)`. We avoid descriptions of the marginals: the three families

* `G(w, z) = 1[w is a pair code] · f_z(w)` (`jointFamily`),
* `G₁(x, z) = ∑_y f_z(⟨x, y⟩)`, `G₂(y, z) = ∑_x f_z(⟨x, y⟩)` (`marg1Family`, `marg2Family`)

are jointly lower semicomputable and at `z = y_p` they are `p`, `p₁`, `p₂`; indexed domination
(`indexed_domination_trim`) gives `2^{-K(y_p)} p_•(·) ≤ 2^c 2^{-K(·)}` directly, and the
termwise estimate of Theorem 3.1.3 (`Classical.mass_mul_length_le`) gives the expected
complexity bounds `E[K] ≤ H + K(y_p) + c`. Gibbs' inequality gives `H ≤ E[K]`, and the
`ℝ≥0∞` identity `H(p) + I = H(p₁) + H(p₂)` (`Classical.entropy_add_mutualInfoKL`) closes.
-/

namespace Kolmogorov.Information

open scoped ENNReal
open Kolmogorov.Randomness (IsLSCDescription descVal descVal_isLSC indexed_domination_trim
  isLSC₁_natCast exists_weight_eq IsLSC.comp₁ IsLSC₁.toLSC₂ IsLSC.congr' isLSC₁_tsum_mul IsLSC₁)
open Kolmogorov.Information.Classical (entropy marg1 marg2 mutualInfoKL tsum_marg1 tsum_marg2
  entropy_le_tsum_mul_length mass_mul_length_le entropy_add_mutualInfoKL le_one_of_tsum_le_one)

variable {U : Map}

/-! ### Lower semicomputability with two computable reindexings -/

theorem isLSC_comp₂ {F : BitString → BitString → ℝ≥0∞} (hF : IsLSC F)
    {φ ψ : BitString → BitString → BitString}
    (hφ : Computable (fun p : BitString × BitString ↦ φ p.1 p.2))
    (hψ : Computable (fun p : BitString × BitString ↦ ψ p.1 p.2)) :
    IsLSC (fun q y ↦ F (φ q y) (ψ q y)) := by
  obtain ⟨a, h1, h2, h3⟩ := hF
  refine ⟨fun s q y ↦ a s (φ q y) (ψ q y), fun s q y ↦ h1 s _ _, fun q y ↦ h2 _ _, ?_⟩
  have := h3.comp (Computable.pair Computable.fst
    (Computable.pair (hφ.comp Computable.snd) (hψ.comp Computable.snd)))
  exact this.of_eq fun _ ↦ rfl

/-! ### The three families -/

open Classical in
/-- Is `w` a pair code? -/
noncomputable def isPairInd (w : BitString) : ℕ :=
  if pairCode (decodeFirst w) (decodeSecond w) = w then 1 else 0

theorem isPairInd_computable : Computable isPairInd := by
  have hpc : Computable (fun w : BitString ↦ pairCode (decodeFirst w) (decodeSecond w)) := by
    have h := pairCode_computable.comp (Computable.pair decodeFirst_computable
      decodeSecond_computable)
    exact h.of_eq fun _ ↦ rfl
  have hdec := bitStringEq_primrec.to_comp.comp (Computable.pair hpc Computable.id)
  have h := Computable.cond hdec (Computable.const 1) (Computable.const 0)
  refine h.of_eq fun w ↦ ?_
  unfold isPairInd
  by_cases hw : pairCode (decodeFirst w) (decodeSecond w) = w <;> simp [hw]

/-- `G(w, z) = 1[w is a pair code] · f_z(w)`. -/
noncomputable def jointFamily (w z : BitString) : ℝ≥0∞ := (isPairInd w : ℝ≥0∞) * descVal z w

theorem jointFamily_isLSC : IsLSC jointFamily := by
  have h1 := isLSC₁_natCast (isPairInd_computable.comp decodeFirst_computable)
  have h2 := IsLSC.comp₁ descVal_isLSC decodeFirst_computable decodeSecond_computable
  refine IsLSC.congr' ((h1.mul h2).toLSC₂ pairCode_computable) fun w z ↦ ?_
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, jointFamily]

/-- `G₁(x, z) = ∑_y f_z(⟨x, y⟩)`. -/
noncomputable def marg1Family (x z : BitString) : ℝ≥0∞ := ∑' y, descVal z (pairCode x y)

/-- `G₂(y, z) = ∑_x f_z(⟨x, y⟩)`. -/
noncomputable def marg2Family (y z : BitString) : ℝ≥0∞ := ∑' x, descVal z (pairCode x y)

theorem isLSC₁_one' : IsLSC₁ (fun _ : BitString ↦ ((1 : ℕ) : ℝ≥0∞)) :=
  isLSC₁_natCast (Computable.const 1)

theorem marg1Family_isLSC : IsLSC marg1Family := by
  have hφ : Computable (fun p : BitString × BitString ↦ pairCode (decodeFirst p.1) p.2) :=
    (pairCode_computable.comp (Computable.pair (decodeFirst_computable.comp Computable.fst)
      Computable.snd)).of_eq fun _ ↦ rfl
  have hψ : Computable (fun p : BitString × BitString ↦ decodeSecond p.1) :=
    decodeSecond_computable.comp Computable.fst
  have hg := isLSC_comp₂ (φ := fun q y ↦ pairCode (decodeFirst q) y)
    (ψ := fun q _ ↦ decodeSecond q) descVal_isLSC hφ hψ
  have h := isLSC₁_tsum_mul hg isLSC₁_one'
  refine IsLSC.congr' (h.toLSC₂ pairCode_computable) fun x z ↦ ?_
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, Nat.cast_one, mul_one, marg1Family]

theorem marg2Family_isLSC : IsLSC marg2Family := by
  have hφ : Computable (fun p : BitString × BitString ↦ pairCode p.2 (decodeFirst p.1)) :=
    (pairCode_computable.comp (Computable.pair Computable.snd
      (decodeFirst_computable.comp Computable.fst))).of_eq fun _ ↦ rfl
  have hψ : Computable (fun p : BitString × BitString ↦ decodeSecond p.1) :=
    decodeSecond_computable.comp Computable.fst
  have hg := isLSC_comp₂ (φ := fun q x ↦ pairCode x (decodeFirst q))
    (ψ := fun q _ ↦ decodeSecond q) descVal_isLSC hφ hψ
  have h := isLSC₁_tsum_mul hg isLSC₁_one'
  refine IsLSC.congr' (h.toLSC₂ pairCode_computable) fun y z ↦ ?_
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, Nat.cast_one, mul_one, marg2Family]

/-! ### The families at a valid description -/

section Valid

variable {p : BitString × BitString → ℝ≥0∞} {yp : BitString}

theorem descVal_pairCode (hd : IsLSCDescription yp (fun w ↦ p (decodeFirst w, decodeSecond w)))
    (x y : BitString) : descVal yp (pairCode x y) = p (x, y) := by
  rw [hd.descVal_eq]; simp [decodeFirst_pairCode, decodeSecond_pairCode]

theorem tsum_jointFamily (hd : IsLSCDescription yp (fun w ↦ p (decodeFirst w, decodeSecond w))) :
    ∑' w, jointFamily w yp = ∑' z, p z := by
  have hsupp : Function.support (fun w ↦ jointFamily w yp) ⊆
      Set.range (fun q : BitString × BitString ↦ pairCode q.1 q.2) := by
    intro w hw
    by_contra hnot
    apply hw
    have : pairCode (decodeFirst w) (decodeSecond w) ≠ w :=
      fun h ↦ hnot ⟨(decodeFirst w, decodeSecond w), h⟩
    simp [jointFamily, isPairInd, this]
  rw [← pairCode_injective.tsum_eq hsupp]
  refine tsum_congr fun q ↦ ?_
  simp [jointFamily, isPairInd, decodeFirst_pairCode, decodeSecond_pairCode,
    descVal_pairCode hd]

theorem marg1Family_eq (hd : IsLSCDescription yp (fun w ↦ p (decodeFirst w, decodeSecond w)))
    (x : BitString) : marg1Family x yp = marg1 p x := by
  simp only [marg1Family, marg1, descVal_pairCode hd]

theorem marg2Family_eq (hd : IsLSCDescription yp (fun w ↦ p (decodeFirst w, decodeSecond w)))
    (y : BitString) : marg2Family y yp = marg2 p y := by
  simp only [marg2Family, marg2, descVal_pairCode hd]

end Valid

/-! ### Expected complexity under a domination bound -/

/-- `∑ P(a) ℓ(a) ≤ H(P) + k + c` from `2^{-k} P(a) ≤ 2^c 2^{-ℓ(a)}` (Theorem 3.1.3's argument). -/
theorem tsum_mul_length_le_entropy_add {α : Type*} [Countable α] {P : α → ℝ≥0∞}
    (hP : ∑' a, P a = 1) {ℓ : α → ℕ} {k c : ℕ}
    (hdom : ∀ a, (2 : ℝ≥0∞)⁻¹ ^ k * P a ≤ 2 ^ c * 2⁻¹ ^ ℓ a) :
    ∑' a, P a * (ℓ a : ℝ≥0∞) ≤ entropy P + k + c := by
  calc ∑' a, P a * (ℓ a : ℝ≥0∞)
      ≤ ∑' a, (ENNReal.ofReal (Real.negMulLog (P a).toReal / Real.log 2)
          + P a * ((k : ℝ≥0∞) + c)) :=
        ENNReal.tsum_le_tsum fun a ↦
          mass_mul_length_le (le_one_of_tsum_le_one hP.le a) (hdom a)
    _ = entropy P + ((k : ℝ≥0∞) + c) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hP, one_mul]; rfl
    _ = entropy P + k + c := by rw [add_assoc]

/-- Domination at the valid description, as a bound on lengths. -/
theorem dom_of_weight (hU : IsOptimalPrefixConditional U) {k c : ℕ} {q : ℝ≥0∞} {x y : BitString}
    (hk : Ku U y = k) (h : prefixComplexityWeight U y * q ≤ 2 ^ c * prefixComplexityWeight U x) :
    (2 : ℝ≥0∞)⁻¹ ^ k * q ≤ 2 ^ c * 2⁻¹ ^ Ku U x := by
  rw [prefixComplexityWeight, prefixComplexityWeight, complexityWeight_KP hU,
    complexityWeight_KP hU] at h
  rw [← hk]; exact h

/-! ### Lemma 3.1.10 -/

/-- **Gács Lemma 3.1.10.** For a joint distribution `p` with description `y_p`:
`I(X:Y) − K(p) ≤⁺ ∑ p I* ≤⁺ I(X:Y) + 2 K(p)`, written without subtraction. -/
theorem expected_infoStar (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (p : BitString × BitString → ℝ≥0∞) (yp : BitString), ∑' z, p z = 1 →
      IsLSCDescription yp (fun w ↦ p (decodeFirst w, decodeSecond w)) →
      mutualInfoKL p + ∑' z, p z * (Ku U (pairCode z.1 z.2) : ℝ≥0∞) ≤
          ∑' z, p z * (Ku U z.1 : ℝ≥0∞) + ∑' z, p z * (Ku U z.2 : ℝ≥0∞) + Ku U yp + c ∧
        ∑' z, p z * (Ku U z.1 : ℝ≥0∞) + ∑' z, p z * (Ku U z.2 : ℝ≥0∞) ≤
          mutualInfoKL p + ∑' z, p z * (Ku U (pairCode z.1 z.2) : ℝ≥0∞) + 2 * Ku U yp + c := by
  obtain ⟨c₀, h₀⟩ := indexed_domination_trim U hU jointFamily_isLSC
  obtain ⟨c₁, h₁⟩ := indexed_domination_trim U hU marg1Family_isLSC
  obtain ⟨c₂, h₂⟩ := indexed_domination_trim U hU marg2Family_isLSC
  refine ⟨c₀ + c₁ + c₂, fun p yp hp hd ↦ ?_⟩
  -- Kraft for the three length functions
  have hkraft : ∑' w, (2 : ℝ≥0∞)⁻¹ ^ Ku U w ≤ 1 :=
    Classical.tsum_inv_two_pow_KP_le_one U hU
  have hkraft2 : ∑' z : BitString × BitString, (2 : ℝ≥0∞)⁻¹ ^ Ku U (pairCode z.1 z.2) ≤ 1 :=
    (ENNReal.tsum_comp_le_tsum_of_injective pairCode_injective
      (fun w ↦ (2 : ℝ≥0∞)⁻¹ ^ Ku U w)).trans hkraft
  -- the domination bounds at `y_p`
  have hJ : ∀ z : BitString × BitString,
      (2 : ℝ≥0∞)⁻¹ ^ Ku U yp * p z ≤ 2 ^ c₀ * 2⁻¹ ^ Ku U (pairCode z.1 z.2) := fun z ↦ by
    have hs : ∑' w, jointFamily w yp ≤ 1 := by rw [tsum_jointFamily hd, hp]
    have h := h₀ yp hs (pairCode z.1 z.2)
    have hv : jointFamily (pairCode z.1 z.2) yp = p z := by
      simp [jointFamily, isPairInd, decodeFirst_pairCode, decodeSecond_pairCode,
        descVal_pairCode hd]
    rw [hv] at h
    exact dom_of_weight hU rfl h
  have hM1 : ∀ x, (2 : ℝ≥0∞)⁻¹ ^ Ku U yp * marg1 p x ≤ 2 ^ c₁ * 2⁻¹ ^ Ku U x := fun x ↦ by
    have hs : ∑' x, marg1Family x yp ≤ 1 := by
      simp_rw [marg1Family_eq hd]; rw [tsum_marg1, hp]
    have h := h₁ yp hs x
    rw [marg1Family_eq hd] at h
    exact dom_of_weight hU rfl h
  have hM2 : ∀ y, (2 : ℝ≥0∞)⁻¹ ^ Ku U yp * marg2 p y ≤ 2 ^ c₂ * 2⁻¹ ^ Ku U y := fun y ↦ by
    have hs : ∑' y, marg2Family y yp ≤ 1 := by
      simp_rw [marg2Family_eq hd]; rw [tsum_marg2, hp]
    have h := h₂ yp hs y
    rw [marg2Family_eq hd] at h
    exact dom_of_weight hU rfl h
  -- expectations of `K(x)`, `K(y)` are expectations under the marginals
  have hE1 : ∑' z, p z * (Ku U z.1 : ℝ≥0∞) = ∑' x, marg1 p x * (Ku U x : ℝ≥0∞) := by
    rw [ENNReal.tsum_prod']
    exact tsum_congr fun x ↦ by rw [marg1, ← ENNReal.tsum_mul_right]
  have hE2 : ∑' z, p z * (Ku U z.2 : ℝ≥0∞) = ∑' y, marg2 p y * (Ku U y : ℝ≥0∞) := by
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    exact tsum_congr fun y ↦ by rw [marg2, ← ENNReal.tsum_mul_right]
  have hm1 : ∑' x, marg1 p x = 1 := by rw [tsum_marg1, hp]
  have hm2 : ∑' y, marg2 p y = 1 := by rw [tsum_marg2, hp]
  -- Gibbs and Theorem 3.1.3 for the joint law and the marginals
  have gJ := entropy_le_tsum_mul_length p hp (fun z ↦ Ku U (pairCode z.1 z.2)) hkraft2
  have g1 := entropy_le_tsum_mul_length (marg1 p) hm1 (Ku U) hkraft
  have g2 := entropy_le_tsum_mul_length (marg2 p) hm2 (Ku U) hkraft
  have uJ := tsum_mul_length_le_entropy_add hp hJ
  have u1 := tsum_mul_length_le_entropy_add hm1 hM1
  have u2 := tsum_mul_length_le_entropy_add hm2 hM2
  have hid := entropy_add_mutualInfoKL p hp
  rw [hE1, hE2]
  set I := mutualInfoKL p
  set H := entropy p
  set H1 := entropy (marg1 p)
  set H2 := entropy (marg2 p)
  set Exy := ∑' z, p z * (Ku U (pairCode z.1 z.2) : ℝ≥0∞)
  set Ex := ∑' x, marg1 p x * (Ku U x : ℝ≥0∞)
  set Ey := ∑' y, marg2 p y * (Ku U y : ℝ≥0∞)
  set K := (Ku U yp : ℝ≥0∞)
  constructor
  · calc I + Exy ≤ I + (H + K + c₀) := add_le_add le_rfl uJ
      _ = (H + I) + K + c₀ := by ring
      _ = H1 + H2 + K + c₀ := by rw [hid]
      _ ≤ Ex + Ey + K + c₀ := by gcongr
      _ ≤ Ex + Ey + K + ↑(c₀ + c₁ + c₂) := by gcongr; exact_mod_cast (by omega)
  · calc Ex + Ey ≤ (H1 + K + c₁) + (H2 + K + c₂) := add_le_add u1 u2
      _ = (H1 + H2) + 2 * K + (c₁ + c₂ : ℕ) := by push_cast; ring
      _ = (H + I) + 2 * K + (c₁ + c₂ : ℕ) := by rw [hid]
      _ ≤ (Exy + I) + 2 * K + (c₁ + c₂ : ℕ) := by gcongr
      _ = I + Exy + 2 * K + (c₁ + c₂ : ℕ) := by ring
      _ ≤ I + Exy + 2 * K + ↑(c₀ + c₁ + c₂) := by gcongr; exact_mod_cast (by omega)

end Kolmogorov.Information
