/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Information.Identities

/-!
# Information non-increase (Gács §3.1.2)

* (3.1.x) **Guessing does not help** (`info_guess`): `∑_y m(y) 2^{I(x:y)} ≲ 1`, for a universal
  semimeasure `m`; with `m` replaced by `2^{-K}` it is exactly the conditional Kraft
  inequality `∑_y 2^{-K(y ∣ x)} ≤ 1` (`info_guess_weight`).
* **Theorem 3.1.11** (`info_nonincrease_det`): if a program `q` (for any fixed programming
  system `Φ`) computes `z` from `x*`, then `I*(y : z) ≤⁺ I*(y : x) + K(q)`.
* **Theorem 3.1.12** (`info_nonincrease_rand`, multiplicative form
  `info_nonincrease_rand_mul`):
  `2^{-K(z ∣ x*)} 2^{I*(z:y) − I*(x:y)} ≲ 2^{-K(z ∣ x*, y, K(y ∣ x*))}`,
  Gács' `m(z ∣ x*) 2^{I*(z:y) − I*(x:y)} ≲ m(z ∣ x*, y, K(y ∣ x*))` with `m(· ∣ ·)` in its coding
  form `2^{-K(· ∣ ·)}`.
* **Remark 3.1.16** (`info_increase_expectation`, `info_increase_tail`): the
  `2^{-K(· ∣ x*)}`-expectation of `2^{I*(z:y) − I*(x:y)}` is bounded, and an increase by `d` has
  weight `≲ 2^{-d}`.
-/

namespace Kolmogorov.Information

open scoped ENNReal
open Kolmogorov.Randomness (exists_inv_two_pow_le_of_pos two_pow_ne_zero' two_pow_ne_top')

variable {U : Map}

/-! ### Guessing -/

/-- `∑_y 2^{-K(y)} 2^{I(x:y)} = ∑_y 2^{-K(y ∣ x)} ≤ 1`. -/
theorem info_guess_weight (hU : IsOptimalPrefixConditional U) (x : BitString) :
    ∑' y, prefixComplexityWeight U y * (2 ^ Ku U y * 2⁻¹ ^ Kc U y x) ≤ 1 := by
  have h : ∀ y, prefixComplexityWeight U y * (2 ^ Ku U y * 2⁻¹ ^ Kc U y x) =
      complexityWeight (KP U y x) := fun y ↦ by
    rw [prefixComplexityWeight, complexityWeight_KP hU, complexityWeight_KP hU, ← mul_assoc]
    unfold Ku
    rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel (two_pow_ne_zero' _) (two_pow_ne_top' _),
      one_mul]
  simp_rw [h]
  exact KP_kraft_sum_le_one U hU.isPrefixDecompressor x

/-- **Gács (3.1.x), "guessing blindly does not help".** `∑_y m(y) 2^{I(x:y)} ≲ 1` for a
universal semimeasure `m`. -/
theorem info_guess {m : BitString → ℝ≥0∞} (hm : IsUniversalSemimeasure m)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, ∑' y, m y * (2 ^ Ku U y * 2⁻¹ ^ Kc U y x) ≤ 2 ^ c := by
  obtain ⟨c1, -, hc1, -, h1, -⟩ := universalSemimeasure_equiv_prefixComplexity hm hU
  obtain ⟨c, hc⟩ := exists_inv_two_pow_le_of_pos hc1
  refine ⟨c, fun x ↦ ?_⟩
  have hle : ∀ y, m y ≤ 2 ^ c * prefixComplexityWeight U y := fun y ↦
    Kolmogorov.Randomness.le_two_pow_mul_of_inv ((mul_le_mul' hc le_rfl).trans (h1 y))
  calc ∑' y, m y * (2 ^ Ku U y * 2⁻¹ ^ Kc U y x)
      ≤ ∑' y, 2 ^ c * (prefixComplexityWeight U y * (2 ^ Ku U y * 2⁻¹ ^ Kc U y x)) :=
        ENNReal.tsum_le_tsum fun y ↦ (mul_le_mul' (hle y) le_rfl).trans_eq (mul_assoc _ _ _)
    _ = 2 ^ c * ∑' y, prefixComplexityWeight U y * (2 ^ Ku U y * 2⁻¹ ^ Kc U y x) :=
        ENNReal.tsum_mul_left
    _ ≤ 2 ^ c * 1 := mul_le_mul' le_rfl (info_guess_weight hU x)
    _ = 2 ^ c := mul_one _

/-! ### Theorem 3.1.11: deterministic processing -/

/-- `I*(y : z) ≤⁺ I*(y : ⟨x, z⟩)`. -/
theorem infoStar_le_pair_right (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ y x z, InfoStar U y z ≤ InfoStar U y (pairCode x z) + c := by
  obtain ⟨c₁, h₁⟩ := infoStar_mono hU
  obtain ⟨c₂, h₂⟩ := Kc_pair_swap hU
  -- `⟨y, ⟨z, x⟩⟩ ↦ ⟨y, ⟨x, z⟩⟩`
  have hmap : Computable (fun w : BitString ↦
      pairCode (decodeFirst w) (pswap (decodeSecond w))) := by
    have h := pairCode_computable.comp (Computable.pair decodeFirst_computable
      (pswap_computable.comp decodeSecond_computable))
    exact h.of_eq fun _ ↦ rfl
  obtain ⟨c₃, h₃⟩ := Kc_map hU hmap
  refine ⟨c₁ + c₂ + c₃, fun y x z ↦ ?_⟩
  have a := h₁ (y, z, x)
  have b := h₂ z x []
  have d := h₃ (pairCode y (pairCode z x)) []
  simp only [decodeFirst_pairCode, decodeSecond_pairCode, pswap_pairCode] at a d
  unfold InfoStar Ku at *
  omega

/-- **Gács Theorem 3.1.11.** If `q` computes `z` from `x*` (in any fixed programming system `Φ`),
then `I*(y : z) ≤⁺ I*(y : x) + K(q)`. -/
theorem info_nonincrease_det (hU : IsOptimalPrefixConditional U)
    (Φ : BitString × BitString →. BitString) (hΦ : Partrec Φ) :
    ∃ c : ℕ, ∀ x y z q, z ∈ Φ (q, xStar U x) →
      InfoStar U y z ≤ InfoStar U y x + Ku U q + c := by
  obtain ⟨c₁, h₁⟩ := infoStar_le_pair_right hU
  obtain ⟨⟨c₂, h₂⟩, -⟩ := data_processing hU
  obtain ⟨c₃, h₃⟩ := Kc_proj hU
  have hf : Partrec (fun p : BitString × BitString ↦ Φ (p.1, p.2)) :=
    hΦ.of_eq fun _ ↦ rfl
  obtain ⟨c₄, h₄⟩ := Kc_map_partrec hU (fun w q ↦ Φ (q, w)) hf
  obtain ⟨c₅, h₅⟩ := Kc_le_Ku hU
  refine ⟨c₁ + c₂ + c₃ + c₄ + c₅, fun x y z q hz ↦ ?_⟩
  have a := h₁ y x z
  have b := h₂ (y, x, z)
  have d := (h₃ y z (xStar U x)).1
  have e := h₄ q z (xStar U x) hz
  have f := h₅ q (xStar U x)
  simp only at b
  unfold CondInfoStar at b
  push_cast
  omega

/-! ### Theorem 3.1.12: randomized processing -/

/-- `I*(x : y) =⁺ I*(y : x)`. -/
theorem infoStar_comm (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, InfoStar U x y ≤ InfoStar U y x + c := by
  obtain ⟨c, hc⟩ := Kc_pair_swap hU
  exact ⟨c, fun x y ↦ by have := hc y x []; unfold InfoStar Ku at *; omega⟩

/-- **Gács Theorem 3.1.12, additive form.** For `p = (x, y, z)`:
`I*(z : y) − I*(x : y) ≤⁺ K(z ∣ x*) − K(z ∣ x*, y, K(y ∣ x*))`. -/
theorem info_nonincrease_rand (hU : IsOptimalPrefixConditional U) :
    AddLE (fun p : BitString × BitString × BitString ↦
        InfoStar U p.2.2 p.2.1 - InfoStar U p.1 p.2.1)
      (fun p ↦ (Kc U p.2.2 (xStar U p.1) : ℤ) -
        Kc U p.2.2 (condCtx U (xStar U p.1) p.2.1)) := by
  obtain ⟨c₁, h₁⟩ := infoStar_comm hU
  obtain ⟨c₂, h₂⟩ := infoStar_le_pair_right hU
  obtain ⟨⟨c₃, h₃⟩, -⟩ := data_processing hU
  obtain ⟨⟨c₄, h₄⟩, -⟩ := condInfoStar_eq_left hU
  refine ⟨2 * c₁ + c₂ + c₃ + c₄, fun p ↦ ?_⟩
  obtain ⟨x, y, z⟩ := p
  dsimp only
  have a := h₁ z y
  have a' := h₁ y x
  have b := h₂ y x z
  have d := h₃ (y, x, z)
  have e := h₄ (y, z, xStar U x)
  simp only at d e
  push_cast
  omega

/-- `2^{-a} · 2^{e} ≤ 2^c · 2^{-b}` whenever `e ≤ a − b + c` (integer exponents). -/
theorem inv_two_pow_mul_zpow_le {a b c : ℕ} {e : ℤ} (h : e ≤ (a : ℤ) - b + c) :
    (2 : ℝ≥0∞)⁻¹ ^ a * 2 ^ e ≤ 2 ^ c * 2⁻¹ ^ b := by
  have h2 : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
  have h2' : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
  have hl : (2 : ℝ≥0∞)⁻¹ ^ a * 2 ^ e = 2 ^ (e - a) := by
    rw [ENNReal.zpow_sub h2 h2', zpow_natCast, mul_comm, ENNReal.inv_pow]
  have hr : (2 : ℝ≥0∞) ^ c * 2⁻¹ ^ b = 2 ^ ((c : ℤ) - b) := by
    rw [ENNReal.zpow_sub h2 h2', zpow_natCast, zpow_natCast, ENNReal.inv_pow]
  rw [hl, hr]
  exact ENNReal.zpow_le_of_le one_le_two (by omega)

/-- **Gács Theorem 3.1.12, multiplicative form.**
`2^{-K(z ∣ x*)} 2^{I*(z:y) − I*(x:y)} ≤ 2^c 2^{-K(z ∣ x*, y, K(y ∣ x*))}`. -/
theorem info_nonincrease_rand_mul (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y z, (2 : ℝ≥0∞)⁻¹ ^ Kc U z (xStar U x) *
        2 ^ (InfoStar U z y - InfoStar U x y) ≤
      2 ^ c * 2⁻¹ ^ Kc U z (condCtx U (xStar U x) y) := by
  obtain ⟨c, hc⟩ := info_nonincrease_rand hU
  exact ⟨c, fun x y z ↦ inv_two_pow_mul_zpow_le (by have := hc (x, y, z); simp only at this; omega)⟩

/-- **Gács Remark 3.1.16.** `∑_z 2^{-K(z ∣ x*)} 2^{I*(z:y) − I*(x:y)} ≲ 1`. -/
theorem info_increase_expectation (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, ∑' z, (2 : ℝ≥0∞)⁻¹ ^ Kc U z (xStar U x) *
        2 ^ (InfoStar U z y - InfoStar U x y) ≤ 2 ^ c := by
  obtain ⟨c, hc⟩ := info_nonincrease_rand_mul hU
  refine ⟨c, fun x y ↦ ?_⟩
  calc ∑' z, (2 : ℝ≥0∞)⁻¹ ^ Kc U z (xStar U x) * 2 ^ (InfoStar U z y - InfoStar U x y)
      ≤ ∑' z, 2 ^ c * complexityWeight (KP U z (condCtx U (xStar U x) y)) :=
        ENNReal.tsum_le_tsum fun z ↦ by rw [complexityWeight_KP hU]; exact hc x y z
    _ = 2 ^ c * ∑' z, complexityWeight (KP U z (condCtx U (xStar U x) y)) := ENNReal.tsum_mul_left
    _ ≤ 2 ^ c * 1 :=
        mul_le_mul' le_rfl (KP_kraft_sum_le_one U hU.isPrefixDecompressor _)
    _ = 2 ^ c := mul_one _

/-- **Gács Remark 3.1.16, tail form.** The `2^{-K(· ∣ x*)}`-weight of the outcomes `z` that
increase the information about `y` by at least `d` is `≲ 2^{-d}`. -/
theorem info_increase_tail (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y (d : ℕ), ∑' z, (if (d : ℤ) ≤ InfoStar U z y - InfoStar U x y then
        (2 : ℝ≥0∞)⁻¹ ^ Kc U z (xStar U x) else 0) ≤ 2 ^ c * 2⁻¹ ^ d := by
  obtain ⟨c, hc⟩ := info_nonincrease_rand hU
  refine ⟨c, fun x y d ↦ ?_⟩
  have hterm : ∀ z, (if (d : ℤ) ≤ InfoStar U z y - InfoStar U x y then
      (2 : ℝ≥0∞)⁻¹ ^ Kc U z (xStar U x) else 0) ≤
      2 ^ c * 2⁻¹ ^ d * complexityWeight (KP U z (condCtx U (xStar U x) y)) := fun z ↦ by
    split_ifs with h
    · have := hc (x, y, z)
      simp only at this
      rw [complexityWeight_KP hU, mul_assoc, ← pow_add]
      have hle : Kc U z (condCtx U (xStar U x) y) + d ≤ Kc U z (xStar U x) + c := by omega
      calc (2 : ℝ≥0∞)⁻¹ ^ Kc U z (xStar U x)
          = 2 ^ c * 2⁻¹ ^ (Kc U z (xStar U x) + c) := by
            rw [pow_add, ← mul_assoc, mul_comm (2 ^ c), mul_assoc, ← ENNReal.inv_pow (n := c),
              ENNReal.mul_inv_cancel (two_pow_ne_zero' c) (two_pow_ne_top' c), mul_one]
        _ ≤ 2 ^ c * 2⁻¹ ^ (d + Kc U z (condCtx U (xStar U x) y)) :=
            mul_le_mul' le_rfl (pow_le_pow_right_of_le_one' (by norm_num) (by omega))
    · exact zero_le
  calc ∑' z, (if (d : ℤ) ≤ InfoStar U z y - InfoStar U x y then
        (2 : ℝ≥0∞)⁻¹ ^ Kc U z (xStar U x) else 0)
      ≤ ∑' z, 2 ^ c * 2⁻¹ ^ d * complexityWeight (KP U z (condCtx U (xStar U x) y)) :=
        ENNReal.tsum_le_tsum hterm
    _ = 2 ^ c * 2⁻¹ ^ d * ∑' z, complexityWeight (KP U z (condCtx U (xStar U x) y)) :=
        ENNReal.tsum_mul_left
    _ ≤ 2 ^ c * 2⁻¹ ^ d * 1 :=
        mul_le_mul' le_rfl (KP_kraft_sum_le_one U hU.isPrefixDecompressor _)
    _ = 2 ^ c * 2⁻¹ ^ d := mul_one _

end Kolmogorov.Information
