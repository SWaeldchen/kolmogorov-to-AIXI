/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.UpperBound
import KolmogorovMathlib.Prefix.Symmetry
import KolmogorovMathlib.Prefix.Properties

/-!
# Corollary 1.7.1 and the identity `K(x, K(x)) =⁺ K(x)`

Gács draws two immediate consequences from Theorem 1.7.1 (lines 2036–2050 of the
source). Both are the *upper* half of that theorem evaluated at the single length
`n = K(x)`, read in two different ways.

* **`eq:xHx`**: `K(x, K(x)) =⁺ K(x)`. The easy direction `K(x) ≤⁺ K(x, K(x))` is
  the general pair-projection bound. For the hard direction, note that `x` has at
  least one program of length exactly `K(x)`, so `f(x, K(x)) ≥ 1`; feeding that into
  the upper bound `2^{-n} f(x,n) ≤× m(x,n)` at `n = K(x)`, and converting `m` to
  `2^{-K}` by the coding theorem, gives `2^{-K(x)} ≤× 2^{-K(x,K(x))}`, i.e.
  `K(x, K(x)) ≤⁺ K(x)`.
* **Corollary 1.7.1**: *the number of shortest descriptions of any object is
  bounded by a universal constant.* Same instantiation, but keep the count on the
  left and use `K(x) ≤⁺ K(x, K(x))` on the right; the two powers of `2^{-K(x)}`
  cancel and a constant remains.

Neither result touches the lower half of Theorem 1.7.1, so neither needs
prefix-prepend universality: `IsOptimalPrefixConditional` suffices throughout.

Along the way we record the upper half of Theorem 1.7.1 with the coding theorem
already folded in (`inv_two_pow_mul_progCount_le_complexityWeight_pair`):
`2^{-n} f(x,n) ≤ 2^c · 2^{-K(x,n)}` for all `x, n`. This is the form most
convenient for downstream counting arguments.

Gács' `K(x, n)` is the complexity of the pair of `x` with the *number* `n`; we
encode the number as `natCode n`, consistently with the rest of this directory.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Two `ℝ≥0∞` bookkeeping helpers -/

/-- Move a factor `2^{-c}` from the left of an inequality to the right as `2^c`. -/
theorem le_two_pow_mul_of_inv_two_pow_mul_le {a b : ℝ≥0∞} {c : ℕ}
    (h : (2 : ℝ≥0∞)⁻¹ ^ c * a ≤ b) : a ≤ (2 : ℝ≥0∞) ^ c * b := by
  have hcc : (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ c = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  calc a = (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞)⁻¹ ^ c * a) := by rw [← mul_assoc, hcc, one_mul]
    _ ≤ (2 : ℝ≥0∞) ^ c * b := by gcongr

/-- Move a factor `2^c` from the right of an inequality to the left as `2^{-c}`. -/
theorem inv_two_pow_mul_le_of_le_two_pow_mul {a b : ℝ≥0∞} {c : ℕ}
    (h : a ≤ (2 : ℝ≥0∞) ^ c * b) : (2 : ℝ≥0∞)⁻¹ ^ c * a ≤ b := by
  have hcc : (2 : ℝ≥0∞)⁻¹ ^ c * (2 : ℝ≥0∞) ^ c = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  calc (2 : ℝ≥0∞)⁻¹ ^ c * a ≤ (2 : ℝ≥0∞)⁻¹ ^ c * ((2 : ℝ≥0∞) ^ c * b) := by gcongr
    _ = b := by rw [← mul_assoc, hcc, one_mul]

/-! ### The upper half of Theorem 1.7.1 with the coding theorem folded in -/

/-- **`2^{-n} · f(x, n) ≤× 2^{-K(x, n)}`.** The upper half of Theorem 1.7.1 with
`m(x, n)` replaced by `2^{-K(x,n)}` via the hard half of the coding theorem. Holds
for every `x` and `n`. -/
theorem inv_two_pow_mul_progCount_le_complexityWeight_pair (U : Map)
    (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (n : ℕ),
      (2 : ℝ≥0∞)⁻¹ ^ n * (progCount U x n : ℝ≥0∞)
        ≤ (2 : ℝ≥0∞) ^ c * complexityWeight (KPPair U x (natCode n)) := by
  obtain ⟨c, hc⟩ := progCount_le_aprioriMeasure_pair U hU
  obtain ⟨c₁, hc₁⟩ := aprioriMeasure_le_complexityWeight_optimal hU hU.isPrefixDecompressor
  refine ⟨c + c₁, fun x n ↦ ?_⟩
  have hm : aprioriMeasure U (pairCode x (natCode n)) []
      ≤ (2 : ℝ≥0∞) ^ c₁ * complexityWeight (KPPair U x (natCode n)) :=
    le_two_pow_mul_of_inv_two_pow_mul_le (hc₁ (pairCode x (natCode n)) [])
  calc (2 : ℝ≥0∞)⁻¹ ^ n * (progCount U x n : ℝ≥0∞)
      ≤ (2 : ℝ≥0∞) ^ c * aprioriMeasure U (pairCode x (natCode n)) [] := hc x n
    _ ≤ (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞) ^ c₁ * complexityWeight (KPPair U x (natCode n))) := by
        gcongr
    _ = (2 : ℝ≥0∞) ^ (c + c₁) * complexityWeight (KPPair U x (natCode n)) := by
        rw [pow_add, mul_assoc]

/-! ### The shortest program is a length-`K(x)` program -/

/-- If `K(x) = k` then `x` has at least one program of length exactly `k`, so the
description count at `k` is positive. -/
theorem one_le_progCount_of_hasPrefixComplexityValue (U : Map) {x : BitString} {k : ℕ}
    (hk : HasPrefixComplexityValue U x k) : 1 ≤ progCount U x k := by
  classical
  have hne : KP U x [] ≠ ⊤ := by
    rw [← KPPlain_eq_KP, ← hk]; exact ENat.coe_ne_top k
  obtain ⟨p, hp, hlen⟩ := KP_mem_candidateLengths_of_ne_top hne
  have hlen' : p.length = k := by
    have : (p.length : ENat) = (k : ENat) := by rw [hlen, ← KPPlain_eq_KP, ← hk]
    exact_mod_cast this
  have hmem : p ∈ progSet U x k := mem_progSet.mpr ⟨hlen', hp⟩
  exact Finset.card_pos.mpr ⟨p, hmem⟩

/-! ### `eq:xHx` -/

/-- **`K(x, K(x)) ≤⁺ K(x)`**, the hard direction of `eq:xHx`. -/
theorem KPPair_natCode_self_le_KPPlain (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (k : ℕ), HasPrefixComplexityValue U x k →
      KPPair U x (natCode k) ≤ KPPlain U x + (c : ENat) := by
  obtain ⟨c, hc⟩ := inv_two_pow_mul_progCount_le_complexityWeight_pair U hU
  refine ⟨c, fun x k hk ↦ ?_⟩
  have hkK : KPPlain U x = (k : ENat) := hk.symm
  have hne : KPPlain U x ≠ ⊤ := by rw [hkK]; exact ENat.coe_ne_top k
  apply le_add_nat_of_complexityWeight_le hne
  rw [hkK, complexityWeight_coe]
  -- `2^{-k} ≤ 2^{-k} · f(x,k)` since the count is at least one.
  have h1 : (2 : ℝ≥0∞)⁻¹ ^ k ≤ (2 : ℝ≥0∞)⁻¹ ^ k * (progCount U x k : ℝ≥0∞) := by
    calc (2 : ℝ≥0∞)⁻¹ ^ k = (2 : ℝ≥0∞)⁻¹ ^ k * 1 := (mul_one _).symm
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ k * (progCount U x k : ℝ≥0∞) := by
          gcongr
          exact_mod_cast one_le_progCount_of_hasPrefixComplexityValue U hk
  exact inv_two_pow_mul_le_of_le_two_pow_mul (h1.trans (hc x k))

/-- **`eq:xHx` packaged**: `K(x) ≤⁺ K(x, K(x))` and `K(x, K(x)) ≤⁺ K(x)`, with one
shared constant. -/
theorem KPPair_natCode_self_eq_KPPlain (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (k : ℕ), HasPrefixComplexityValue U x k →
      KPPlain U x ≤ KPPair U x (natCode k) + (c : ENat) ∧
      KPPair U x (natCode k) ≤ KPPlain U x + (c : ENat) := by
  obtain ⟨c₁, hc₁⟩ := KPPlain_left_le_KPPair U hU
  obtain ⟨c₂, hc₂⟩ := KPPair_natCode_self_le_KPPlain U hU
  refine ⟨c₁ + c₂, fun x k hk ↦ ⟨?_, ?_⟩⟩
  · calc KPPlain U x ≤ KPPair U x (natCode k) + (c₁ : ENat) := hc₁ x (natCode k)
      _ ≤ KPPair U x (natCode k) + ((c₁ + c₂ : ℕ) : ENat) := by
          gcongr; exact_mod_cast Nat.le_add_right c₁ c₂
  · calc KPPair U x (natCode k) ≤ KPPlain U x + (c₂ : ENat) := hc₂ x k hk
      _ ≤ KPPlain U x + ((c₁ + c₂ : ℕ) : ENat) := by
          gcongr; exact_mod_cast Nat.le_add_left c₂ c₁

/-! ### Corollary 1.7.1 -/

/-- **Corollary 1.7.1.** The number of shortest descriptions of any object is
bounded by a constant depending only on `U`: if `K(x) = k` then
`progCount U x k ≤ C`. -/
theorem progCount_shortest_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ (x : BitString) (k : ℕ), HasPrefixComplexityValue U x k →
      progCount U x k ≤ C := by
  obtain ⟨c, hc⟩ := inv_two_pow_mul_progCount_le_complexityWeight_pair U hU
  obtain ⟨c₂, hc₂⟩ := KPPlain_left_le_KPPair U hU
  refine ⟨2 ^ (c + c₂), fun x k hk ↦ ?_⟩
  have hkK : KPPlain U x = (k : ENat) := hk.symm
  -- `2^{-K(x,k)} ≤ 2^{c₂} · 2^{-k}` from `K(x) ≤ K(x,k) + c₂`.
  have hcw : complexityWeight (KPPair U x (natCode k)) ≤ (2 : ℝ≥0∞) ^ c₂ * (2 : ℝ≥0∞)⁻¹ ^ k := by
    have h := complexityWeight_le_of_le (hc₂ x (natCode k))
    rw [complexityWeight_add_nat, hkK, complexityWeight_coe, mul_comm] at h
    exact le_two_pow_mul_of_inv_two_pow_mul_le h
  -- Chain: `2^{-k} · f ≤ 2^{c+c₂} · 2^{-k}`.
  have hchain : (2 : ℝ≥0∞)⁻¹ ^ k * (progCount U x k : ℝ≥0∞)
      ≤ (2 : ℝ≥0∞) ^ (c + c₂) * (2 : ℝ≥0∞)⁻¹ ^ k := by
    calc (2 : ℝ≥0∞)⁻¹ ^ k * (progCount U x k : ℝ≥0∞)
        ≤ (2 : ℝ≥0∞) ^ c * complexityWeight (KPPair U x (natCode k)) := hc x k
      _ ≤ (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞) ^ c₂ * (2 : ℝ≥0∞)⁻¹ ^ k) := by gcongr
      _ = (2 : ℝ≥0∞) ^ (c + c₂) * (2 : ℝ≥0∞)⁻¹ ^ k := by rw [pow_add, mul_assoc]
  -- Cancel the common `2^{-k}`.
  have hcancel : (2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ k = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  have hreal : (progCount U x k : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (c + c₂) := by
    calc (progCount U x k : ℝ≥0∞)
        = (2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞)⁻¹ ^ k * (progCount U x k : ℝ≥0∞)) := by
          rw [← mul_assoc, hcancel, one_mul]
      _ ≤ (2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞) ^ (c + c₂) * (2 : ℝ≥0∞)⁻¹ ^ k) := by gcongr
      _ = (2 : ℝ≥0∞) ^ (c + c₂) * ((2 : ℝ≥0∞) ^ k * (2 : ℝ≥0∞)⁻¹ ^ k) := by ring
      _ = (2 : ℝ≥0∞) ^ (c + c₂) := by rw [hcancel, mul_one]
  exact_mod_cast hreal

end Kolmogorov
