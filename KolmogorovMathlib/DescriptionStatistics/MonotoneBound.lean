/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.ComplexityLevelsLower
import KolmogorovMathlib.DescriptionStatistics.FuelComplexity
import KolmogorovMathlib.Prefix.CountingBound
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Foundation.NatEncoding

/-!
# Theorem 1.7.3: `K⁺(n) =⁺ log n + K(⌊log n⌋)`

`K⁺(n) = max_{k ≤ n} K(k)` is the smallest monotone function above `K`
(Definition 1.7.4). Theorem 1.7.3 gives it a closed form up to an additive constant.

We state the theorem with the **bit-length** `Nat.size n` in place of `⌊log₂ n⌋`;
the two differ by one, so the statements agree up to a constant, and `Nat.size`
comes with the arithmetic we need (`Nat.size_le`, `Nat.lt_size`, `Nat.size_eq_bits_len`)
while `Nat.log` does not. Numbers are encoded as `natCode`, as everywhere in this
directory; the bridge to the `Nat.bits` encoding used by `Prefix/CountingBound` is
two instances of `KPPlain_partrec_map_le`.

## Upper half, no new machine

Gács builds a machine that reads a program for a length and then that many raw
bits. The repository already has that machine's conclusion:
`KPPlain_le_length_add_KPPlain_length` (`eq:monbd`), `K(x) ≤⁺ |x| + K(|x|)`.
Applying it to the binary representation of `k ≤ n`, zero-padded to length
`Nat.size n`, gives `K(k) ≤⁺ Nat.size n + K(Nat.size n)` uniformly in `k ≤ n`.

## Lower half, by counting

Let `L = Nat.size n − 1`. The numbers of bit-length `L` all lie below `n`, and there
are `2^(L−1)` of them. The Markov bound from `sum_complexityWeight_stringsOfLength_le`
says at most `2^(L−2)` strings of length `L` have complexity below `L + K(L) − c`. So
some number of bit-length `L` is incompressible, and it witnesses `K⁺(n) ≥⁺ L + K(L)`.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Encoding bridges -/

/-- `K(natCode m) ≤⁺ K(Nat.bits m)`. -/
theorem KPPlain_natCode_le_bits (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ m : ℕ, KPPlain U (natCode m) ≤ KPPlain U (Nat.bits m) + (c : ENat) := by
  have hf : Partrec (fun w : BitString ↦ (Part.some (natCode (bitsToNat w)) : Part BitString)) :=
    (natCode_primrec.to_comp.comp bitsToNat_computable : Computable _)
  obtain ⟨c, hc⟩ := KPPlain_partrec_map_le U hU _ hf
  refine ⟨c, fun m ↦ ?_⟩
  have := hc (Nat.bits m) _ (Part.mem_some _)
  rwa [bitsToNat_bits] at this

/-- `K(Nat.bits m) ≤⁺ K(natCode m)`. -/
theorem KPPlain_bits_le_natCode (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ m : ℕ, KPPlain U (Nat.bits m) ≤ KPPlain U (natCode m) + (c : ENat) := by
  have hf : Partrec (fun w : BitString ↦ (Part.some (Nat.bits (w.length - 1)) : Part BitString)) :=
    (natBitsComputable.comp
      ((Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)).to_comp) : Computable _)
  obtain ⟨c, hc⟩ := KPPlain_partrec_map_le U hU _ hf
  refine ⟨c, fun m ↦ ?_⟩
  have := hc (natCode m) _ (Part.mem_some _)
  rwa [length_natCode, Nat.add_sub_cancel] at this

/-- `K(natCode (m + 1)) ≤⁺ K(natCode m)`. -/
theorem KPPlain_natCode_succ_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ m : ℕ, KPPlain U (natCode (m + 1)) ≤ KPPlain U (natCode m) + (c : ENat) := by
  have hf : Partrec (fun w : BitString ↦ (Part.some (natCode w.length) : Part BitString)) :=
    (natCode_primrec.comp Primrec.list_length).to_comp
  obtain ⟨c, hc⟩ := KPPlain_partrec_map_le U hU _ hf
  refine ⟨c, fun m ↦ ?_⟩
  have := hc (natCode m) _ (Part.mem_some _)
  rwa [length_natCode] at this

/-! ### Zero-padding a binary representation -/

/-- Appending high-order zeros does not change the value of a little-endian bit list. -/
theorem bitsToNat_append_replicate_false (l : List Bool) (j : ℕ) :
    bitsToNat (l ++ List.replicate j false) = bitsToNat l := by
  unfold bitsToNat
  rw [List.foldr_append]
  congr 1
  induction j with
  | zero => rfl
  | succ j ih => simp [List.replicate_succ, ih]

/-! ### `K⁺` -/

/-- **`K⁺(n) = max_{k ≤ n} K(k)`**, Definition 1.7.4. -/
noncomputable def KPlus (U : Map) (n : ℕ) : ENat :=
  (Finset.range (n + 1)).sup (fun k ↦ KPPlain U (natCode k))

/-- `K(k) ≤ K⁺(n)` for `k ≤ n`. -/
theorem KPPlain_natCode_le_KPlus (U : Map) {k n : ℕ} (h : k ≤ n) :
    KPPlain U (natCode k) ≤ KPlus U n :=
  Finset.le_sup (f := fun k ↦ KPPlain U (natCode k)) (Finset.mem_range.mpr (by omega))

/-- `K⁺(n) ≤ b` iff every `K(k)`, `k ≤ n`, is at most `b`. -/
theorem KPlus_le_iff (U : Map) {n : ℕ} {b : ENat} :
    KPlus U n ≤ b ↔ ∀ k ≤ n, KPPlain U (natCode k) ≤ b := by
  unfold KPlus
  rw [Finset.sup_le_iff]
  simp only [Finset.mem_range, Nat.lt_succ_iff]

/-- `K⁺` is monotone. -/
theorem KPlus_mono (U : Map) {m n : ℕ} (h : m ≤ n) : KPlus U m ≤ KPlus U n :=
  (KPlus_le_iff U).mpr (fun _ hk ↦ KPPlain_natCode_le_KPlus U (hk.trans h))

/-! ### Upper half -/

/-- **Theorem 1.7.3, `≤⁺`.** `K⁺(n) ≤ Nat.size n + K(Nat.size n) + c`. Each `k ≤ n` is
described by its binary representation padded to `Nat.size n` bits, to which `eq:monbd`
applies. -/
theorem KPlus_le_size_add (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ,
      KPlus U n ≤ (Nat.size n : ENat) + KPPlain U (natCode (Nat.size n)) + (c : ENat) := by
  have hf : Partrec (fun w : BitString ↦ (Part.some (natCode (bitsToNat w)) : Part BitString)) :=
    (natCode_primrec.to_comp.comp bitsToNat_computable : Computable _)
  obtain ⟨c₁, hc₁⟩ := KPPlain_partrec_map_le U hU _ hf
  obtain ⟨c₂, hc₂⟩ := KPPlain_le_length_add_KPPlain_length U hU
  obtain ⟨c₃, hc₃⟩ := KPPlain_bits_le_natCode U hU
  refine ⟨c₁ + c₂ + c₃, fun n ↦ ?_⟩
  rw [KPlus_le_iff]
  intro k hk
  set x : BitString := Nat.bits k ++ List.replicate (Nat.size n - Nat.size k) false with hx
  have hxlen : x.length = Nat.size n := by
    rw [hx, List.length_append, List.length_replicate, Nat.size_eq_bits_len]
    have := Nat.size_le_size hk
    omega
  have hxval : natCode (bitsToNat x) = natCode k := by
    rw [hx, bitsToNat_append_replicate_false, bitsToNat_bits]
  have h1 : KPPlain U (natCode k) ≤ KPPlain U x + (c₁ : ENat) := by
    have := hc₁ x _ (Part.mem_some _)
    rwa [hxval] at this
  have h2 : KPPlain U x
      ≤ (Nat.size n : ENat) + KPPlain U (Nat.bits (Nat.size n)) + (c₂ : ENat) := by
    have := hc₂ x
    rwa [hxlen] at this
  have h3 : KPPlain U (Nat.bits (Nat.size n)) ≤ KPPlain U (natCode (Nat.size n)) + (c₃ : ENat) :=
    hc₃ (Nat.size n)
  calc KPPlain U (natCode k)
      ≤ KPPlain U x + (c₁ : ENat) := h1
    _ ≤ ((Nat.size n : ENat) + KPPlain U (Nat.bits (Nat.size n)) + (c₂ : ENat)) + (c₁ : ENat) := by
        gcongr
    _ ≤ ((Nat.size n : ENat) + (KPPlain U (natCode (Nat.size n)) + (c₃ : ENat)) + (c₂ : ENat))
          + (c₁ : ENat) := by gcongr
    _ = (Nat.size n : ENat) + KPPlain U (natCode (Nat.size n)) + ((c₁ + c₂ + c₃ : ℕ) : ENat) := by
        push_cast; ring

/-! ### The Markov counting bound -/

open Classical in
/-- **Few strings of length `L` are compressible.** With `kL = K(Nat.bits L)`, the number
of length-`L` strings with `K(x) + c ≤ L + kL` satisfies `count · 2^c ≤ 2^c' · 2^L`. -/
theorem card_compressible_mul_two_pow_le (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c' : ℕ, ∀ (L kL c : ℕ), HasPrefixComplexityValue U (Nat.bits L) kL →
      ((stringsOfLength L).filter
          (fun x ↦ KPPlain U x + (c : ENat) ≤ ((L + kL : ℕ) : ENat))).card * 2 ^ c
        ≤ 2 ^ c' * 2 ^ L := by
  obtain ⟨c', hc'⟩ := sum_complexityWeight_stringsOfLength_le U hU
  refine ⟨c', fun L kL c hkL ↦ ?_⟩
  set A := (stringsOfLength L).filter
    (fun x ↦ KPPlain U x + (c : ENat) ≤ ((L + kL : ℕ) : ENat)) with hA
  -- Each compressible string carries weight at least `2^c · 2^{-(L + kL)}`.
  have hterm : ∀ x ∈ A,
      (2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ (L + kL) ≤ complexityWeight (KPPlain U x) := by
    intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    have h := complexityWeight_le_of_le hx'
    rw [complexityWeight_add_nat, complexityWeight_coe, mul_comm] at h
    exact two_pow_mul_le_of_le_inv_two_pow_mul h
  have h1 : (A.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ (L + kL))
      ≤ ∑ x ∈ A, complexityWeight (KPPlain U x) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hterm
  have h2 : (∑ x ∈ A, complexityWeight (KPPlain U x))
      ≤ ∑ x ∈ stringsOfLength L, complexityWeight (KPPlain U x) := by
    rw [hA, Finset.sum_filter]
    exact Finset.sum_le_sum (fun x _ ↦ by split_ifs <;> simp)
  have h3 := hc' L kL hkL
  have h4 : (A.card : ℝ≥0∞) * (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞) ^ 0 * (2 : ℝ≥0∞)⁻¹ ^ (L + kL))
      ≤ ((2 : ℝ≥0∞) ^ c' * (2 : ℝ≥0∞) ^ L) * ((2 : ℝ≥0∞) ^ 0 * (2 : ℝ≥0∞)⁻¹ ^ (L + kL)) := by
    calc (A.card : ℝ≥0∞) * (2 : ℝ≥0∞) ^ c * ((2 : ℝ≥0∞) ^ 0 * (2 : ℝ≥0∞)⁻¹ ^ (L + kL))
        = (A.card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ c * (2 : ℝ≥0∞)⁻¹ ^ (L + kL)) := by ring
      _ ≤ ∑ x ∈ A, complexityWeight (KPPlain U x) := h1
      _ ≤ ∑ x ∈ stringsOfLength L, complexityWeight (KPPlain U x) := h2
      _ ≤ (2 : ℝ≥0∞) ^ c' * (2 : ℝ≥0∞)⁻¹ ^ kL := h3
      _ = ((2 : ℝ≥0∞) ^ c' * (2 : ℝ≥0∞) ^ L) * ((2 : ℝ≥0∞) ^ 0 * (2 : ℝ≥0∞)⁻¹ ^ (L + kL)) := by
          rw [← inv_two_pow_add_mul_two_pow kL L]; ring
  have h5 : (A.card : ℝ≥0∞) * (2 : ℝ≥0∞) ^ c ≤ (2 : ℝ≥0∞) ^ c' * (2 : ℝ≥0∞) ^ L :=
    le_of_mul_two_pow_mul_inv_two_pow_le h4
  exact_mod_cast h5

/-! ### Lower half -/

/-- **Theorem 1.7.3, `≥⁺`.** `Nat.size n + K(Nat.size n) ≤ K⁺(n) + C`. -/
theorem size_add_le_KPlus (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ n : ℕ,
      (Nat.size n : ENat) + KPPlain U (natCode (Nat.size n)) ≤ KPlus U n + (C : ENat) := by
  classical
  obtain ⟨c', hc'⟩ := card_compressible_mul_two_pow_le U hU
  obtain ⟨c₁, hc₁⟩ := KPPlain_bits_le_natCode U hU
  obtain ⟨c₂, hc₂⟩ := KPPlain_natCode_le_bits U hU
  obtain ⟨c₃, hc₃⟩ := KPPlain_natCode_succ_le U hU
  obtain ⟨cb, hcb⟩ := KPPlain_le_trivBound U hU
  have hfin : ∀ z, KPPlain U z ≠ ⊤ := fun z ↦ ne_top_of_le_ne_top (ENat.coe_ne_top _) (hcb z)
  -- Natural-number complexities.
  set kN : BitString → ℕ := fun z ↦ (KPPlain U z).toNat with hkN
  have hk : ∀ z, (kN z : ENat) = KPPlain U z := fun z ↦ ENat.coe_toNat (hfin z)
  have toNat_le : ∀ {a b : BitString} {d : ℕ},
      KPPlain U a ≤ KPPlain U b + (d : ENat) → kN a ≤ kN b + d := by
    intro a b d h
    rw [← hk a, ← hk b] at h
    exact_mod_cast h
  set Csmall := 2 + kN (natCode 0) + kN (natCode 1) + kN (natCode 2) with hCsmall
  set Cbig := c₁ + (c' + 2) + 1 + c₂ + c₃ with hCbig
  refine ⟨Csmall + Cbig, fun n ↦ ?_⟩
  by_cases hn : n < 4
  · -- Small `n`: the left side is bounded by a constant.
    have hs : Nat.size n ≤ 2 := Nat.size_le.mpr (by omega)
    have hsmall : ∀ m ≤ 2, m + kN (natCode m) ≤ Csmall := by
      intro m hm
      interval_cases m <;> omega
    calc (Nat.size n : ENat) + KPPlain U (natCode (Nat.size n))
        = ((Nat.size n + kN (natCode (Nat.size n)) : ℕ) : ENat) := by push_cast; rw [hk]
      _ ≤ ((Csmall + Cbig : ℕ) : ENat) := by
          exact_mod_cast (hsmall _ hs).trans (Nat.le_add_right _ _)
      _ ≤ KPlus U n + ((Csmall + Cbig : ℕ) : ENat) := le_add_self
  · -- Large `n`: `Nat.size n = L + 1` with `L ≥ 2`, and we work at bit-length `L`.
    have hs3 : 3 ≤ Nat.size n := by
      have : 2 < Nat.size n := Nat.lt_size.mpr (by omega)
      omega
    obtain ⟨L, hL⟩ : ∃ L, Nat.size n = L + 1 := ⟨Nat.size n - 1, by omega⟩
    have hL2 : 2 ≤ L := by omega
    rw [hL]
    obtain ⟨kL, hkL⟩ : ∃ kL : ℕ, HasPrefixComplexityValue U (Nat.bits L) kL :=
      ⟨_, (hk (Nat.bits L))⟩
    -- The compressible strings of length `L` number at most `2^(L-2)`.
    set A := (stringsOfLength L).filter
      (fun x ↦ KPPlain U x + ((c' + 2 : ℕ) : ENat) ≤ ((L + kL : ℕ) : ENat)) with hA
    have hAcard : A.card ≤ 2 ^ (L - 2) := by
      have h := hc' L kL (c' + 2) hkL
      have hpow1 : 2 ^ (c' + 2) = 2 ^ c' * 4 := by rw [pow_add]; norm_num
      have hpow2 : 2 ^ L = 2 ^ (L - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      rw [hpow1, hpow2] at h
      have h' : A.card * (2 ^ c' * 4) ≤ 2 ^ (L - 2) * (2 ^ c' * 4) := by
        calc A.card * (2 ^ c' * 4) ≤ 2 ^ c' * (2 ^ (L - 2) * 4) := h
          _ = 2 ^ (L - 2) * (2 ^ c' * 4) := by ring
      exact Nat.le_of_mul_le_mul_right h' (by positivity)
    -- The numbers of bit-length `L`, as strings, number exactly `2^(L-1)`.
    set B := (Finset.Ico (2 ^ (L - 1)) (2 ^ L)).image Nat.bits with hB
    have hbits_inj : Function.Injective Nat.bits :=
      Function.LeftInverse.injective bitsToNat_bits
    have hBcard : B.card = 2 ^ (L - 1) := by
      rw [hB, Finset.card_image_of_injective _ hbits_inj, Nat.card_Ico]
      have : 2 ^ L = 2 ^ (L - 1) * 2 := by
        rw [← Nat.pow_succ]; congr 1; omega
      omega
    have hBsub : B ⊆ stringsOfLength L := by
      intro x hx
      obtain ⟨k, hk', rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hk'
      rw [memStringsOfLength, Nat.size_eq_bits_len]
      apply le_antisymm (Nat.size_le.mpr hhi)
      have := Nat.lt_size.mpr hlo
      omega
    have hlt : A.card < B.card := by
      rw [hBcard]
      exact hAcard.trans_lt (Nat.pow_lt_pow_right (by norm_num) (by omega))
    -- An incompressible number `k` of bit-length `L`.
    obtain ⟨x, hxB, hxA⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    obtain ⟨k, hk', rfl⟩ := Finset.mem_image.mp hxB
    have hxS : Nat.bits k ∈ stringsOfLength L := hBsub hxB
    have hnotc : ¬ (KPPlain U (Nat.bits k) + ((c' + 2 : ℕ) : ENat) ≤ ((L + kL : ℕ) : ENat)) :=
      fun h ↦ hxA (Finset.mem_filter.mpr ⟨hxS, h⟩)
    have hkk : L + kL < kN (Nat.bits k) + (c' + 2) := by
      by_contra hcon
      apply hnotc
      rw [← hk (Nat.bits k)]
      exact_mod_cast not_lt.mp hcon
    -- `k ≤ n`, so `K(k) ≤ K⁺(n)`.
    have hkn : k ≤ n := by
      have h1 : k < 2 ^ L := (Finset.mem_Ico.mp hk').2
      have h2 : 2 ^ L ≤ n := Nat.lt_size.mp (by rw [hL]; omega)
      omega
    have hKk : KPPlain U (natCode k) ≤ KPlus U n := KPPlain_natCode_le_KPlus U hkn
    -- Assemble in `ℕ`.
    have e1 : kN (Nat.bits k) ≤ kN (natCode k) + c₁ := toNat_le (hc₁ k)
    have e2 : kN (natCode L) ≤ kN (Nat.bits L) + c₂ := toNat_le (hc₂ L)
    have e3 : kN (natCode (L + 1)) ≤ kN (natCode L) + c₃ := toNat_le (hc₃ L)
    have ekL : kN (Nat.bits L) = kL := by
      have : (kN (Nat.bits L) : ENat) = (kL : ENat) := by rw [hk]; exact hkL.symm
      exact_mod_cast this
    have hnat : (L + 1) + kN (natCode (L + 1)) ≤ kN (natCode k) + Cbig := by
      rw [hCbig]; omega
    calc ((L + 1 : ℕ) : ENat) + KPPlain U (natCode (L + 1))
        = (((L + 1) + kN (natCode (L + 1)) : ℕ) : ENat) := by push_cast; rw [hk]
      _ ≤ ((kN (natCode k) + Cbig : ℕ) : ENat) := by exact_mod_cast hnat
      _ = KPPlain U (natCode k) + (Cbig : ENat) := by push_cast; rw [hk]
      _ ≤ KPlus U n + ((Csmall + Cbig : ℕ) : ENat) := by
          gcongr
          exact_mod_cast Nat.le_add_left Cbig Csmall

/-! ### Theorem 1.7.3, packaged -/

/-- **Theorem 1.7.3.** `K⁺(n) =⁺ Nat.size n + K(Nat.size n)`: there is a constant `c`
with `Nat.size n + K(Nat.size n) − c ≤ K⁺(n) ≤ Nat.size n + K(Nat.size n) + c` for all
`n`, both inequalities written additively in `ℕ∞`. -/
theorem KPlus_eq_size_add (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ,
      KPlus U n ≤ (Nat.size n : ENat) + KPPlain U (natCode (Nat.size n)) + (c : ENat) ∧
      (Nat.size n : ENat) + KPPlain U (natCode (Nat.size n)) ≤ KPlus U n + (c : ENat) := by
  obtain ⟨c₁, h₁⟩ := KPlus_le_size_add U hU
  obtain ⟨c₂, h₂⟩ := size_add_le_KPlus U hU
  refine ⟨c₁ + c₂, fun n ↦ ⟨?_, ?_⟩⟩
  · calc KPlus U n ≤ (Nat.size n : ENat) + KPPlain U (natCode (Nat.size n)) + (c₁ : ENat) := h₁ n
      _ ≤ (Nat.size n : ENat) + KPPlain U (natCode (Nat.size n)) + ((c₁ + c₂ : ℕ) : ENat) := by
          gcongr; exact_mod_cast Nat.le_add_right c₁ c₂
  · calc (Nat.size n : ENat) + KPPlain U (natCode (Nat.size n)) ≤ KPlus U n + (c₂ : ENat) := h₂ n
      _ ≤ KPlus U n + ((c₁ + c₂ : ℕ) : ENat) := by
          gcongr; exact_mod_cast Nat.le_add_left c₂ c₁

end Kolmogorov
