/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.PlainInformation.Subadditivity

/-!
# Gács Theorem 1.4.3: complexity from a position in an enumeration

  `C(x | a) ≤⁺ log |E_a|`  for every `x ∈ E_a`,

where `a ↦ E_a` is a computable family of finite sets. An element of a finite set is
described by its **position** in the set, and a position below `|E_a|` fits in
`log |E_a|` bits.

## Why this is short for plain complexity

For prefix complexity the analogous statement needs care, because the index has to be
delimited: `Foundation/EnumerationComplexity.lean` pays a logarithmic surcharge for
that. Plain complexity needs nothing of the sort. The decompressor is handed the
condition `a`, from which it recomputes the whole list `E_a`, so it can read the
program as a bare binary numeral and index into the list. No delimiter, no padding,
no search.

So the machine is simply `D(p, a) = (E a)[bitsToNat p]`, and feeding it the binary
representation of the position gives the bound. Two forms are proved: with the
position itself (`condK_le_index`), and with any `n` bounding `log |E_a|`
(`condK_le_log_card`).

The family is a computable `List`-valued function; `Finset`-valued families are
covered by composing with `Finset.toList`.
-/

namespace Kolmogorov

/-! ### The indexing machine -/

/-- The **indexing machine** for a family `E`: read the program as a binary numeral
and return the element of `E a` at that position. -/
def indexMap (E : BitString → List BitString) : Map := fun pr ↦
  Part.some ((E pr.2).getD (bitsToNat pr.1) [])

/-- The indexing machine is a decompressor whenever the family is computable. -/
theorem indexMap_isDecompressor {E : BitString → List BitString} (hE : Computable E) :
    isDecompressor (indexMap E) := by
  have h : Computable (fun pr : BitString × BitString ↦
      (E pr.2).getD (bitsToNat pr.1) []) :=
    (Primrec.list_getD ([] : BitString)).to_comp.comp (hE.comp Computable.snd)
      (bitsToNat_computable.comp Computable.fst)
  exact h.partrec

/-- What the indexing machine produces on a binary numeral. -/
theorem produces_indexMap (E : BitString → List BitString) (a : BitString) (i : ℕ) :
    produces (indexMap E) (Nat.bits i) a ((E a).getD i []) := by
  have hb : bitsToNat (Nat.bits i) = i := bitsToNat_bits i
  change (E a).getD i [] ∈ Part.some ((E a).getD (bitsToNat (Nat.bits i)) [])
  rw [hb]
  exact Part.mem_some _

/-! ### The bound by position -/

/-- **Position bound.** The element at position `i` of `E a` has conditional
complexity at most the bit-length of `i`, up to a constant depending only on `U` and
the family. -/
theorem condK_le_index (U : Map) (hU : isOptimalConditional U)
    {E : BitString → List BitString} (hE : Computable E) :
    ∃ c : ℕ, ∀ (a : BitString) (i : ℕ),
      condK U ((E a).getD i []) a ≤ ((Nat.bits i).length : ENat) + (c : ENat) := by
  obtain ⟨c, hc⟩ := hU.2 (indexMap E) (indexMap_isDecompressor hE)
  refine ⟨c, fun a i ↦ ?_⟩
  calc condK U ((E a).getD i []) a
      ≤ condK (indexMap E) ((E a).getD i []) a + (c : ENat) := hc _ _
    _ ≤ (programLength (Nat.bits i) : ENat) + (c : ENat) := by
        gcongr
        rw [← KP_eq_condK]
        exact KP_le_programLength_of_produces (produces_indexMap E a i)

/-! ### Theorem 1.4.3 -/

/-- **Gács Theorem 1.4.3.** If `E` is a computable family of lists and the list `E a`
has at most `2 ^ n` entries, then every member of `E a` has conditional complexity at
most `n`, up to a constant. In Gács' notation, `C(x | a) ≤⁺ log |E_a|`.

The bit-length of a position `i < 2 ^ n` is at most `n` (`Nat.size_le`), so the
position bound `condK_le_index` specialises. -/
theorem condK_le_log_card (U : Map) (hU : isOptimalConditional U)
    {E : BitString → List BitString} (hE : Computable E) :
    ∃ c : ℕ, ∀ (a x : BitString) (n : ℕ), (E a).length ≤ 2 ^ n → x ∈ E a →
      condK U x a ≤ ((n : ℕ) : ENat) + (c : ENat) := by
  obtain ⟨c, hc⟩ := condK_le_index U hU hE
  refine ⟨c, fun a x n hcard hx ↦ ?_⟩
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
  -- The list entry at `i` is `x`.
  have hgetD : (E a).getD i [] = x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hix]; rfl
  -- The position is below `2 ^ n`, so its bit-length is at most `n`.
  have hilt : i < 2 ^ n := lt_of_lt_of_le hi hcard
  have hbits : (Nat.bits i).length ≤ n := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr hilt
  calc condK U x a
      = condK U ((E a).getD i []) a := by rw [hgetD]
    _ ≤ ((Nat.bits i).length : ENat) + (c : ENat) := hc a i
    _ ≤ ((n : ℕ) : ENat) + (c : ENat) := by gcongr

/-- **Theorem 1.4.3 for `Finset`-valued families.** Same statement with the family
given as computable finite sets, via `Finset.toList`. -/
theorem condK_le_log_card_finset (U : Map) (hU : isOptimalConditional U)
    {E : BitString → Finset BitString}
    (hE : Computable (fun a ↦ (E a).toList)) :
    ∃ c : ℕ, ∀ (a x : BitString) (n : ℕ), (E a).card ≤ 2 ^ n → x ∈ E a →
      condK U x a ≤ ((n : ℕ) : ENat) + (c : ENat) := by
  obtain ⟨c, hc⟩ := condK_le_log_card U hU hE
  refine ⟨c, fun a x n hcard hx ↦ ?_⟩
  refine hc a x n ?_ ?_
  · rwa [Finset.length_toList]
  · rwa [Finset.mem_toList]

end Kolmogorov
