/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.PlainInformation.Basic
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Foundation.NatEncoding
import KolmogorovMathlib.Prefix.TwoStage

/-!
# Gács Theorem 1.4.2: subadditivity of plain complexity

  `C(x, y) ≤⁺ J(C(x)) + C(y | x)`,  where `J(u) = u + 2 log u`.

To describe the pair it suffices to describe `x`, and then to describe `y` using
`x`. The two programs are concatenated, so the decoder must be told where the first
one ends. Gács pays for that with the self-delimiting code `ι(w) = β(|w|)^o w`,
whose length is `|w| + 2 log |w| + O(1)`, which is where the `J` comes from.

## The code

Here that code is `sdPair w q = pairCode (Nat.bits |w|) (w ++ q)`: the repository's
`pairCode` already prefixes its first argument with a unary length marker, so
feeding it the *binary* representation of `|w|` yields exactly Gács' `ι`. Its length
is `|w| + 2·|Nat.bits |w|| + 1 + |q|`, and `(Nat.bits m).length` is the bit-length of
`m`, i.e. `log₂ m` up to one. Decoding is `bitsToNat ∘ decodeFirst` for the length
and `take`/`drop` on `decodeSecond` for the two halves — all primitive recursive, and
**no search is needed**, because the length is written down explicitly.

## Statement shape

The bound is stated with the complexities supplied as natural numbers, `kx` for
`C(x)` and `ky` for `C(y | x)`. Both are finite for an optimal `U`
(`plainK_ne_top`, `condK_ne_top`), so the hypotheses are always dischargeable; taking
them as inputs keeps the arithmetic in `ℕ` and avoids `⊤` bookkeeping.
-/

namespace Kolmogorov

/-! ### Finiteness of plain complexity -/

/-- For an optimal `U`, plain complexity is finite. -/
theorem plainK_ne_top (U : Map) (hU : isOptimalConditional U) (x : BitString) :
    plainK U x ≠ ⊤ := by
  obtain ⟨c, hc⟩ := plainKLeLength U hU
  exact ne_top_of_le_ne_top (by simp) (hc x)

/-- For an optimal `U`, conditional complexity is finite. -/
theorem condK_ne_top (U : Map) (hU : isOptimalConditional U) (x y : BitString) :
    condK U x y ≠ ⊤ := by
  obtain ⟨c, hc⟩ := condKLePlainK U hU
  exact ne_top_of_le_ne_top
    (by simp [plainK_ne_top U hU x]) (hc x y)

/-- The natural-number value of a finite plain complexity. -/
theorem exists_plainK_value (U : Map) (hU : isOptimalConditional U) (x : BitString) :
    ∃ k : ℕ, (k : ENat) = plainK U x := by
  lift plainK U x to ℕ using plainK_ne_top U hU x with k hk
  exact ⟨k, rfl⟩

/-- The natural-number value of a finite conditional complexity. -/
theorem exists_condK_value (U : Map) (hU : isOptimalConditional U) (x y : BitString) :
    ∃ k : ℕ, (k : ENat) = condK U x y := by
  lift condK U x y to ℕ using condK_ne_top U hU x y with k hk
  exact ⟨k, rfl⟩

/-! ### The two-part program -/

/-- The **two-part program**: the binary length of `w`, then `w`, then `q`. This is
Gács' `ι(w) q`, realised through `pairCode`. -/
def sdPair (w q : BitString) : BitString := pairCode (Nat.bits w.length) (w ++ q)

/-- The length of a two-part program: `|w| + 2·(bit-length of |w|) + 1 + |q|`. -/
theorem length_sdPair (w q : BitString) :
    (sdPair w q).length = 2 * (Nat.bits w.length).length + 1 + w.length + q.length := by
  unfold sdPair
  rw [length_pairCode, List.length_append]
  omega

/-- Recovering the length of the first half. -/
@[simp] theorem sdPair_len (w q : BitString) :
    bitsToNat (decodeFirst (sdPair w q)) = w.length := by
  unfold sdPair
  rw [decodeFirst_pairCode, bitsToNat_bits]

/-- Recovering the first half. -/
@[simp] theorem sdPair_fst (w q : BitString) :
    (decodeSecond (sdPair w q)).take (bitsToNat (decodeFirst (sdPair w q))) = w := by
  rw [sdPair_len]
  unfold sdPair
  rw [decodeSecond_pairCode, List.take_left]

/-- Recovering the second half. -/
@[simp] theorem sdPair_snd (w q : BitString) :
    (decodeSecond (sdPair w q)).drop (bitsToNat (decodeFirst (sdPair w q))) = q := by
  rw [sdPair_len]
  unfold sdPair
  rw [decodeSecond_pairCode, List.drop_left]

/-! ### The two-stage decompressor -/

/-- The **two-stage decompressor**: split the program, run `U` on the first half to
get `x`, run `U` on the second half *in the context* `x` to get `y`, output the pair.
The condition slot is ignored. -/
noncomputable def twoStagePlain (U : Map) : Map := fun pr ↦
  (U ((decodeSecond pr.1).take (bitsToNat (decodeFirst pr.1)), [])).bind (fun x ↦
    (U ((decodeSecond pr.1).drop (bitsToNat (decodeFirst pr.1)), x)).map (fun y ↦
      pairCode x y))

/-- The two-stage decompressor is partial recursive. -/
theorem twoStagePlain_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (twoStagePlain U) := by
  have hlen : Computable (fun pr : BitString × BitString ↦
      bitsToNat (decodeFirst pr.1)) :=
    bitsToNat_computable.comp (decodeFirst_computable.comp Computable.fst)
  have hrest : Computable (fun pr : BitString × BitString ↦ decodeSecond pr.1) :=
    decodeSecond_computable.comp Computable.fst
  have hfst : Partrec (fun pr : BitString × BitString ↦
      U ((decodeSecond pr.1).take (bitsToNat (decodeFirst pr.1)), [])) :=
    hU.comp (Computable.pair (primrec_list_take.to_comp.comp hrest hlen)
      (Computable.const []))
  have hsnd : Partrec₂ (fun (pr : BitString × BitString) (x : BitString) ↦
      (U ((decodeSecond pr.1).drop (bitsToNat (decodeFirst pr.1)), x)).map
        (fun y ↦ pairCode x y)) := by
    have hcall : Partrec (fun r : (BitString × BitString) × BitString ↦
        U ((decodeSecond r.1.1).drop (bitsToNat (decodeFirst r.1.1)), r.2)) :=
      hU.comp (Computable.pair
        (primrec_list_drop.to_comp.comp (hrest.comp Computable.fst)
          (hlen.comp Computable.fst))
        Computable.snd)
    have hpost : Computable₂ (fun (r : (BitString × BitString) × BitString)
        (y : BitString) ↦ pairCode r.2 y) :=
      (pairCode_primrec.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd).to₂
    exact (hcall.map hpost).of_eq (fun r ↦ rfl)
  exact (Partrec.bind hfst hsnd).of_eq (fun pr ↦ rfl)

/-- The two-stage decompressor produces the pair from a two-part program. -/
theorem produces_twoStagePlain {U : Map} {w q x y z : BitString}
    (hx : produces U w [] x) (hy : produces U q x y) :
    produces (twoStagePlain U) (sdPair w q) z (pairCode x y) := by
  change pairCode x y ∈ Part.bind _ _
  rw [Part.mem_bind_iff]
  refine ⟨x, ?_, ?_⟩
  · rw [sdPair_fst]; exact hx
  · rw [sdPair_snd]; exact Part.mem_map _ hy

/-! ### Theorem 1.4.2 -/

/-- **Gács Theorem 1.4.2.** `C(x, y) ≤⁺ J(C(x)) + C(y | x)` with
`J(u) = u + 2 log u`, the logarithm realised as the bit-length `(Nat.bits ·).length`.

Given the values `kx = C(x)` and `ky = C(y | x)` (both finite by
`exists_plainK_value` and `exists_condK_value`), the pair is described by
concatenating a shortest program for `x`, prefixed by its own length in binary, with
a shortest program for `y` given `x`. -/
theorem plainK_pairCode_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString) (kx ky : ℕ),
      (kx : ENat) = plainK U x → (ky : ENat) = condK U y x →
        plainK U (pairCode x y)
          ≤ ((kx + 2 * (Nat.bits kx).length + ky + c : ℕ) : ENat) := by
  obtain ⟨c, hc⟩ := hU.2 (twoStagePlain U) (twoStagePlain_isDecompressor U hU.1)
  refine ⟨c + 1, fun x y kx ky hkx hky ↦ ?_⟩
  -- Shortest programs for `x` and for `y` given `x`.
  obtain ⟨w, hw, hwlen⟩ : ∃ w, produces U w [] x ∧ (programLength w : ENat) = plainK U x :=
    KP_mem_candidateLengths_of_ne_top (M := U) (x := x) (y := [])
      (by rw [KP_eq_condK]; exact plainK_ne_top U hU x)
  obtain ⟨q, hq, hqlen⟩ : ∃ q, produces U q x y ∧ (programLength q : ENat) = condK U y x :=
    KP_mem_candidateLengths_of_ne_top (M := U) (x := y) (y := x)
      (by rw [KP_eq_condK]; exact condK_ne_top U hU y x)
  have hwn : w.length = kx := by
    have : (w.length : ENat) = (kx : ENat) := by rw [hwlen, hkx]
    exact_mod_cast this
  have hqn : q.length = ky := by
    have : (q.length : ENat) = (ky : ENat) := by rw [hqlen, hky]
    exact_mod_cast this
  -- The two-part program describes the pair on the auxiliary machine.
  have hprod := produces_twoStagePlain (z := []) hw hq
  have hbound : condK (twoStagePlain U) (pairCode x y) []
      ≤ ((sdPair w q).length : ENat) := by
    rw [← KP_eq_condK]
    exact KP_le_programLength_of_produces hprod
  have hlen : (sdPair w q).length = 2 * (Nat.bits kx).length + 1 + kx + ky := by
    rw [length_sdPair, hwn, hqn]
  calc plainK U (pairCode x y)
      ≤ condK (twoStagePlain U) (pairCode x y) [] + (c : ENat) := hc (pairCode x y) []
    _ ≤ (((sdPair w q).length : ℕ) : ENat) + (c : ENat) := by gcongr
    _ = ((2 * (Nat.bits kx).length + 1 + kx + ky + c : ℕ) : ENat) := by
        rw [hlen]; push_cast; ring
    _ = ((kx + 2 * (Nat.bits kx).length + ky + (c + 1) : ℕ) : ENat) := by
        congr 1; omega

/-! ### Corollary 1.4.3 -/

/-- **Gács Corollary 1.4.3**, the specialisation `C(x, y) ≤⁺ J(C(x)) + C(y)`:
conditioning on `x` only helps, so the bound holds with `C(y)` in place of
`C(y | x)`. -/
theorem plainK_pairCode_le_plainK (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString) (kx ky : ℕ),
      (kx : ENat) = plainK U x → (ky : ENat) = plainK U y →
        plainK U (pairCode x y)
          ≤ ((kx + 2 * (Nat.bits kx).length + ky + c : ℕ) : ENat) := by
  obtain ⟨c₁, hc₁⟩ := plainK_pairCode_le U hU
  obtain ⟨c₂, hc₂⟩ := condKLePlainK U hU
  refine ⟨c₁ + c₂, fun x y kx ky hkx hky ↦ ?_⟩
  -- `C(y | x) ≤ C(y) + c₂`, so pick the value of `C(y | x)` and compare.
  obtain ⟨k', hk'⟩ := exists_condK_value U hU y x
  have hk'le : k' ≤ ky + c₂ := by
    have h : (k' : ENat) ≤ ((ky + c₂ : ℕ) : ENat) := by
      rw [hk']
      calc condK U y x ≤ plainK U y + (c₂ : ENat) := hc₂ y x
        _ = ((ky + c₂ : ℕ) : ENat) := by rw [← hky]; push_cast; ring
    exact_mod_cast h
  calc plainK U (pairCode x y)
      ≤ ((kx + 2 * (Nat.bits kx).length + k' + c₁ : ℕ) : ENat) := hc₁ x y kx k' hkx hk'
    _ ≤ ((kx + 2 * (Nat.bits kx).length + ky + (c₁ + c₂) : ℕ) : ENat) := by
        have : kx + 2 * (Nat.bits kx).length + k' + c₁
            ≤ kx + 2 * (Nat.bits kx).length + ky + (c₁ + c₂) := by omega
        exact_mod_cast this

/-- **Corollary 1.4.3, general form.** Applying any computable function to the pair
cannot increase the bound. -/
theorem plainK_map_pairCode_le (U : Map) (hU : isOptimalConditional U)
    (f : BitString → BitString) (hf : Computable f) :
    ∃ c : ℕ, ∀ (x y : BitString) (kx ky : ℕ),
      (kx : ENat) = plainK U x → (ky : ENat) = condK U y x →
        plainK U (f (pairCode x y))
          ≤ ((kx + 2 * (Nat.bits kx).length + ky + c : ℕ) : ENat) := by
  obtain ⟨c₁, hc₁⟩ := plainK_pairCode_le U hU
  obtain ⟨c₂, hc₂⟩ := plainKMapLe U hU f hf
  refine ⟨c₁ + c₂, fun x y kx ky hkx hky ↦ ?_⟩
  calc plainK U (f (pairCode x y))
      ≤ plainK U (pairCode x y) + (c₂ : ENat) := hc₂ (pairCode x y)
    _ ≤ ((kx + 2 * (Nat.bits kx).length + ky + c₁ : ℕ) : ENat) + (c₂ : ENat) := by
        gcongr; exact hc₁ x y kx ky hkx hky
    _ = ((kx + 2 * (Nat.bits kx).length + ky + (c₁ + c₂) : ℕ) : ENat) := by
        push_cast; ring

end Kolmogorov
