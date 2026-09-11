/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.PlainInformation.Subadditivity

/-!
# Gács Theorems 1.4.4 and 1.4.5: the self-referential identities

Two identities that Gács calls "strange", because they say a shortest description
carries *more* than the string it describes, at no extra cost.

* **Theorem 1.4.4**: `C(x, C(x)) =⁺ C(x)`. Describing `x` together with its own
  complexity is no harder than describing `x`.
* **Theorem 1.4.5**: `C(y | x, i − C(y | x, i)) ≤⁺ C(y | x, i)`. Left as an exercise
  in the text.

Both rest on the same device, the one that also drives Theorem 1.7.1: **a program
knows its own length**. A machine reading a program `p` may use `|p|` as data. If `p`
is a *shortest* program for `x`, then `|p|` *is* `C(x)`, so the machine can output the
pair `⟨x, C(x)⟩` while being handed only a description of `x`. No search and no
self-reference paradox: the machine never computes `C`, it merely reports the length
of the input it was given, which happens to equal `C(x)` on the inputs we feed it.

For 1.4.5 the same trick recovers a *lost* datum: the program is handed `i − k` in the
condition, where `k` is the length of the program itself, so it reconstitutes
`i = (i − k) + k` and then runs the original program.
-/

namespace Kolmogorov

/-! ### The self-length machine -/

/-- Run `U` on the program in the empty context and pair the output with the
program's own length, written in binary. This is Gács' `A(p) = ⟨U(p), l(p)⟩`. -/
noncomputable def selfLenPlain (U : Map) : Map := fun pr ↦
  (U (pr.1, [])).map (fun x ↦ pairCode x (Nat.bits pr.1.length))

/-- The self-length machine is partial recursive. -/
theorem selfLenPlain_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (selfLenPlain U) := by
  have hf : Partrec (fun pr : BitString × BitString ↦ U (pr.1, [])) :=
    hU.comp (Computable.fst.pair (Computable.const []))
  have hg : Computable₂ (fun (pr : BitString × BitString) (x : BitString) ↦
      pairCode x (Nat.bits pr.1.length)) :=
    (pairCode_primrec.to_comp.comp Computable.snd
      (natBitsComputable.comp
        (Computable.list_length.comp (Computable.fst.comp Computable.fst)))).to₂
  exact (hf.map hg).of_eq (fun pr ↦ rfl)

/-- What the self-length machine produces. -/
theorem produces_selfLenPlain {U : Map} {p x z : BitString} (h : produces U p [] x) :
    produces (selfLenPlain U) p z (pairCode x (Nat.bits p.length)) :=
  Part.mem_map _ h

/-! ### Theorem 1.4.4 -/

/-- **Gács Theorem 1.4.4, `≤⁺`.** `C(x, C(x)) ≤⁺ C(x)`. Feed a shortest program for
`x` to the self-length machine: it emits `x` paired with the length of that program,
which is exactly `C(x)`. -/
theorem plainK_pair_selfComplexity_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (k : ℕ), (k : ENat) = plainK U x →
      plainK U (pairCode x (Nat.bits k)) ≤ plainK U x + (c : ENat) := by
  obtain ⟨c, hc⟩ := hU.2 (selfLenPlain U) (selfLenPlain_isDecompressor U hU.1)
  refine ⟨c, fun x k hk ↦ ?_⟩
  obtain ⟨p, hp, hplen⟩ : ∃ p, produces U p [] x ∧ (programLength p : ENat) = plainK U x :=
    KP_mem_candidateLengths_of_ne_top (M := U) (x := x) (y := [])
      (by rw [KP_eq_condK]; exact plainK_ne_top U hU x)
  have hpk : p.length = k := by
    have : (p.length : ENat) = (k : ENat) := by rw [hplen, hk]
    exact_mod_cast this
  have hprod : produces (selfLenPlain U) p [] (pairCode x (Nat.bits k)) := by
    have := produces_selfLenPlain (z := []) hp
    rwa [hpk] at this
  calc plainK U (pairCode x (Nat.bits k))
      ≤ condK (selfLenPlain U) (pairCode x (Nat.bits k)) [] + (c : ENat) := hc _ []
    _ ≤ (programLength p : ENat) + (c : ENat) := by
        gcongr
        rw [← KP_eq_condK]
        exact KP_le_programLength_of_produces hprod
    _ = plainK U x + (c : ENat) := by rw [hplen]

/-- **Gács Theorem 1.4.4, `≥⁺`.** `C(x) ≤⁺ C(x, C(x))`, a special case of
`C(x) ≤⁺ C(x, y)`. -/
theorem plainK_le_plainK_pair_selfComplexity (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (k : ℕ),
      plainK U x ≤ plainK U (pairCode x (Nat.bits k)) + (c : ENat) := by
  obtain ⟨c, hc⟩ := condK_le_condK_pair_left U hU
  exact ⟨c, fun x k ↦ hc x (Nat.bits k) []⟩

/-- **Gács Theorem 1.4.4.** `C(x, C(x)) =⁺ C(x)`, both directions with one
constant. The complexity is supplied as the natural number `k`, which exists by
`exists_plainK_value`. -/
theorem plainK_pair_selfComplexity_eq (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x : BitString) (k : ℕ), (k : ENat) = plainK U x →
      plainK U (pairCode x (Nat.bits k)) ≤ plainK U x + (c : ENat) ∧
      plainK U x ≤ plainK U (pairCode x (Nat.bits k)) + (c : ENat) := by
  obtain ⟨c₁, h₁⟩ := plainK_pair_selfComplexity_le U hU
  obtain ⟨c₂, h₂⟩ := plainK_le_plainK_pair_selfComplexity U hU
  refine ⟨c₁ + c₂, fun x k hk ↦ ⟨?_, ?_⟩⟩
  · exact (h₁ x k hk).trans (by gcongr; exact_mod_cast Nat.le_add_right c₁ c₂)
  · exact (h₂ x k).trans (by gcongr; exact_mod_cast Nat.le_add_left c₂ c₁)

/-! ### Theorem 1.4.5 -/

/-- The **length-restoring machine**: the condition is `⟨x, m⟩` with `m = i − k`,
where `k` is the length of the program itself. Restore `i = m + k`, then run `U` on
the program in the context `⟨x, i⟩`. -/
noncomputable def restoreLenPlain (U : Map) : Map := fun pr ↦
  U (pr.1, pairCode (decodeFirst pr.2)
    (Nat.bits (bitsToNat (decodeSecond pr.2) + pr.1.length)))

/-- The length-restoring machine is partial recursive. -/
theorem restoreLenPlain_isDecompressor (U : Map) (hU : isDecompressor U) :
    isDecompressor (restoreLenPlain U) := by
  have hctx : Computable (fun pr : BitString × BitString ↦
      pairCode (decodeFirst pr.2)
        (Nat.bits (bitsToNat (decodeSecond pr.2) + pr.1.length))) :=
    pairCode_primrec.to_comp.comp
      (decodeFirst_computable.comp Computable.snd)
      (natBitsComputable.comp
        (Primrec.nat_add.to_comp.comp
          (bitsToNat_computable.comp (decodeSecond_computable.comp Computable.snd))
          (Computable.list_length.comp Computable.fst)))
  exact hU.comp (Computable.pair Computable.fst hctx)

/-- **Gács Theorem 1.4.5.** `C(y | x, i − C(y | x, i)) ≤⁺ C(y | x, i)`.

Write `k = C(y | ⟨x, i⟩)` and feed a shortest such program to the length-restoring
machine in the context `⟨x, i − k⟩`. The machine reads its own length `k`, rebuilds
`i = (i − k) + k`, and runs the program in the original context. -/
theorem condK_pair_sub_selfComplexity_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ (x y : BitString) (i k : ℕ),
      (k : ENat) = condK U y (pairCode x (Nat.bits i)) → k ≤ i →
        condK U y (pairCode x (Nat.bits (i - k)))
          ≤ condK U y (pairCode x (Nat.bits i)) + (c : ENat) := by
  obtain ⟨c, hc⟩ := hU.2 (restoreLenPlain U) (restoreLenPlain_isDecompressor U hU.1)
  refine ⟨c, fun x y i k hk hki ↦ ?_⟩
  obtain ⟨p, hp, hplen⟩ : ∃ p, produces U p (pairCode x (Nat.bits i)) y ∧
      (programLength p : ENat) = condK U y (pairCode x (Nat.bits i)) :=
    KP_mem_candidateLengths_of_ne_top (M := U) (x := y) (y := pairCode x (Nat.bits i))
      (by rw [KP_eq_condK]; exact condK_ne_top U hU y _)
  have hpk : p.length = k := by
    have : (p.length : ENat) = (k : ENat) := by rw [hplen, hk]
    exact_mod_cast this
  -- On the shortened context the machine restores the original one.
  have hprod : produces (restoreLenPlain U) p (pairCode x (Nat.bits (i - k))) y := by
    change y ∈ U (p, pairCode (decodeFirst _) (Nat.bits (bitsToNat (decodeSecond _) + p.length)))
    rw [decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits, hpk,
      show i - k + k = i by omega]
    exact hp
  calc condK U y (pairCode x (Nat.bits (i - k)))
      ≤ condK (restoreLenPlain U) y (pairCode x (Nat.bits (i - k))) + (c : ENat) := hc _ _
    _ ≤ (programLength p : ENat) + (c : ENat) := by
        gcongr
        rw [← KP_eq_condK]
        exact KP_le_programLength_of_produces hprod
    _ = condK U y (pairCode x (Nat.bits i)) + (c : ENat) := by rw [hplen]

end Kolmogorov
