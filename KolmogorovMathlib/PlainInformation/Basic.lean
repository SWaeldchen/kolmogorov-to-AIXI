/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.Complexity.Properties
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Encoding.Tuples

/-!
# Gács §1.4: transport lemmas and the basic identities of plain complexity

Section 1.4 of Gács' notes develops the elementary information-theoretic
properties of **plain** complexity `C`. The repository has a rich theory of prefix
complexity but, as `COVERAGE.md` records, no standalone plain-pair theory. This
directory supplies it.

Everything in this file rests on two transport lemmas, which between them account
for every identity in Corollary 1.4.2 and for Theorem 1.4.1.

* `condK_ctxMap_le` — post-composition, allowed to read the condition:
  `C(f y x | y) ≤⁺ C(x | y)` for computable `f`. Taking `f` to ignore its first
  argument recovers the repository's `condKMapLe`.
* `condK_le_condK_ctx_map` — pre-composition on the condition:
  `C(x | y) ≤⁺ C(x | g y)`. Knowing `y` you can compute `g y`, so `y` is at least
  as useful a condition. This is the second half of Theorem 1.4.1.

Both are proved the same way: build an auxiliary decompressor, observe that its
complexity is bounded by the relevant `condK` **definitionally** (a `Part.map` or a
substitution in the context slot changes neither the domain nor the outputs in a way
`condK` can see), then invoke optimality.

Pairs are encoded with the repository's `pairCode`, so Gács' `C(x, y | z)` is
`condK U (pairCode x y) z` and `C(x | y, z)` is `condK U x (pairCode y z)`.
-/

namespace Kolmogorov

/-! ### The two transport lemmas -/

/-- **Post-composition, reading the condition.** If `f` is computable then
`C(f y x | y) ≤⁺ C(x | y)`: any program for `x` given `y` becomes a program for
`f y x` given `y`. -/
theorem condK_ctxMap_le (U : Map) (hU : isOptimalConditional U)
    (f : BitString → BitString → BitString)
    (hf : Computable (fun p : BitString × BitString ↦ f p.1 p.2)) :
    ∃ c : ℕ, ∀ x y : BitString, condK U (f y x) y ≤ condK U x y + (c : ENat) := by
  let D : Map := fun pr ↦ (U pr).map (fun z ↦ f pr.2 z)
  have hD : isDecompressor D :=
    Partrec.map hU.1 (hf.comp (Computable.pair (Computable.snd.comp Computable.fst)
      Computable.snd)).to₂
  obtain ⟨c, hc⟩ := hU.2 D hD
  refine ⟨c, fun x y ↦ le_trans (hc (f y x) y) ?_⟩
  gcongr
  apply sInf_le_sInf
  rintro n ⟨p, hp, rfl⟩
  exact ⟨p, Part.mem_map _ hp, rfl⟩

/-- **Pre-composition on the condition.** If `g` is computable then
`C(x | y) ≤⁺ C(x | g y)`: the condition `y` determines `g y`, so it is at least as
informative. This is the second inequality of Theorem 1.4.1. -/
theorem condK_le_condK_ctx_map (U : Map) (hU : isOptimalConditional U)
    (g : BitString → BitString) (hg : Computable g) :
    ∃ c : ℕ, ∀ x y : BitString, condK U x y ≤ condK U x (g y) + (c : ENat) := by
  let D : Map := fun pr ↦ U (pr.1, g pr.2)
  have hD : isDecompressor D :=
    hU.1.comp (Computable.pair Computable.fst (hg.comp Computable.snd))
  obtain ⟨c, hc⟩ := hU.2 D hD
  exact ⟨c, fun x y ↦ hc x y⟩

/-! ### Corollary 1.4.2: the identity list

Each item below is one line of Gács' display, with pairs written through `pairCode`.
-/

/-- `C(x | z) ≤⁺ C(x, y | z)`: a description of the pair describes the first
component. Gács (1.4.1). -/
theorem condK_le_condK_pair_left (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y z : BitString,
      condK U x z ≤ condK U (pairCode x y) z + (c : ENat) := by
  obtain ⟨c, hc⟩ := condKMapLe U hU decodeFirst decodeFirst_computable
  refine ⟨c, fun x y z ↦ ?_⟩
  have h := hc (pairCode x y) z
  rwa [decodeFirst_pairCode] at h

/-- `C(y | z) ≤⁺ C(x, y | z)`: likewise for the second component. -/
theorem condK_le_condK_pair_right (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y z : BitString,
      condK U y z ≤ condK U (pairCode x y) z + (c : ENat) := by
  obtain ⟨c, hc⟩ := condKMapLe U hU decodeSecond decodeSecond_computable
  refine ⟨c, fun x y z ↦ ?_⟩
  have h := hc (pairCode x y) z
  rwa [decodeSecond_pairCode] at h

/-- `C(x | y, z) ≤⁺ C(x | y)`: extra conditions never hurt. -/
theorem condK_pair_ctx_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y z : BitString,
      condK U x (pairCode y z) ≤ condK U x y + (c : ENat) := by
  obtain ⟨c, hc⟩ := condK_le_condK_ctx_map U hU decodeFirst decodeFirst_computable
  refine ⟨c, fun x y z ↦ ?_⟩
  have h := hc x (pairCode y z)
  rwa [decodeFirst_pairCode] at h

/-- The pair swap is computable. -/
theorem swapPair_computable :
    Computable (fun w : BitString ↦ pairCode (decodeSecond w) (decodeFirst w)) :=
  pairCode_primrec.to_comp.comp decodeSecond_computable decodeFirst_computable

/-- `C(x, y | z) ≤⁺ C(y, x | z)`, and hence by symmetry the two are equal up to a
constant. -/
theorem condK_pair_swap_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y z : BitString,
      condK U (pairCode x y) z ≤ condK U (pairCode y x) z + (c : ENat) := by
  obtain ⟨c, hc⟩ := condKMapLe U hU
    (fun w ↦ pairCode (decodeSecond w) (decodeFirst w)) swapPair_computable
  refine ⟨c, fun x y z ↦ ?_⟩
  have h := hc (pairCode y x) z
  rwa [decodeFirst_pairCode, decodeSecond_pairCode] at h

/-- `C(x | y, z) ≤⁺ C(x | z, y)`: the order of the conditions is immaterial. -/
theorem condK_ctx_swap_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y z : BitString,
      condK U x (pairCode y z) ≤ condK U x (pairCode z y) + (c : ENat) := by
  obtain ⟨c, hc⟩ := condK_le_condK_ctx_map U hU
    (fun w ↦ pairCode (decodeSecond w) (decodeFirst w)) swapPair_computable
  refine ⟨c, fun x y z ↦ ?_⟩
  have h := hc x (pairCode y z)
  rwa [decodeFirst_pairCode, decodeSecond_pairCode] at h

/-- `C(x | x, z) ≤⁺ 0`: the condition already contains the answer. -/
theorem condK_self_ctx_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x z : BitString, condK U x (pairCode x z) ≤ (c : ENat) := by
  obtain ⟨c, hc⟩ := condKComp U hU decodeFirst decodeFirst_computable
  refine ⟨c, fun x z ↦ ?_⟩
  have h := hc (pairCode x z)
  rwa [decodeFirst_pairCode] at h

/-- `C(x, y | x, z) ≤⁺ C(y | x, z)`: the first component is free, being present in
the condition. -/
theorem condK_pair_ctx_dup_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x y z : BitString,
      condK U (pairCode x y) (pairCode x z) ≤ condK U y (pairCode x z) + (c : ENat) := by
  obtain ⟨c, hc⟩ := condK_ctxMap_le U hU (fun w v ↦ pairCode (decodeFirst w) v)
    (pairCode_primrec.to_comp.comp (decodeFirst_computable.comp Computable.fst) Computable.snd)
  refine ⟨c, fun x y z ↦ ?_⟩
  have h := hc y (pairCode x z)
  rwa [decodeFirst_pairCode] at h

/-! ### `C(x, x) =⁺ C(x)`, Gács (1.4.2) -/

/-- Duplication is computable. -/
theorem dupPair_computable : Computable (fun x : BitString ↦ pairCode x x) :=
  pairCode_primrec.to_comp.comp Computable.id Computable.id

/-- `C(x, x) ≤⁺ C(x)`. -/
theorem plainK_pair_self_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x : BitString, plainK U (pairCode x x) ≤ plainK U x + (c : ENat) := by
  obtain ⟨c, hc⟩ := plainKMapLe U hU (fun x ↦ pairCode x x) dupPair_computable
  exact ⟨c, hc⟩

/-- `C(x) ≤⁺ C(x, x)`. -/
theorem plainK_le_plainK_pair_self (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x : BitString, plainK U x ≤ plainK U (pairCode x x) + (c : ENat) := by
  obtain ⟨c, hc⟩ := plainKMapLe U hU decodeFirst decodeFirst_computable
  refine ⟨c, fun x ↦ ?_⟩
  have h := hc (pairCode x x)
  rwa [decodeFirst_pairCode] at h

/-- **Gács (1.4.2)**: `C(x, x) =⁺ C(x)`, both directions with one constant. -/
theorem plainK_pair_self_eq (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, ∀ x : BitString,
      plainK U (pairCode x x) ≤ plainK U x + (c : ENat) ∧
      plainK U x ≤ plainK U (pairCode x x) + (c : ENat) := by
  obtain ⟨c₁, h₁⟩ := plainK_pair_self_le U hU
  obtain ⟨c₂, h₂⟩ := plainK_le_plainK_pair_self U hU
  refine ⟨c₁ + c₂, fun x ↦ ⟨?_, ?_⟩⟩
  · exact (h₁ x).trans (by gcongr; exact_mod_cast Nat.le_add_right c₁ c₂)
  · exact (h₂ x).trans (by gcongr; exact_mod_cast Nat.le_add_left c₂ c₁)

end Kolmogorov
