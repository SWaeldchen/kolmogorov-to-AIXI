/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.Prefix.OptimalExistence

/-!
# Prefix-prepending universality

The lower half of Gács' Theorem 1.7.1 counts programs of one *exact* length. To
transport programs of an auxiliary machine `G` into programs of the universal
machine `U` while controlling their length exactly, an inequality
`|translate p| ≤ |p| + c` (as in `ProgramSimulation`) is not enough: the
translation must be *concatenation with a fixed tag*, `p ↦ tag ++ p`, whose
length is exactly `|tag| + |p|`.

This is Gács' formulation of universality (`T(gp) = G(p)`, line 1646 of the
source) and it is also how the repository's concrete universal machine actually
works: `taggedUnionSimulation` translates by `p ↦ natCode i ++ p`. The abstract
`IsSimulationUniversal` forgets this. Here we name the stronger notion,

* `PrefixPrependSimulation M N` — a tag `g` with
  `produces N p y x → produces M (g ++ p) y x`;
* `IsPrefixPrependUniversal U` — `U` is a prefix decompressor that
  prefix-prepend simulates every prefix decompressor;

and record two facts: `universalPrefixMachine` has it
(`universalPrefixMachine_isPrefixPrependUniversal`), and it implies the existing
`IsSimulationUniversal`, hence `IsOptimalPrefixConditional`
(`IsPrefixPrependUniversal.isOptimalPrefixConditional`). The second fact is what
makes the coding theorem available under this hypothesis.

Only the forward implication `produces N … → produces M …` is required: the
counting argument exhibits programs that *do* produce a given output and never
needs to reason about programs that fail to.
-/

namespace Kolmogorov

/-! ### The simulation and the universality predicate -/

/-- A **prefix-prepend simulation** of `N` by `M`: a fixed tag such that whatever
`N` produces from `p`, `M` produces from `tag ++ p`, in every context. -/
structure PrefixPrependSimulation (M N : Map) where
  /-- The tag prepended to every `N`-program. -/
  tag : BitString
  /-- Prepending the tag reproduces `N`'s outputs on `M`. -/
  simulates : ∀ p y x, produces N p y x → produces M (tag ++ p) y x

/-- A map `U` is **prefix-prepend universal** if it is a prefix decompressor and
prefix-prepend simulates every prefix decompressor. -/
def IsPrefixPrependUniversal (U : Map) : Prop :=
  IsPrefixDecompressor U ∧
    ∀ M, IsPrefixDecompressor M → Nonempty (PrefixPrependSimulation U M)

/-- A prefix-prepend universal map is in particular a prefix decompressor. -/
theorem IsPrefixPrependUniversal.isPrefixDecompressor {U : Map}
    (hU : IsPrefixPrependUniversal U) : IsPrefixDecompressor U :=
  hU.1

/-- The length of a tagged program is exactly the tag length plus the program
length. This exactness is the whole point of the notion. -/
theorem PrefixPrependSimulation.length_tag_append {M N : Map}
    (s : PrefixPrependSimulation M N) (p : BitString) :
    programLength (s.tag ++ p) = programLength s.tag + programLength p :=
  List.length_append

/-! ### Relation to the existing simulation notions -/

/-- A prefix-prepend simulation is a `ProgramSimulation` with constant `|tag|`:
concatenation with a fixed tag is injective, inflates length by exactly `|tag|`,
and simulates by hypothesis. -/
def PrefixPrependSimulation.toProgramSimulation {M N : Map}
    (s : PrefixPrependSimulation M N) : ProgramSimulation M N s.tag.length where
  translate := fun p ↦ s.tag ++ p
  injective := fun _ _ h ↦ List.append_cancel_left h
  length_le := fun p ↦ by
    simp only [programLength, List.length_append]; omega
  simulates := s.simulates

/-- Prefix-prepend universality implies simulation universality. -/
theorem IsPrefixPrependUniversal.isSimulationUniversal {U : Map}
    (hU : IsPrefixPrependUniversal U) : IsSimulationUniversal U := by
  refine ⟨hU.1, fun M hM ↦ ?_⟩
  obtain ⟨s⟩ := hU.2 M hM
  exact ⟨s.tag.length, ⟨s.toProgramSimulation⟩⟩

/-- Prefix-prepend universality implies optimality for conditional prefix
complexity. This unlocks the coding theorem
(`aprioriMeasure_le_complexityWeight_optimal`) under the stronger hypothesis. -/
theorem IsPrefixPrependUniversal.isOptimalPrefixConditional {U : Map}
    (hU : IsPrefixPrependUniversal U) : IsOptimalPrefixConditional U :=
  hU.isSimulationUniversal.isOptimalPrefixConditional

/-! ### The concrete universal machine -/

/-- **The repository's universal prefix machine is prefix-prepend universal.**
Every prefix decompressor `M` is some `enumeratedPrefixMachine i`, and
`taggedUnion_produces_natCode` says precisely that prepending `natCode i`
reproduces `M`'s outputs on the tagged union. -/
theorem universalPrefixMachine_isPrefixPrependUniversal :
    IsPrefixPrependUniversal universalPrefixMachine := by
  refine ⟨universalPrefixMachine_isPrefixDecompressor, fun M hM ↦ ?_⟩
  obtain ⟨i, hi⟩ := exists_enumeratedPrefixMachine_eq hM
  refine ⟨⟨natCode i, fun p y x hp ↦ ?_⟩⟩
  have hp' : produces (enumeratedPrefixMachine i) p y x := by rw [hi]; exact hp
  exact taggedUnion_produces_natCode hp'

/-- There is a prefix-prepend universal machine. -/
theorem exists_isPrefixPrependUniversal : ∃ U : Map, IsPrefixPrependUniversal U :=
  ⟨universalPrefixMachine, universalPrefixMachine_isPrefixPrependUniversal⟩

end Kolmogorov
