/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.AlgorithmicProbability.PairProjection

/-!
# The padding core `P_i`, relationally

The lower half of Gács' Theorem 1.7.1 manufactures many length-`n` programs for
`x` out of one short program `q` for the pair `⟨x, n⟩`, by appending arbitrary
padding. The machine that decodes such padded programs is the **padding core**
`P_i`, indexed by a natural number `i` that will later be set to the length of
its own universality tag.

On input `w`, `P_i` outputs `x` exactly when `w` splits as `v ++ u` where `v` is
a `U`-program for the pair `pairCode x (natCode (|w| + 2i + 1))`. Two features
carry the whole argument:

* the padding `u` is completely unconstrained — this is where the `2^ℓ` distinct
  programs come from;
* the pair's second component must equal `|w| + 2i + 1`, which is the total
  length the final `U`-program `tag ++ natCode i ++ w` will have. The program thus
  *states its own length*, and that is what makes `P_i`'s domain prefix-free
  (`padBuilder_isPrefixMachine`): two comparable halting inputs decode the same
  `v`, hence the same pair, hence the same length, hence are equal.

Following `Prefix/TwoStage`, the machine is defined here *relationally*, as the
`Part.mk` of its graph `padSpec`. Uniqueness of the output for a prefix machine
`U` (`padSpec_unique`) makes this a genuine partial function with
`produces (padBuilder U i) w y x ↔ padSpec U i w x`. Its partial recursiveness
is a separate matter, handled by a dovetailing implementation in
`PaddingMachineComputable`.
-/

namespace Kolmogorov

/-! ### The spec and the relational machine -/

/-- The graph of the padding core: `w = v ++ u` with `v` a `U`-program (empty
context) for the pair of `x` with the length code of `|w| + 2i + 1`. -/
def padSpec (U : Map) (i : ℕ) (w x : BitString) : Prop :=
  ∃ v u : BitString, w = v ++ u ∧
    produces U v [] (pairCode x (natCode (w.length + 2 * i + 1)))

/-- The **padding core** `P_i`: the noncomputable partial map with graph
`padSpec U i`. The context argument is ignored. -/
noncomputable def padBuilder (U : Map) (i : ℕ) : Map := fun pr ↦
  Part.mk (∃ x, padSpec U i pr.1 x) (fun h ↦ Classical.choose h)

/-- The padding core halts exactly when a padded parse exists. -/
theorem padBuilder_dom_iff (U : Map) (i : ℕ) (w y : BitString) :
    (padBuilder U i (w, y)).Dom ↔ ∃ x, padSpec U i w x :=
  Iff.rfl

/-! ### Uniqueness -/

/-- The sub-program `v` in a padded parse is a prefix of the input. -/
theorem padSpec_prefix {w v u : BitString} (hw : w = v ++ u) : v <+: w := by
  rw [hw]; exact List.prefix_append v u

/-- **The decoded sub-program is unique.** Two padded parses of the same input
`w` (possibly with different outputs and different length targets) use the same
`v`: both are prefixes of `w`, hence comparable, and both halt on the prefix
machine `U`. -/
theorem padSpec_sub_eq {U : Map} (hU : IsPrefixMachine U) {w v u v' u' : BitString}
    {z z' : BitString}
    (hw : w = v ++ u) (hv : produces U v [] z)
    (hw' : w = v' ++ u') (hv' : produces U v' [] z') : v = v' := by
  have h1 : v <+: w := padSpec_prefix hw
  have h2 : v' <+: w := padSpec_prefix hw'
  rcases List.prefix_or_prefix_of_prefix h1 h2 with hpre | hpre
  · exact hU.eq_of_prefix hv hv' hpre
  · exact (hU.eq_of_prefix hv' hv hpre).symm

/-- **Uniqueness of the output.** For a prefix machine `U`, the padding spec
determines `x`. -/
theorem padSpec_unique {U : Map} (hU : IsPrefixMachine U) {i : ℕ} {w x x' : BitString}
    (hx : padSpec U i w x) (hx' : padSpec U i w x') : x = x' := by
  obtain ⟨v, u, hw, hv⟩ := hx
  obtain ⟨v', u', hw', hv'⟩ := hx'
  have hvv : v = v' := padSpec_sub_eq hU hw hv hw' hv'
  subst hvv
  have hpair := Part.mem_unique hv hv'
  have := congrArg decodeFirst hpair
  rwa [decodeFirst_pairCode, decodeFirst_pairCode] at this

/-! ### Membership -/

/-- Any padded parse is produced by the relational padding core, given
prefix-freeness of `U`. -/
theorem padBuilder_produces_of_spec {U : Map} (hU : IsPrefixMachine U) {i : ℕ}
    {w y x : BitString} (hx : padSpec U i w x) :
    produces (padBuilder U i) w y x := by
  change x ∈ Part.mk (∃ x', padSpec U i w x') (fun h ↦ Classical.choose h)
  rw [Part.mem_mk_iff]
  refine ⟨⟨x, hx⟩, ?_⟩
  exact padSpec_unique hU (Classical.choose_spec ⟨x, hx⟩) hx

/-- Membership in the relational padding core is exactly the spec, given
prefix-freeness of `U`. -/
theorem mem_padBuilder_iff {U : Map} (hU : IsPrefixMachine U) {i : ℕ}
    {w y x : BitString} :
    produces (padBuilder U i) w y x ↔ padSpec U i w x := by
  constructor
  · intro h
    change x ∈ Part.mk (∃ x', padSpec U i w x') (fun h ↦ Classical.choose h) at h
    rw [Part.mem_mk_iff] at h
    obtain ⟨hex, hx⟩ := h
    rw [← hx]
    exact Classical.choose_spec hex
  · exact padBuilder_produces_of_spec hU

/-- The halting domain of the padding core does not depend on the context. -/
theorem domainAt_padBuilder (U : Map) (i : ℕ) (y : BitString) :
    domainAt (padBuilder U i) y = domainAt (padBuilder U i) [] := rfl

/-! ### Prefix-freeness -/

/-- **The padding core is a prefix machine** whenever `U` is. Two comparable
halting inputs `w ⊑ w'` decode the same sub-program `v` (both `v, v'` are
prefixes of `w'` halting on `U`), hence the same pair; the pair's second
component records `|w| + 2i + 1` resp. `|w'| + 2i + 1`, so the lengths agree and
a prefix of equal length is equal. -/
theorem padBuilder_isPrefixMachine {U : Map} (hU : IsPrefixMachine U) (i : ℕ) :
    IsPrefixMachine (padBuilder U i) := by
  intro y w hw w' hw' hpre
  obtain ⟨x, v, u, hweq, hv⟩ := (padBuilder_dom_iff U i w y).mp hw
  obtain ⟨x', v', u', hw'eq, hv'⟩ := (padBuilder_dom_iff U i w' y).mp hw'
  -- Both `v` and `v'` are prefixes of `w'` halting on `U`, hence equal.
  have h1 : v <+: w' := (padSpec_prefix hweq).trans hpre
  have h2 : v' <+: w' := padSpec_prefix hw'eq
  have hvv : v = v' := by
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · exact hU.eq_of_prefix hv hv' h
    · exact (hU.eq_of_prefix hv' hv h).symm
  subst hvv
  -- The same `U`-output records both length targets.
  have hpair := Part.mem_unique hv hv'
  have hsec := congrArg decodeSecond hpair
  rw [decodeSecond_pairCode, decodeSecond_pairCode] at hsec
  have hlen : w.length = w'.length := by
    have := natCode_injective hsec
    omega
  exact hpre.eq_of_length hlen

end Kolmogorov
