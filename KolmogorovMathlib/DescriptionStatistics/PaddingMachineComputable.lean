/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.PaddingMachine
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.Prefix.OptimalExistence
import KolmogorovMathlib.Encoding.Tuples

/-!
# The padding core, computably

`PaddingMachine` defines the padding core `P_i = padBuilder U i` relationally.
This file shows it is partial recursive — uniformly in the index `i` — and hence
that Gács' machine `G = taggedUnion (padBuilder U)` is a genuine decompressor.

## The obstacle and its resolution

On input `w`, `P_i` must locate the unique prefix `v ⊑ w` on which `U` halts.
In the list-based `Map` model the whole of `w` is available at once, so `v` has
to be *found*: running `U` on the prefixes of `w` one at a time could hang on a
non-halting prefix, so the search must dovetail over pairs `(prefix length, fuel)`.

`Prefix/TwoStage` already solves exactly this. Its stage-one primitive
`twoStageS1 c w n` is "decode the output of the code `c` on `(w.take j, [])`
run with fuel `t`, where `(j, t) = n.unpair`", and `twoStageS1_computable` is
proved. We reuse both verbatim. Our search index `n` is then accepted when the
stage-one output `z` is a pair whose second component is the length target
`natCode (|w| + 2i + 1)`; the machine returns the first component.

## Structure

* `twoStageS1_sound` / `twoStageS1_complete` — the reused primitive against the
  relational `produces` predicate, through the code hypothesis `hc`.
* `padOut`, `padCheck`, `padMap` — the dovetailing implementation, indexed by a
  code `c` for `U` and the parameter `i`.
* `padOut_eq_some_iff` — the accepted outputs are exactly the pairs with the
  right second component.
* `padMap_mem_imp_spec`, `padMap_dom_of_spec`, `padBuilder_eq_padMap` — the
  implementation has the relational graph, for a prefix machine `U`.
* `padOut_computable`, `padCheck_computable`, `padMap_partrec_uniform` — the
  computability layer, in the argument `(i, w, y)` jointly.
* `taggedUnion_padBuilder_isDecompressor` — the result consumed by `LowerBound`.

The code hypothesis `hc` is stated in exactly the form `Code.exists_code`
produces from `isDecompressor U`, as in `twoStagePairBuilder_eq_twoStageMap`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-! ### The reused stage-one primitive against `produces` -/

/-- **Soundness of stage one.** If the reused primitive returns `z` at search
index `n`, then `U` produces `z` from the prefix `w.take n.unpair.1`. -/
theorem twoStageS1_sound {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {w z : BitString} {n : ℕ} (h : twoStageS1 c w n = some z) :
    produces U (w.take n.unpair.1) [] z := by
  unfold twoStageS1 at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨e, he, hdec⟩ := h
  have hev : e ∈ c.eval (Encodable.encode (w.take n.unpair.1, ([] : BitString))) :=
    Nat.Partrec.Code.evaln_sound he
  rw [hc, Part.mem_bind_iff] at hev
  obtain ⟨a, ha, hea⟩ := hev
  rw [Part.mem_ofOption, Encodable.encodek] at ha
  have ha' := Option.some_inj.mp (Option.mem_def.mp ha)
  subst ha'
  obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hea
  rw [Encodable.encodek] at hdec
  have hbz := Option.some_inj.mp hdec
  subst hbz
  exact hb

/-- **Completeness of stage one.** If `U` produces `z` from `v`, then for any
continuation `u` some fuel `t` makes the reused primitive return `z` at the
search index `⟨|v|, t⟩` on the input `v ++ u`. -/
theorem twoStageS1_complete {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {v u z : BitString} (hv : produces U v [] z) :
    ∃ t, twoStageS1 c (v ++ u) (Nat.pair v.length t) = some z := by
  have hmem : Encodable.encode z ∈ c.eval (Encodable.encode (v, ([] : BitString))) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨(v, ([] : BitString)), by simp [Encodable.encodek],
      Part.mem_map Encodable.encode hv⟩
  obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
  have ht' : Code.evaln t c (Encodable.encode (v, ([] : BitString)))
      = some (Encodable.encode z) := Option.mem_def.mp ht
  refine ⟨t, ?_⟩
  unfold twoStageS1
  simp only [Nat.unpair_pair, List.take_left, ht', Option.bind_some, Encodable.encodek]

/-! ### The dovetailing implementation -/

/-- The candidate output at search index `n`: run stage one on `w`; if the output
`z` is a pair whose second component is the length target `natCode (|w| + 2i + 1)`,
return its first component, otherwise reject. -/
def padOut (c : Code) (i : ℕ) (w : BitString) (n : ℕ) : Option BitString :=
  (twoStageS1 c w n).bind (fun z ↦
    bif decide (z = pairCode (decodeFirst z) (natCode (w.length + 2 * i + 1)))
      then some (decodeFirst z) else none)

/-- The dovetailing check: the search index `n` yields an accepted output. -/
def padCheck (c : Code) (i : ℕ) (w : BitString) (n : ℕ) : Bool :=
  (padOut c i w n).isSome

/-- The explicit computable padding core: search for the least accepted index and
return its output. The context argument is ignored. -/
def padMap (c : Code) (i : ℕ) : Map := fun pr ↦
  (Nat.rfind (fun n ↦ Part.some (padCheck c i pr.1 n))).bind
    (fun n ↦ (↑(padOut c i pr.1 n) : Part BitString))

/-- **Accepted outputs are exactly the correctly-shaped pairs.** `padOut` returns
`x` at index `n` iff stage one returns the pair of `x` with the length target. -/
theorem padOut_eq_some_iff {c : Code} {i : ℕ} {w : BitString} {n : ℕ} {x : BitString} :
    padOut c i w n = some x ↔
      twoStageS1 c w n = some (pairCode x (natCode (w.length + 2 * i + 1))) := by
  unfold padOut
  constructor
  · intro h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨z, hz, hbr⟩ := h
    by_cases hp : z = pairCode (decodeFirst z) (natCode (w.length + 2 * i + 1))
    · rw [Bool.cond_decide, if_pos hp, Option.some.injEq] at hbr
      rw [hbr] at hp
      rw [hz, hp]
    · rw [Bool.cond_decide, if_neg hp] at hbr
      simp at hbr
  · intro h
    rw [h]
    simp [decodeFirst_pairCode]

/-! ### The implementation has the relational graph -/

/-- **Soundness.** Whatever the implementation produces satisfies the padding
spec, for a code `c` of `U`. -/
theorem padMap_mem_imp_spec {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {i : ℕ} {w y x : BitString} (hx : x ∈ padMap c i (w, y)) : padSpec U i w x := by
  unfold padMap at hx
  rw [Part.mem_bind_iff] at hx
  obtain ⟨n, -, hn⟩ := hx
  rw [Part.mem_ofOption, Option.mem_def] at hn
  have hS1 := padOut_eq_some_iff.mp hn
  exact ⟨w.take n.unpair.1, w.drop n.unpair.1, (List.take_append_drop _ _).symm,
    twoStageS1_sound hc hS1⟩

/-- **Completeness.** Whenever the padding spec is satisfiable, the implementation
halts, for a code `c` of `U`. -/
theorem padMap_dom_of_spec {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {i : ℕ} {w y x : BitString} (hx : padSpec U i w x) : (padMap c i (w, y)).Dom := by
  obtain ⟨v, u, hw, hv⟩ := hx
  subst hw
  obtain ⟨t, ht⟩ := twoStageS1_complete (u := u) hc hv
  have hout : padOut c i (v ++ u) (Nat.pair v.length t) = some x :=
    padOut_eq_some_iff.mpr ht
  have hcheck : padCheck c i (v ++ u) (Nat.pair v.length t) = true := by
    unfold padCheck; rw [hout]; rfl
  -- The dovetailing search halts.
  have hrdom : (Nat.rfind (fun m ↦ Part.some (padCheck c i (v ++ u) m))).Dom := by
    rw [Nat.rfind_dom]
    exact ⟨Nat.pair v.length t, by rw [Part.mem_some_iff, hcheck],
      fun {m} _ ↦ Part.some_dom _⟩
  obtain ⟨n', hn'⟩ := Part.dom_iff_mem.mp hrdom
  -- At its witness the check passes, so an output exists.
  have hcheck' : padCheck c i (v ++ u) n' = true := by
    have h := (Nat.mem_rfind.mp hn').1
    rw [Part.mem_some_iff] at h
    exact h.symm
  unfold padCheck at hcheck'
  obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.mp hcheck'
  refine Part.dom_iff_mem.mpr ⟨x', ?_⟩
  unfold padMap
  rw [Part.mem_bind_iff]
  exact ⟨n', hn', by rw [Part.mem_ofOption]; exact Option.mem_def.mpr hx'⟩

/-- **The implementation equals the relational core**, for a code `c` of a prefix
machine `U`. -/
theorem padBuilder_eq_padMap {U : Map} (hU : IsPrefixMachine U) {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    (i : ℕ) : padBuilder U i = padMap c i := by
  funext pr
  obtain ⟨w, y⟩ := pr
  apply Part.ext
  intro x
  have hmem : x ∈ padBuilder U i (w, y) ↔ padSpec U i w x := mem_padBuilder_iff hU
  rw [hmem]
  constructor
  · intro hx
    have hdom := padMap_dom_of_spec (U := U) hc (y := y) hx
    obtain ⟨x', hx'⟩ := Part.dom_iff_mem.mp hdom
    have hspec' := padMap_mem_imp_spec (U := U) hc hx'
    have : x' = x := padSpec_unique hU hspec' hx
    rwa [this] at hx'
  · intro hx
    exact padMap_mem_imp_spec (U := U) hc hx

/-! ### Computability, uniformly in the index -/

/-- Decidable equality on `BitString` is computable. -/
theorem bitString_eq_computable :
    Computable (fun p : BitString × BitString ↦ decide (p.1 = p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.eq : PrimrecRel (@Eq BitString))
  exact Computable.of_eq h.to_comp (fun p ↦ by congr)

/-- The length target `|w| + 2i + 1` is primitive recursive in `(i, w)`, read off
the argument `((i, w, y), n)`. -/
theorem padTarget_primrec :
    Primrec (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString ↦
      r.1.1.2.1.length + 2 * r.1.1.1 + 1) := by
  have hi : Primrec (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString ↦ r.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hw : Primrec (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString ↦ r.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  exact Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.list_length.comp hw)
      (Primrec.nat_mul.comp (Primrec.const 2) hi))
    (Primrec.const 1)

/-- `padOut` is computable in `((i, w, y), n)` jointly. -/
theorem padOut_computable (c : Code) :
    Computable (fun q : (ℕ × BitString × BitString) × ℕ ↦ padOut c q.1.1 q.1.2.1 q.2) := by
  -- Stage one on `(w, n)`.
  have hS1 : Computable (fun q : (ℕ × BitString × BitString) × ℕ ↦ twoStageS1 c q.1.2.1 q.2) :=
    @Computable.comp ((ℕ × BitString × BitString) × ℕ) (BitString × ℕ) (Option BitString) _ _ _
      (fun p ↦ twoStageS1 c p.1 p.2) (fun q ↦ (q.1.2.1, q.2))
      (twoStageS1_computable c)
      (Computable.pair (Computable.fst.comp (Computable.snd.comp Computable.fst)) Computable.snd)
  -- The branch on the stage-one output `z = r.2`.
  have hz : Computable (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString ↦ r.2) :=
    Computable.snd
  have htarget : Computable (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString ↦
      natCode (r.1.1.2.1.length + 2 * r.1.1.1 + 1)) :=
    natCode_primrec.to_comp.comp padTarget_primrec.to_comp
  have hpair : Computable (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString ↦
      pairCode (decodeFirst r.2) (natCode (r.1.1.2.1.length + 2 * r.1.1.1 + 1))) :=
    pairCode_primrec.to_comp.comp (decodeFirst_computable.comp hz) htarget
  have hdec : Computable (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString ↦
      decide (r.2 = pairCode (decodeFirst r.2) (natCode (r.1.1.2.1.length + 2 * r.1.1.1 + 1)))) :=
    (bitString_eq_computable.comp (Computable.pair hz hpair)).of_eq (fun r ↦ rfl)
  have hsome : Computable (fun r : ((ℕ × BitString × BitString) × ℕ) × BitString ↦
      (some (decodeFirst r.2) : Option BitString)) :=
    Computable.option_some.comp (decodeFirst_computable.comp hz)
  have hbranch : Computable₂ (fun (q : (ℕ × BitString × BitString) × ℕ) (z : BitString) ↦
      bif decide (z = pairCode (decodeFirst z) (natCode (q.1.2.1.length + 2 * q.1.1 + 1)))
        then some (decodeFirst z) else none) :=
    Computable.cond hdec hsome (Computable.const none)
  exact (Computable.option_bind hS1 hbranch).of_eq (fun q ↦ rfl)

/-- `padCheck` is computable in `((i, w, y), n)` jointly. -/
theorem padCheck_computable (c : Code) :
    Computable (fun q : (ℕ × BitString × BitString) × ℕ ↦ padCheck c q.1.1 q.1.2.1 q.2) :=
  (Primrec.option_isSome.to_comp).comp (padOut_computable c)

/-- **The implementation is partial recursive, uniformly in `i`.** This is the
shape `taggedUnion_isDecompressor_of_uniform` consumes. -/
theorem padMap_partrec_uniform (c : Code) :
    Partrec (fun t : ℕ × BitString × BitString ↦ padMap c t.1 t.2) := by
  have hp : Partrec₂ (fun (t : ℕ × BitString × BitString) (n : ℕ) ↦
      (Part.some (padCheck c t.1 t.2.1 n) : Part Bool)) :=
    padCheck_computable c
  have hg : Partrec₂ (fun (t : ℕ × BitString × BitString) (n : ℕ) ↦
      (↑(padOut c t.1 t.2.1 n) : Part BitString)) :=
    Computable.ofOption (padOut_computable c)
  exact (Partrec.bind (Partrec.rfind hp) hg).of_eq (fun t ↦ rfl)

/-! ### The result for Gács' machine -/

/-- **Gács' machine `G = taggedUnion (padBuilder U)` is partial recursive**
whenever `U` is a prefix decompressor. Choose a code `c` for `U`; every core
`padBuilder U i` equals `padMap c i`; the family `padMap c` is uniformly partial
recursive; tagged unions of such families are partial recursive. -/
theorem taggedUnion_padBuilder_isDecompressor {U : Map} (hU : IsPrefixDecompressor U) :
    isDecompressor (taggedUnion (padBuilder U)) := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp hU.isDecompressor
  have heq : padBuilder U = padMap c :=
    funext (padBuilder_eq_padMap hU.isPrefixMachine hc)
  rw [heq]
  exact taggedUnion_isDecompressor_of_uniform (padMap_partrec_uniform c)

end Kolmogorov
