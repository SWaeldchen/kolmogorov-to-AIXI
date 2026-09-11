/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.Chapter1Misc.Counting
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.Foundation.UnboundedSearch
import KolmogorovMathlib.DescriptionStatistics.MonotoneBound
import KolmogorovMathlib.DescriptionStatistics.Solovay
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import Mathlib.Computability.PartrecCode

/-!
# Gács Theorem 1.5.3 (Levin): when does a function bound `C` from above?

Let `F(x, y)` be upper semicomputable. Then

  `C(x | y) ≤⁺ F(x, y)`  for all `x, y`   **iff**   `log |{x : F(x, y) < m}| ≤⁺ m`  for all `y, m`.

So an upper semicomputable function dominates `C` exactly when its level sets are no
larger than those of `C` itself. It is the characterisation of `C` as the *least*
upper semicomputable function with small level sets.

## Definitions

* `UpperSemicomputable F`: the relation `F x y < m` is recursively enumerable, in the
  repository's sense `IsRE` (the domain of a partial recursive function). This is
  Gács' Definition 1.5.2 read for `−F`. Conditional complexity is an instance
  (`condK_upperSemicomputable`, from the repository's `condKLeIsRe`).
* The level-set condition is stated with `Set.encard`, so it includes finiteness:
  `{x | F x y < m}.encard ≤ 2 ^ (m + c)`.

## Proof

**`⇒`** is counting: if `C ≤ F + c` then `{F < m} ⊆ {C < m + c}`, and the latter has
fewer than `2^(m+c)` elements (`encard_condK_lt_le`).

**`⇐`** is the construction of a decompressor. Fix a code for the r.e. witness of
`F x y < m`. For a section `(y, m)` we enumerate its members in stages: at stage `s`,
the strings of length `≤ s` whose witness halts within fuel `s` (`discAt`); the
**discovery list** `discList` concatenates, stage by stage, the strings first seen at
that stage (`firstAt`). It is computable in `(y, m, s)`, grows by appending, has no
duplicates, and eventually lists every member of the section. Its length is therefore
at most the size of the section, `2^(m+c)`, so every member has a position `t` below
`2^(m+c)`, expressible in exactly `m + c` bits.

The decoder is handed the program `p` (those `m + c` bits) and the condition `y`. It
recovers `m` as `|p| − c` — **a program knows its own length**, the device of
Theorems 1.4.4, 1.4.5 and 1.7.1 — and `t` as the numeral `p` denotes, then searches for
the first stage at which the discovery list is longer than `t` and outputs the entry
at position `t`. Since the list only ever grows by appending, that entry is stable.
Taking `m = F(x, y) + 1` gives `C(x | y) ≤ F(x, y) + c + 1 + O(1)`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-! ### Upper semicomputability -/

/-- **Upper semicomputability**: the relation `F x y < m` is recursively enumerable.
This is Gács' Definition 1.5.2 applied to `−F`. -/
def UpperSemicomputable (F : BitString → BitString → ENat) : Prop :=
  IsRE (fun q : (BitString × BitString) × ℕ ↦ F q.1.1 q.1.2 < (q.2 : ENat))

/-- Conditional complexity is upper semicomputable (Gács Theorem 1.5.1, in this
form). From the repository's `condKLeIsRe`, shifting the bound by one. -/
theorem condK_upperSemicomputable (U : Map) (hU : isOptimalConditional U) :
    UpperSemicomputable (condK U) := by
  obtain ⟨f, hf, hdom⟩ := condKLeIsRe U hU
  -- Guard `m ≠ 0`, then ask the witness about `m - 1`.
  let guard : (BitString × BitString) × ℕ → Option Unit := fun q ↦
    if q.2 = 0 then none else some ()
  have hguard : Computable guard :=
    (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const none)
      (Primrec.const (some ()))).to_comp
  refine ⟨fun q ↦ (Part.ofOption (guard q)).bind (fun _ ↦ f (q.1.1, q.1.2, q.2 - 1)), ?_, ?_⟩
  · refine Partrec.bind (Computable.ofOption hguard) ?_
    exact (hf.comp (Computable.pair (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.pair (Computable.snd.comp (Computable.fst.comp Computable.fst))
        ((Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 1)).to_comp)))).to₂
  · rintro ⟨⟨x, y⟩, m⟩
    rw [Part.bind_dom]
    cases m with
    | zero =>
      have hno : ¬ (condK U x y < ((0 : ℕ) : ENat)) := by simp
      constructor
      · rintro ⟨h, _⟩
        exact absurd h (by simp [guard])
      · intro h
        exact absurd h hno
    | succ k =>
      have hg : guard ((x, y), k + 1) = some () := by simp [guard]
      have hlt : condK U x y < ((k + 1 : ℕ) : ENat) ↔ condK U x y ≤ (k : ENat) := by
        rw [Nat.cast_succ]; exact ENat.lt_add_one_iff (ENat.coe_ne_top k)
      change _ ↔ condK U x y < ((k + 1 : ℕ) : ENat)
      rw [hlt]
      constructor
      · rintro ⟨_, h⟩
        have := (hdom (x, y, k + 1 - 1)).mp h
        simpa using this
      · intro h
        refine ⟨by simp [hg], ?_⟩
        simpa using (hdom (x, y, k)).mpr h

/-! ### Direction `⇒`: a bound on `C` forces small level sets -/

/-- **Levin, `⇒`.** If `C(x | y) ≤ F(x, y) + c` for all `x, y`, then every level set
`{x | F x y < m}` has at most `2 ^ (m + c)` elements. No semicomputability is needed. -/
theorem encard_lt_le_of_condK_le (U : Map) (F : BitString → BitString → ENat) (c : ℕ)
    (h : ∀ x y, condK U x y ≤ F x y + (c : ENat)) (y : BitString) (m : ℕ) :
    {x | F x y < (m : ENat)}.encard ≤ 2 ^ (m + c) := by
  refine (Set.encard_le_encard ?_).trans (encard_condK_lt_le U y (m + c))
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  have hne : F x y ≠ ⊤ := ne_top_of_lt hx
  have hk : ((F x y).toNat : ENat) = F x y := ENat.coe_toNat hne
  have hkm : (F x y).toNat < m := by rw [← hk] at hx; exact_mod_cast hx
  calc condK U x y ≤ F x y + (c : ENat) := h x y
    _ = (((F x y).toNat + c : ℕ) : ENat) := by rw [← hk]; push_cast; rfl
    _ < ((m + c : ℕ) : ENat) := by exact_mod_cast (by omega : (F x y).toNat + c < m + c)

/-! ### Fuel-bounded halting of the r.e. witness -/

/-- Does the witness for `q` halt within fuel `k`? -/
def reHalts (c : Code) (k : ℕ) (q : (BitString × BitString) × ℕ) : Bool :=
  (Code.evaln k c (Encodable.encode q)).isSome

/-- The fuel check is primitive recursive. -/
theorem reHalts_primrec (c : Code) :
    Primrec (fun a : ℕ × ((BitString × BitString) × ℕ) ↦ reHalts c a.1 a.2) :=
  Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c))
      (Primrec.encode.comp Primrec.snd)))

/-- More fuel never hurts. -/
theorem reHalts_mono (c : Code) {k k' : ℕ} (h : k ≤ k') {q : (BitString × BitString) × ℕ}
    (hq : reHalts c k q = true) : reHalts c k' q = true := by
  unfold reHalts at hq ⊢
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hq
  have := Nat.Partrec.Code.evaln_mono h (Option.mem_def.mpr hv)
  rw [Option.mem_def.mp this]
  rfl

section Witness

variable {f : (BitString × BitString) × ℕ →. Unit} {c : Code}

/-- Fuel-bounded halting is genuine halting of the witness. -/
theorem reHalts_sound
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := (BitString × BitString) × ℕ) n)).bind
        (fun a ↦ Part.map Encodable.encode (f a)))
    {k : ℕ} {q : (BitString × BitString) × ℕ} (h : reHalts c k q = true) : (f q).Dom := by
  unfold reHalts at h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  have hev : v ∈ c.eval (Encodable.encode q) :=
    Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)
  rw [hc, Part.mem_bind_iff] at hev
  obtain ⟨a, ha, hva⟩ := hev
  rw [Part.mem_ofOption, Encodable.encodek] at ha
  have ha' := Option.some_inj.mp (Option.mem_def.mp ha)
  subst ha'
  obtain ⟨b, hb, _⟩ := (Part.mem_map_iff _).mp hva
  exact Part.dom_iff_mem.mpr ⟨b, hb⟩

/-- Genuine halting of the witness appears at some fuel. -/
theorem reHalts_complete
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := (BitString × BitString) × ℕ) n)).bind
        (fun a ↦ Part.map Encodable.encode (f a)))
    {q : (BitString × BitString) × ℕ} (h : (f q).Dom) : ∃ k, reHalts c k q = true := by
  obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp h
  have hmem : Encodable.encode u ∈ c.eval (Encodable.encode q) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨q, by simp [Encodable.encodek], Part.mem_map Encodable.encode hu⟩
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
  refine ⟨k, ?_⟩
  unfold reHalts
  rw [Option.mem_def.mp hk]
  rfl

end Witness

/-! ### The staged enumeration of a section

All functions below take one packed argument `((y, m), s)`: the condition `y`, the
level `m`, the stage `s`. This keeps the `Primrec` proofs to projections. -/

/-- **Discovered by stage `s`**: strings of length at most `s` whose witness for
`F x y < m` halts within fuel `s`. -/
def discAt (c : Code) (a : (BitString × ℕ) × ℕ) : List BitString :=
  (boundedPrograms a.2).filter (fun x ↦ reHalts c a.2 ((x, a.1.1), a.1.2))

/-- `discAt` is primitive recursive. -/
theorem discAt_primrec (c : Code) : Primrec (discAt c) := by
  refine list_filter_primrec (primrec_boundedPrograms.comp Primrec.snd) ?_
  exact ((reHalts_primrec c).comp (Primrec.pair (Primrec.snd.comp Primrec.fst)
    (Primrec.pair (Primrec.pair Primrec.snd (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))).to₂

/-- Membership in `discAt`. -/
theorem mem_discAt {c : Code} {y : BitString} {m s : ℕ} {x : BitString} :
    x ∈ discAt c ((y, m), s) ↔ x.length ≤ s ∧ reHalts c s ((x, y), m) = true := by
  unfold discAt
  rw [List.mem_filter, mem_boundedPrograms_iff]

/-- Discovery is monotone in the stage. -/
theorem discAt_mono (c : Code) {y : BitString} {m s s' : ℕ} (h : s ≤ s') {x : BitString}
    (hx : x ∈ discAt c ((y, m), s)) : x ∈ discAt c ((y, m), s') := by
  rw [mem_discAt] at hx ⊢
  exact ⟨hx.1.trans h, reHalts_mono c h hx.2⟩

/-- What was discovered by the previous stage (nothing, at stage `0`). -/
def prevDisc (c : Code) (a : (BitString × ℕ) × ℕ) : List BitString :=
  if a.2 = 0 then [] else discAt c (a.1, a.2 - 1)

/-- `prevDisc` is primitive recursive. -/
theorem prevDisc_primrec (c : Code) : Primrec (prevDisc c) :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const [])
    ((discAt_primrec c).comp (Primrec.pair Primrec.fst
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))))

/-- **First discovered at stage `s`**: discovered by `s` but not by `s − 1`. -/
def firstAt (c : Code) (a : (BitString × ℕ) × ℕ) : List BitString :=
  (discAt c a).filter (fun x ↦ !((prevDisc c a).any (fun z ↦ decide (z = x))))

/-- `firstAt` is primitive recursive. -/
theorem firstAt_primrec (c : Code) : Primrec (firstAt c) := by
  refine list_filter_primrec (discAt_primrec c) ?_
  exact (Primrec.not.comp (list_any_primrec
    (f := fun p : ((BitString × ℕ) × ℕ) × BitString ↦ prevDisc c p.1)
    (p := fun p z ↦ decide (z = p.2))
    ((prevDisc_primrec c).comp Primrec.fst)
    (bitStringEq_primrec.comp (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂)).to₂

/-- Membership in `firstAt`. -/
theorem mem_firstAt {c : Code} {y : BitString} {m s : ℕ} {x : BitString} :
    x ∈ firstAt c ((y, m), s) ↔
      x ∈ discAt c ((y, m), s) ∧ (s = 0 ∨ x ∉ discAt c ((y, m), s - 1)) := by
  unfold firstAt prevDisc
  rw [List.mem_filter]
  simp only
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases hs : s = 0
    · exact Or.inl hs
    · right
      rw [if_neg hs] at h2
      intro hx
      have : ((discAt c ((y, m), s - 1)).any fun z ↦ decide (z = x)) = true :=
        List.any_eq_true.mpr ⟨x, hx, by simp⟩
      simp [this] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_cases hs : s = 0
    · simp [hs]
    · rw [if_neg hs]
      rcases h2 with h0 | hx
      · exact absurd h0 hs
      · have hfalse : ((discAt c ((y, m), s - 1)).any fun z ↦ decide (z = x)) = false := by
          rw [List.any_eq_false]
          intro z hz hzx
          have : z = x := by simpa using hzx
          subst this
          exact hx hz
        simp [hfalse]

/-- **The discovery list** at stage `s`: everything first discovered at stages
`0, …, s`, in order of discovery. -/
def discList (c : Code) (a : (BitString × ℕ) × ℕ) : List BitString :=
  (List.range (a.2 + 1)).flatMap (fun j ↦ firstAt c (a.1, j))

/-- `discList` is primitive recursive. -/
theorem discList_primrec (c : Code) : Primrec (discList c) :=
  Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.snd))
    ((firstAt_primrec c).comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂

/-- The discovery list grows by appending. -/
theorem discList_succ (c : Code) (y : BitString) (m s : ℕ) :
    discList c ((y, m), s + 1) = discList c ((y, m), s) ++ firstAt c ((y, m), s + 1) := by
  unfold discList
  simp [List.range_succ]

/-- Earlier discovery lists are prefixes of later ones. -/
theorem discList_prefix (c : Code) (y : BitString) (m : ℕ) {s s' : ℕ} (h : s ≤ s') :
    discList c ((y, m), s) <+: discList c ((y, m), s') := by
  induction s', h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ s' _ ih => rw [discList_succ]; exact ih.trans (List.prefix_append _ _)

/-- Membership in the discovery list. -/
theorem mem_discList_iff {c : Code} {y : BitString} {m s : ℕ} {x : BitString} :
    x ∈ discList c ((y, m), s) ↔ ∃ j ≤ s, x ∈ firstAt c ((y, m), j) := by
  unfold discList
  simp only [List.mem_flatMap, List.mem_range, Nat.lt_succ_iff]

section Enumeration

variable {F : BitString → BitString → ENat} {f : (BitString × BitString) × ℕ →. Unit} {c : Code}

/-- Everything on the discovery list belongs to the section. -/
theorem discList_sound
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := (BitString × BitString) × ℕ) n)).bind
        (fun a ↦ Part.map Encodable.encode (f a)))
    (hdom : ∀ q, (f q).Dom ↔ F q.1.1 q.1.2 < (q.2 : ENat))
    {y : BitString} {m s : ℕ} {x : BitString} (hx : x ∈ discList c ((y, m), s)) :
    F x y < (m : ENat) := by
  obtain ⟨j, _, hj⟩ := mem_discList_iff.mp hx
  have h2 := (mem_discAt.mp (mem_firstAt.mp hj).1).2
  exact (hdom ((x, y), m)).mp (reHalts_sound hc h2)

/-- Everything in the section eventually appears on the discovery list. -/
theorem discList_complete
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := (BitString × BitString) × ℕ) n)).bind
        (fun a ↦ Part.map Encodable.encode (f a)))
    (hdom : ∀ q, (f q).Dom ↔ F q.1.1 q.1.2 < (q.2 : ENat))
    {y : BitString} {m : ℕ} {x : BitString} (hx : F x y < (m : ENat)) :
    ∃ s, x ∈ discList c ((y, m), s) := by
  classical
  obtain ⟨k, hk⟩ := reHalts_complete hc ((hdom ((x, y), m)).mpr hx)
  have hex : ∃ j, x ∈ discAt c ((y, m), j) :=
    ⟨max k x.length, mem_discAt.mpr ⟨le_max_right _ _, reHalts_mono c (le_max_left _ _) hk⟩⟩
  refine ⟨Nat.find hex, mem_discList_iff.mpr ⟨Nat.find hex, le_rfl, ?_⟩⟩
  rw [mem_firstAt]
  refine ⟨Nat.find_spec hex, ?_⟩
  by_cases h0 : Nat.find hex = 0
  · exact Or.inl h0
  · exact Or.inr (Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero h0) one_pos))

end Enumeration

/-- Each stage's new arrivals are listed without repetition. -/
theorem firstAt_nodup (c : Code) (a : (BitString × ℕ) × ℕ) : (firstAt c a).Nodup :=
  ((boundedPrograms_nodup _).filter _).filter _

/-- Different stages have disjoint new arrivals. -/
theorem firstAt_disjoint (c : Code) (y : BitString) (m : ℕ) {j j' : ℕ} (h : j < j') :
    List.Disjoint (firstAt c ((y, m), j)) (firstAt c ((y, m), j')) := by
  intro x hx hx'
  have h1 := (mem_firstAt.mp hx).1
  obtain ⟨_, h2⟩ := mem_firstAt.mp hx'
  rcases h2 with hj' | hnot
  · omega
  · exact hnot (discAt_mono c (by omega : j ≤ j' - 1) h1)

/-- The discovery list has no duplicates. -/
theorem discList_nodup (c : Code) (y : BitString) (m s : ℕ) : (discList c ((y, m), s)).Nodup := by
  unfold discList
  rw [List.nodup_flatMap]
  refine ⟨fun j _ ↦ firstAt_nodup c _, ?_⟩
  exact List.pairwise_lt_range.imp (fun h ↦ firstAt_disjoint c y m h)

/-- **The discovery list is no longer than the section.** -/
theorem discList_length_le {F : BitString → BitString → ENat}
    {f : (BitString × BitString) × ℕ →. Unit} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := (BitString × BitString) × ℕ) n)).bind
        (fun a ↦ Part.map Encodable.encode (f a)))
    (hdom : ∀ q, (f q).Dom ↔ F q.1.1 q.1.2 < (q.2 : ENat))
    (y : BitString) (m s : ℕ) :
    ((discList c ((y, m), s)).length : ℕ∞) ≤ {x | F x y < (m : ENat)}.encard := by
  have hnd := discList_nodup c y m s
  have hsub : (↑(discList c ((y, m), s)).toFinset : Set BitString) ⊆ {x | F x y < (m : ENat)} := by
    intro x hx
    rw [List.coe_toFinset] at hx
    exact discList_sound hc hdom hx
  calc ((discList c ((y, m), s)).length : ℕ∞)
      = ((discList c ((y, m), s)).toFinset.card : ℕ∞) := by
        rw [List.toFinset_card_of_nodup hnd]
    _ = (↑(discList c ((y, m), s)).toFinset : Set BitString).encard :=
        (Set.encard_coe_eq_coe_finsetCard _).symm
    _ ≤ _ := Set.encard_le_encard hsub

/-! ### The decoder -/

/-- **Levin's decoder.** Given `(p, y)`: read `m = |p| − cst` and `t = bitsToNat p`,
search for the first stage at which the discovery list of the section `(y, m)` has
more than `t` entries, and output entry `t`. -/
noncomputable def levinDecoder (c : Code) (cst : ℕ) : Map := fun pr ↦
  (Nat.rfind (fun s ↦ Part.some (decide (bitsToNat pr.1 <
      (discList c ((pr.2, pr.1.length - cst), s)).length)))).map
    (fun s ↦ (discList c ((pr.2, pr.1.length - cst), s)).getD (bitsToNat pr.1) [])

/-- The order on `ℕ`, as a `Bool`, is primitive recursive (with the standard
`Decidable` instance). -/
theorem natLt_primrec : Primrec (fun p : ℕ × ℕ ↦ decide (p.1 < p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.nat_lt : PrimrecRel ((· < ·) : ℕ → ℕ → Prop))
  exact Primrec.of_eq h (fun p ↦ by congr)

/-- The decoder is partial recursive. -/
theorem levinDecoder_isDecompressor (c : Code) (cst : ℕ) :
    isDecompressor (levinDecoder c cst) := by
  have hlistP : Primrec (fun q : (BitString × BitString) × ℕ ↦
      discList c ((q.1.2, q.1.1.length - cst), q.2)) :=
    (discList_primrec c).comp (Primrec.pair (Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.nat_sub.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.const cst))) Primrec.snd)
  have hidxP : Primrec (fun q : (BitString × BitString) × ℕ ↦ bitsToNat q.1.1) :=
    bitsToNat_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hp : Partrec₂ (fun (pr : BitString × BitString) (s : ℕ) ↦
      (Part.some (decide (bitsToNat pr.1 <
        (discList c ((pr.2, pr.1.length - cst), s)).length)) : Part Bool)) := by
    have : Computable (fun q : (BitString × BitString) × ℕ ↦
        decide (bitsToNat q.1.1 < (discList c ((q.1.2, q.1.1.length - cst), q.2)).length)) :=
      (natLt_primrec.comp (Primrec.pair hidxP (Primrec.list_length.comp hlistP))).to_comp
    exact this
  have hrfind : Partrec (fun pr : BitString × BitString ↦
      Nat.rfind (fun s ↦ (Part.some (decide (bitsToNat pr.1 <
        (discList c ((pr.2, pr.1.length - cst), s)).length)) : Part Bool))) :=
    (Partrec.rfind hp).of_eq (fun pr ↦ rfl)
  have hget : Computable₂ (fun (pr : BitString × BitString) (s : ℕ) ↦
      (discList c ((pr.2, pr.1.length - cst), s)).getD (bitsToNat pr.1) []) := by
    have : Computable (fun q : (BitString × BitString) × ℕ ↦
        (discList c ((q.1.2, q.1.1.length - cst), q.2)).getD (bitsToNat q.1.1) []) :=
      ((Primrec.list_getD ([] : BitString)).comp hlistP hidxP).to_comp
    exact this
  exact (hrfind.map hget).of_eq (fun pr ↦ rfl)

/-- **What the decoder outputs.** If `x` sits at position `t` of some discovery list
of the section `(y, m)`, and `p` is a string of length `m + cst` denoting `t`, then the
decoder outputs `x` on `(p, y)`. -/
theorem levinDecoder_produces (c : Code) (cst : ℕ) {p y x : BitString} {t m s₀ : ℕ}
    (hplen : p.length = m + cst) (hpval : bitsToNat p = t)
    (ht : t < (discList c ((y, m), s₀)).length)
    (htx : (discList c ((y, m), s₀))[t] = x) :
    produces (levinDecoder c cst) p y x := by
  classical
  have hm : p.length - cst = m := by omega
  have hex : ∃ s, t < (discList c ((y, m), s)).length := ⟨s₀, ht⟩
  have hspec : t < (discList c ((y, m), Nat.find hex)).length := Nat.find_spec hex
  -- The search returns the least good stage.
  have hmem : Nat.find hex ∈ Nat.rfind (fun s ↦ Part.some (decide (bitsToNat p <
      (discList c ((y, p.length - cst), s)).length))) := by
    rw [hm, hpval, Nat.mem_rfind]
    refine ⟨?_, fun {j} hj ↦ ?_⟩
    · rw [Part.mem_some_iff]; exact (decide_eq_true hspec).symm
    · rw [Part.mem_some_iff]; exact (decide_eq_false (Nat.find_min hex hj)).symm
  -- The entry at position `t` is `x`, whichever of the two stages is later.
  have hout : (discList c ((y, m), Nat.find hex)).getD t [] = x := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hspec, Option.getD_some, ← htx]
    rcases le_total (Nat.find hex) s₀ with h | h
    · exact (discList_prefix c y m h).getElem hspec
    · exact ((discList_prefix c y m h).getElem ht).symm
  change x ∈ Part.map _ (Nat.rfind _)
  rw [Part.mem_map_iff]
  refine ⟨Nat.find hex, hmem, ?_⟩
  simp only
  rw [hm, hpval]
  exact hout

/-! ### Direction `⇐` and the theorem -/

/-- **Levin, `⇐`.** If `F` is upper semicomputable and every level set
`{x | F x y < m}` has at most `2 ^ (m + cst)` elements, then `C(x | y) ≤⁺ F(x, y)`. -/
theorem condK_le_of_encard_lt_le (U : Map) (hU : isOptimalConditional U)
    (F : BitString → BitString → ENat) (hF : UpperSemicomputable F) (cst : ℕ)
    (hcount : ∀ (y : BitString) (m : ℕ), {x | F x y < (m : ENat)}.encard ≤ 2 ^ (m + cst)) :
    ∃ c : ℕ, ∀ x y, condK U x y ≤ F x y + (c : ENat) := by
  obtain ⟨f, hf, hdom⟩ := hF
  obtain ⟨code, hcode⟩ := Code.exists_code.mp hf
  obtain ⟨c₀, hc₀⟩ := hU.2 (levinDecoder code cst) (levinDecoder_isDecompressor code cst)
  refine ⟨c₀ + cst + 1, fun x y ↦ ?_⟩
  rcases eq_or_ne (F x y) ⊤ with htop | hne
  · rw [htop, top_add]; exact le_top
  -- `k = F x y`, and `x` lies in the section at level `m = k + 1`.
  have hk : ((F x y).toNat : ENat) = F x y := ENat.coe_toNat hne
  set k := (F x y).toNat with hkdef
  have hFlt : F x y < ((k + 1 : ℕ) : ENat) := by
    rw [← hk]; exact_mod_cast Nat.lt_succ_self k
  obtain ⟨s₀, hs₀⟩ := discList_complete (c := code) hcode hdom hFlt
  obtain ⟨t, ht, htx⟩ := List.mem_iff_getElem.mp hs₀
  -- Its position is below `2 ^ (k + 1 + cst)`.
  have htlt : t < 2 ^ (k + 1 + cst) := by
    have h1 : ((discList code ((y, k + 1), s₀)).length : ℕ∞) ≤ 2 ^ (k + 1 + cst) :=
      (discList_length_le hcode hdom y (k + 1) s₀).trans (hcount y (k + 1))
    have h2 : (discList code ((y, k + 1), s₀)).length ≤ 2 ^ (k + 1 + cst) := by
      have h1' : ((discList code ((y, k + 1), s₀)).length : ℕ∞)
          ≤ ((2 ^ (k + 1 + cst) : ℕ) : ℕ∞) := by push_cast; exact h1
      exact_mod_cast h1'
    omega
  -- The program: `t` in binary, padded to exactly `k + 1 + cst` bits.
  set p : BitString := Nat.bits t ++ List.replicate (k + 1 + cst - (Nat.bits t).length) false
    with hp
  have hbits : (Nat.bits t).length ≤ k + 1 + cst := by
    rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr htlt
  have hplen : p.length = k + 1 + cst := by
    rw [hp, List.length_append, List.length_replicate]; omega
  have hpval : bitsToNat p = t := by
    rw [hp, bitsToNat_append_replicate_false, bitsToNat_bits]
  have hprod : produces (levinDecoder code cst) p y x :=
    levinDecoder_produces code cst hplen hpval ht htx
  calc condK U x y ≤ condK (levinDecoder code cst) x y + (c₀ : ENat) := hc₀ x y
    _ ≤ (p.length : ENat) + (c₀ : ENat) := by
        gcongr
        rw [← KP_eq_condK]
        exact KP_le_programLength_of_produces hprod
    _ = F x y + ((c₀ + cst + 1 : ℕ) : ENat) := by
        rw [hplen, ← hk]; push_cast; ring

/-- **Gács Theorem 1.5.3 (Levin).** For an upper semicomputable `F`,
`C(x | y) ≤⁺ F(x, y)` holds for all `x, y` **iff** every level set `{x | F(x, y) < m}`
has at most `2^{m + O(1)}` elements. -/
theorem levin_characterization (U : Map) (hU : isOptimalConditional U)
    (F : BitString → BitString → ENat) (hF : UpperSemicomputable F) :
    (∃ c : ℕ, ∀ x y, condK U x y ≤ F x y + (c : ENat)) ↔
      (∃ c : ℕ, ∀ (y : BitString) (m : ℕ), {x | F x y < (m : ENat)}.encard ≤ 2 ^ (m + c)) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, encard_lt_le_of_condK_le U F c hc⟩
  · rintro ⟨c, hc⟩
    exact condK_le_of_encard_lt_le U hU F hF c hc

end Kolmogorov
