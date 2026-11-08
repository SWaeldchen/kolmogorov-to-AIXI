/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Oracle.Defs
import Gacs_Chapter_3.Halting.RarelyComplex

/-!
# Reading complexities off finite prefixes of `χ`

Proof infrastructure for Gács Theorem 3.3.1. For a code `c` of `U`, a finite prefix `σ` of the
halting sequence `χ` decides, for every program `p` with `idx p < |σ|`, whether `U(p, [])` halts;
running the halting ones with fuel `|σ|` recovers their outputs.

* `knownOut c σ p`: `none` (not yet known), `some none` (`p` does not halt), `some (some v)`
  (`p` halts with encoded output `v`). It is **monotone** in `σ` (`knownOut_mono`), correct
  along `χ` (`knownOut_sound`, `knownOut_sound_none`), eventually defined along `χ`
  (`knownOut_eventually`), and primitive recursive.
* `minHit c σ w v B`: the least `L ≤ B` such that some program of length `≤ L`, wrapped by `w`,
  is known to output `v`. Under `allKnown` and along `χ` it is the true minimal length
  (`minHit_eq`). With `w = id` this computes `K(x)`; with `w q = tag ++ ⟨x, q⟩` (exact
  universality) it computes conditional complexities `K(· ∣ x)`.
-/

namespace Kolmogorov.Information.Oracle

open Kolmogorov.Information.Halting (IsCodeOf chi idx idx_injective idx_primrec countBelow
  countBelow_eq_card countBelow_primrec)
open Kolmogorov.Randomness (Seq seqTake length_seqTake)
open Nat.Partrec (Code)

/-! ### Prefixes of `χ` -/

/-- `σ` is an initial segment of `χ`. -/
def IsChiPrefix (U : Map) (σ : BitString) : Prop := ∀ i (h : i < σ.length), σ[i] = chi U i

theorem isChiPrefix_seqTake (U : Map) (m : ℕ) : IsChiPrefix U (seqTake (chi U) m) := by
  intro i h
  simp [seqTake, List.getElem_ofFn]

theorem chi_idx_iff (U : Map) (p : BitString) :
    chi U (idx p) = true ↔ p ∈ Halting.haltSet U := by
  classical
  unfold chi
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨q, hq, hqp⟩; rwa [← idx_injective hqp]
  · intro h; exact ⟨p, h, rfl⟩

/-! ### What a prefix of `χ` knows about a program -/

/-- `none`: unknown; `some none`: `p` does not halt; `some (some v)`: `p` outputs `v`. -/
def knownOut (c : Code) (σ p : BitString) : Option (Option ℕ) :=
  if idx p < σ.length then
    (if σ.getD (idx p) false then (Halting.runOut c σ.length p).map some else some none)
  else none

theorem knownOut_mono {c : Code} {σ τ p : BitString} {r : Option ℕ} (h : σ <+: τ)
    (hk : knownOut c σ p = some r) : knownOut c τ p = some r := by
  unfold knownOut at hk ⊢
  by_cases hlt : idx p < σ.length
  · have hlt' : idx p < τ.length := lt_of_lt_of_le hlt h.length_le
    have hget : τ.getD (idx p) false = σ.getD (idx p) false := by
      rw [List.getD_eq_getElem _ _ hlt', List.getD_eq_getElem _ _ hlt]
      exact (h.getElem hlt).symm
    rw [if_pos hlt] at hk
    rw [if_pos hlt', hget]
    split_ifs at hk ⊢ with hb
    · obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hk
      rw [Halting.runOut_mono h.length_le hv]; rfl
    · exact hk
  · rw [if_neg hlt] at hk; exact absurd hk (by simp)

section Along

variable {U : Map} {c : Code} {σ : BitString}

theorem knownOut_sound (hc : IsCodeOf U c) (_hσ : IsChiPrefix U σ) {p : BitString} {v : ℕ}
    (h : knownOut c σ p = some (some v)) : ∃ y, v = Encodable.encode y ∧ y ∈ U (p, []) := by
  unfold knownOut at h
  by_cases hlt : idx p < σ.length
  · rw [if_pos hlt] at h
    by_cases hb : σ.getD (idx p) false = true
    · rw [if_pos hb] at h
      obtain ⟨w, hw, hwv⟩ := Option.map_eq_some_iff.mp h
      cases hwv
      exact Halting.runOut_sound hc hw
    · rw [if_neg hb] at h; simp at h
  · rw [if_neg hlt] at h; simp at h

theorem knownOut_sound_none (hσ : IsChiPrefix U σ) {p : BitString}
    (h : knownOut c σ p = some none) : ¬ (U (p, [])).Dom := by
  unfold knownOut at h
  by_cases hlt : idx p < σ.length
  · rw [if_pos hlt] at h
    by_cases hb : σ.getD (idx p) false = true
    · rw [if_pos hb] at h
      obtain ⟨w, -, hwv⟩ := Option.map_eq_some_iff.mp h; cases hwv
    · intro hdom
      have hchi : chi U (idx p) = true := (chi_idx_iff U p).mpr hdom
      rw [List.getD_eq_getElem _ _ hlt, hσ _ hlt, hchi] at hb
      exact hb rfl
  · rw [if_neg hlt] at h; simp at h

/-- Along `χ`, every program is eventually known. -/
theorem knownOut_eventually (hc : IsCodeOf U c) (p : BitString) :
    ∃ m₀, ∀ m, m₀ ≤ m → (knownOut c (seqTake (chi U) m) p).isSome := by
  by_cases hp : p ∈ Halting.haltSet U
  · obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hp
    obtain ⟨t, ht⟩ := Halting.runOut_complete hc hx
    refine ⟨max (idx p + 1) t, fun m hm ↦ ?_⟩
    have hlt : idx p < (seqTake (chi U) m).length := by
      rw [length_seqTake]; have := le_max_left (idx p + 1) t; omega
    have hb : (seqTake (chi U) m).getD (idx p) false = true := by
      rw [List.getD_eq_getElem _ _ hlt, isChiPrefix_seqTake U m _ hlt]
      exact (chi_idx_iff U p).mpr hp
    have hrun : Halting.runOut c (seqTake (chi U) m).length p = some (Encodable.encode x) := by
      rw [length_seqTake]; exact Halting.runOut_mono (le_trans (le_max_right _ _) hm) ht
    unfold knownOut
    rw [if_pos hlt, if_pos hb, hrun]; rfl
  · refine ⟨idx p + 1, fun m hm ↦ ?_⟩
    have hlt : idx p < (seqTake (chi U) m).length := by rw [length_seqTake]; omega
    have hb : (seqTake (chi U) m).getD (idx p) false = false := by
      rw [List.getD_eq_getElem _ _ hlt, isChiPrefix_seqTake U m _ hlt]
      exact Bool.eq_false_iff.mpr fun h ↦ hp ((chi_idx_iff U p).mp h)
    unfold knownOut
    rw [if_pos hlt, if_neg (by rw [hb]; simp)]; rfl

/-- Along `χ`, finitely many programs are eventually all known. -/
theorem knownOut_eventually_list (hc : IsCodeOf U c) (ps : List BitString) :
    ∃ m₀, ∀ m, m₀ ≤ m → ∀ p ∈ ps, (knownOut c (seqTake (chi U) m) p).isSome := by
  induction ps with
  | nil => exact ⟨0, fun _ _ p hp ↦ absurd hp (by simp)⟩
  | cons p ps ih =>
    obtain ⟨m₁, h₁⟩ := knownOut_eventually hc p
    obtain ⟨m₂, h₂⟩ := ih
    refine ⟨max m₁ m₂, fun m hm q hq ↦ ?_⟩
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h₁ m (le_trans (le_max_left _ _) hm)
    · exact h₂ m (le_trans (le_max_right _ _) hm) q hq

end Along

theorem knownOut_primrec (c : Code) :
    Primrec (fun q : BitString × BitString ↦ knownOut c q.1 q.2) := by
  have hidx : Primrec (fun q : BitString × BitString ↦ idx q.2) := idx_primrec.comp Primrec.snd
  have hlen : Primrec (fun q : BitString × BitString ↦ q.1.length) :=
    Primrec.list_length.comp Primrec.fst
  have hget : Primrec (fun q : BitString × BitString ↦ q.1.getD (idx q.2) false) :=
    (Primrec.list_getD false).comp Primrec.fst hidx
  have hrun : Primrec (fun q : BitString × BitString ↦
      (Halting.runOut c q.1.length q.2).map some) :=
    Primrec.option_map ((Halting.runOut_primrec c).comp (Primrec.pair hlen Primrec.snd))
      (Primrec.option_some.comp Primrec.snd).to₂
  have hinner := Primrec.ite (Primrec.eq.comp hget (Primrec.const true))
    hrun (Primrec.const (some none))
  have h := Primrec.ite (Primrec.nat_lt.comp hidx hlen) hinner (Primrec.const none)
  refine h.of_eq fun q ↦ ?_
  unfold knownOut
  by_cases h1 : idx q.2 < q.1.length <;> by_cases h2 : q.1.getD (idx q.2) false = true <;>
    simp [h1]

/-! ### Minimal lengths -/

/-- Some program of length `≤ L`, wrapped by `w`, is known to output `v`. -/
def hitAt (c : Code) (σ : BitString) (w : BitString → BitString) (v L : ℕ) : Bool :=
  (boundedPrograms L).any (fun q ↦ decide (knownOut c σ (w q) = some (some v)))

/-- All wrapped programs of length `≤ B` are known. -/
def allKnown (c : Code) (σ : BitString) (w : BitString → BitString) (B : ℕ) : Bool :=
  !(boundedPrograms B).any (fun q ↦ !(knownOut c σ (w q)).isSome)

/-- The least `L ≤ B` with `hitAt` (or `B + 1` if none). -/
def minHit (c : Code) (σ : BitString) (w : BitString → BitString) (v B : ℕ) : ℕ :=
  countBelow (fun L ↦ !hitAt c σ w v L) (B + 1)

theorem allKnown_iff {c : Code} {σ : BitString} {w : BitString → BitString} {B : ℕ} :
    allKnown c σ w B = true ↔ ∀ q, q.length ≤ B → (knownOut c σ (w q)).isSome := by
  simp [allKnown, mem_boundedPrograms_iff, Option.isSome_iff_ne_none]

theorem hitAt_iff {c : Code} {σ : BitString} {w : BitString → BitString} {v L : ℕ} :
    hitAt c σ w v L = true ↔ ∃ q, q.length ≤ L ∧ knownOut c σ (w q) = some (some v) := by
  simp [hitAt, mem_boundedPrograms_iff]

/-- `countBelow (¬P) (B + 1)` is the least `L` with `P L`, for a monotone `P` holding at `B`. -/
theorem countBelow_not_eq_find {P : ℕ → Bool} {B : ℕ}
    (hmono : ∀ L L', L ≤ L' → P L = true → P L' = true) (hB : P B = true) :
    countBelow (fun L ↦ !P L) (B + 1) = Nat.find (⟨B, hB⟩ : ∃ L, P L = true) := by
  rw [countBelow_eq_card]
  have hset : (Finset.range (B + 1)).filter (fun L ↦ (!P L) = true) =
      Finset.range (Nat.find (⟨B, hB⟩ : ∃ L, P L = true)) := by
    ext L
    simp only [Finset.mem_filter, Finset.mem_range, Bool.not_eq_true']
    constructor
    · rintro ⟨-, hL⟩
      by_contra hge
      rw [not_lt] at hge
      have := hmono _ L hge (Nat.find_spec (⟨B, hB⟩ : ∃ L, P L = true))
      rw [this] at hL; exact absurd hL (by simp)
    · intro hL
      refine ⟨by have := Nat.find_le (h := (⟨B, hB⟩ : ∃ L, P L = true)) hB; omega, ?_⟩
      exact Bool.eq_false_iff.mpr (Nat.find_min (⟨B, hB⟩ : ∃ L, P L = true) hL)
  rw [hset, Finset.card_range]

/-- **`minHit` computes the minimal length**, along `χ`, once all candidates are known. -/
theorem minHit_eq {U : Map} {c : Code} (hc : IsCodeOf U c) {σ : BitString}
    (hσ : IsChiPrefix U σ) {w : BitString → BitString} {y : BitString} {B : ℕ}
    (hall : allKnown c σ w B = true) (hex : ∃ q, q.length ≤ B ∧ y ∈ U (w q, []))
    [DecidablePred fun L ↦ ∃ q : BitString, q.length ≤ L ∧ y ∈ U (w q, [])] :
    minHit c σ w (Encodable.encode y) B =
      Nat.find (⟨B, hex⟩ : ∃ L, ∃ q : BitString, q.length ≤ L ∧ y ∈ U (w q, [])) := by
  classical
  have hiff : ∀ L, L ≤ B → (hitAt c σ w (Encodable.encode y) L = true ↔
      ∃ q : BitString, q.length ≤ L ∧ y ∈ U (w q, [])) := by
    intro L hL
    rw [hitAt_iff]
    constructor
    · rintro ⟨q, hq, hk⟩
      obtain ⟨y', hy', hmem⟩ := knownOut_sound hc hσ hk
      rw [Encodable.encode_inj.mp hy'] ; exact ⟨q, hq, hmem⟩
    · rintro ⟨q, hq, hmem⟩
      refine ⟨q, hq, ?_⟩
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp
        ((allKnown_iff.mp hall) q (le_trans hq hL))
      cases r with
      | none => exact absurd (Part.dom_iff_mem.mpr ⟨y, hmem⟩) (knownOut_sound_none hσ hr)
      | some v =>
        obtain ⟨y', rfl, hmem'⟩ := knownOut_sound hc hσ hr
        rw [hr, Part.mem_unique hmem' hmem]
  have hB : hitAt c σ w (Encodable.encode y) B = true := (hiff B le_rfl).mpr hex
  have hmono : ∀ L L', L ≤ L' → hitAt c σ w (Encodable.encode y) L = true →
      hitAt c σ w (Encodable.encode y) L' = true := fun L L' h hL ↦ by
    rw [hitAt_iff] at hL ⊢
    obtain ⟨q, hq, hk⟩ := hL
    exact ⟨q, le_trans hq h, hk⟩
  unfold minHit
  rw [countBelow_not_eq_find hmono hB]
  set E : ∃ L, ∃ q : BitString, q.length ≤ L ∧ y ∈ U (w q, []) := ⟨B, hex⟩ with hE
  set F : ∃ L, hitAt c σ w (Encodable.encode y) L = true := ⟨B, hB⟩ with hF
  apply le_antisymm
  · apply Nat.find_le
    have hle : Nat.find E ≤ B := Nat.find_le (h := E) hex
    exact (hiff _ hle).mpr (Nat.find_spec E)
  · apply Nat.find_le
    have hle : Nat.find F ≤ B := Nat.find_le (h := F) hB
    exact (hiff _ hle).mp (Nat.find_spec F)

/-- `minHit` only depends on the values `knownOut` takes on the candidates. -/
theorem minHit_congr {c : Code} {σ τ : BitString} {w : BitString → BitString} {v B : ℕ}
    (h : ∀ q, q.length ≤ B → knownOut c σ (w q) = knownOut c τ (w q)) :
    minHit c σ w v B = minHit c τ w v B := by
  unfold minHit
  rw [countBelow_eq_card, countBelow_eq_card]
  congr 1
  refine Finset.filter_congr fun L hL ↦ ?_
  have hLB : L ≤ B := Nat.lt_succ_iff.mp (Finset.mem_range.mp hL)
  have : hitAt c σ w v L = hitAt c τ w v L := by
    rw [Bool.eq_iff_iff, hitAt_iff, hitAt_iff]
    constructor <;> rintro ⟨q, hq, hk⟩ <;> refine ⟨q, hq, ?_⟩
    · rw [← h q (le_trans hq hLB)]; exact hk
    · rw [h q (le_trans hq hLB)]; exact hk
  rw [this]

end Kolmogorov.Information.Oracle
