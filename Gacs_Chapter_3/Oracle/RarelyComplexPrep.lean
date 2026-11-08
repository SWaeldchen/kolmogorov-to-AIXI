/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Oracle.HaltingOracle
import Gacs_Chapter_3.Information.Identities

/-!
# Preparations for Gács Theorem 3.3.1

* `condMachine U`: `⟨x, q⟩ ↦ U(q, x)`, a prefix decompressor; with exact universality,
  `U(t ++ ⟨x, q⟩, []) = U(q, x)` for a fixed tag `t` (`exists_tag_cond`), so conditional halting is
  read off `χ`.
* `strEnum n`: an enumeration of all bit strings without repetition (`strEnum_injective`,
  `exists_strEnum_eq`), the order in which requests are issued.
* `find_eq_Kc`: the least `L` such that some program of length `≤ L` produces `y` from `z` is
  `K(y ∣ z)`.
-/

namespace Kolmogorov.Information.Oracle

open Kolmogorov.Information (Kc Ku KP_eq_Kc)
open Kolmogorov.Information.Halting (pairCode_prefix)

/-! ### Conditional computations as unconditional ones -/

/-- `⟨x, q⟩ ↦ U(q, x)` (and undefined off pair codes). -/
def condMachine (U : Map) : Map := fun pr ↦
  if pairCode (decodeFirst pr.1) (decodeSecond pr.1) = pr.1 then
    U (decodeSecond pr.1, decodeFirst pr.1)
  else Part.none

theorem condMachine_pairCode (U : Map) (x q y : BitString) :
    condMachine U (pairCode x q, y) = U (q, x) := by
  simp [condMachine, decodeFirst_pairCode, decodeSecond_pairCode]

theorem condMachine_isPrefixDecompressor {U : Map} (hU : IsPrefixDecompressor U) :
    IsPrefixDecompressor (condMachine U) := by
  refine ⟨?_, ?_⟩
  · have hpc : Computable (fun r : BitString ↦ pairCode (decodeFirst r) (decodeSecond r)) :=
      (pairCode_computable.comp (Computable.pair decodeFirst_computable
        decodeSecond_computable)).of_eq fun _ ↦ rfl
    have hdec := bitStringEq_primrec.to_comp.comp (Computable.pair
      (hpc.comp (Computable.fst (α := BitString) (β := BitString)))
      (Computable.fst (α := BitString) (β := BitString)))
    have hrun := hU.isDecompressor.comp (Computable.pair
      (decodeSecond_computable.comp (Computable.fst (α := BitString) (β := BitString)))
      (decodeFirst_computable.comp (Computable.fst (α := BitString) (β := BitString))))
    have h := Partrec.cond hdec hrun (Partrec.none (α := BitString × BitString) (σ := BitString))
    refine h.of_eq fun pr ↦ ?_
    by_cases hp : pairCode (decodeFirst pr.1) (decodeSecond pr.1) = pr.1 <;>
      simp [condMachine, hp]
  · intro y r hr r' hr' hpre
    have hvalid : ∀ {s : BitString}, (condMachine U (s, y)).Dom →
        pairCode (decodeFirst s) (decodeSecond s) = s ∧
          (U (decodeSecond s, decodeFirst s)).Dom := fun {s} hs ↦ by
      unfold condMachine at hs
      split_ifs at hs with hp
      · exact ⟨hp, hs⟩
      · exact absurd hs (by simp)
    obtain ⟨h1, d1⟩ := hvalid hr
    obtain ⟨h2, d2⟩ := hvalid hr'
    rw [← h1, ← h2] at hpre
    obtain ⟨hx, hq⟩ := pairCode_prefix hpre
    have hsec : decodeSecond r = decodeSecond r' :=
      hU.isPrefixMachine (decodeFirst r) d1 (by rw [hx]; exact d2) hq
    rw [← h1, ← h2, hx, hsec]

/-- **Conditional halting through the tag.** -/
theorem exists_tag_cond {U : Map} (hU : IsExactUniversal U) :
    ∃ t : BitString, ∀ x q, U (t ++ pairCode x q, []) = U (q, x) := by
  obtain ⟨t, ht⟩ := hU.2 _ (condMachine_isPrefixDecompressor hU.1)
  exact ⟨t, fun x q ↦ by rw [ht, condMachine_pairCode]⟩

/-! ### Enumerating all strings -/

theorem boundedPrograms_prefix {N N' : ℕ} (h : N ≤ N') :
    boundedPrograms N <+: boundedPrograms N' := by
  induction N' with
  | zero => obtain rfl : N = 0 := by omega
            exact List.prefix_rfl
  | succ N' ih =>
    rcases Nat.lt_or_ge N (N' + 1) with hlt | hge
    · rw [boundedPrograms_succ]
      exact (ih (by omega)).trans (List.prefix_append _ _)
    · obtain rfl : N = N' + 1 := by omega
      exact List.prefix_rfl

theorem lt_length_boundedPrograms (n : ℕ) : n < (boundedPrograms n).length := by
  have h := length_boundedPrograms_succ_eq n
  have : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  omega

/-- The `n`-th bit string in length-then-index order. -/
def strEnum (n : ℕ) : BitString := (boundedPrograms n).getD n []

theorem strEnum_eq_getElem {n N : ℕ} (h : n ≤ N) :
    strEnum n = (boundedPrograms N)[n]'(lt_of_lt_of_le (lt_length_boundedPrograms n)
      (boundedPrograms_prefix h).length_le) := by
  unfold strEnum
  rw [List.getD_eq_getElem _ _ (lt_length_boundedPrograms n)]
  exact (boundedPrograms_prefix h).getElem (lt_length_boundedPrograms n)

theorem strEnum_injective : Function.Injective strEnum := by
  intro n n' h
  rw [strEnum_eq_getElem (le_max_left n n'), strEnum_eq_getElem (le_max_right n n')] at h
  exact (List.Nodup.getElem_inj_iff (boundedPrograms_nodup _)).mp h

theorem exists_strEnum_eq (x : BitString) : ∃ n, strEnum n = x := by
  have hx : x ∈ boundedPrograms x.length := (mem_boundedPrograms_iff x _).mpr le_rfl
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hx
  refine ⟨i, ?_⟩
  rcases le_total i x.length with h | h
  · rw [strEnum_eq_getElem h, hget]
  · rw [strEnum_eq_getElem (le_refl i), ← hget]
    exact ((boundedPrograms_prefix h).getElem hi).symm

theorem strEnum_primrec : Primrec strEnum :=
  (Primrec.list_getD []).comp primrec_boundedPrograms Primrec.id

/-! ### Minimal lengths are complexities -/

theorem exists_short_program (hU : IsOptimalPrefixConditional U) (y z : BitString) :
    ∃ q : BitString, q.length ≤ Kc U y z ∧ y ∈ U (q, z) := by
  obtain ⟨p, hp, hlen⟩ := exists_program_of_KP_ne_top (KP_ne_top_of_optimal U hU y z)
  refine ⟨p, ?_, hp⟩
  rw [KP_eq_Kc hU] at hlen
  exact_mod_cast hlen.le

/-- The least `L` such that some program of length `≤ L` produces `y` from `z` is `K(y ∣ z)`. -/
theorem find_eq_Kc (hU : IsOptimalPrefixConditional U) (y z : BitString)
    (hex : ∃ L, ∃ q : BitString, q.length ≤ L ∧ y ∈ U (q, z))
    [DecidablePred fun L ↦ ∃ q : BitString, q.length ≤ L ∧ y ∈ U (q, z)] :
    Nat.find hex = Kc U y z := by
  apply le_antisymm
  · exact Nat.find_le (exists_short_program hU y z)
  · obtain ⟨q, hq, hmem⟩ := Nat.find_spec hex
    have h := KP_le_programLength_of_produces (M := U) (p := q) (x := y) (y := z) hmem
    rw [KP_eq_Kc hU] at h
    have : Kc U y z ≤ q.length := by exact_mod_cast h
    omega

end Kolmogorov.Information.Oracle
