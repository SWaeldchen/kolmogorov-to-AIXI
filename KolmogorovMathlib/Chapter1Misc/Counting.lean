/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.PlainInformation.Subadditivity
import KolmogorovMathlib.Complexity.Incompressibility
import KolmogorovMathlib.Complexity.NatComplexity
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import Mathlib.Data.Set.Card

/-!
# Counting strings of bounded complexity, and Gács Corollary 1.3.7

There are fewer than `2^N` programs of length below `N`, and each produces at most one
output, so **fewer than `2^N` strings have `C(x | y) < N`**. This is the counting
argument behind Theorem 1.3.2(b), stated here for an arbitrary conditional complexity
and an arbitrary level, with cardinalities in `ℕ∞` (`Set.encard`) so that finiteness
is part of the conclusion rather than a hypothesis.

Two consequences follow at once.

* **Corollary 1.3.7**: `lim_{n → ∞} C(n) = ∞`. Only finitely many numbers have
  complexity below any given bound, because `Nat.bits` is injective.
* The `⇒` direction of Levin's Theorem 1.5.3 (`Levin.lean`): any function that
  dominates `C` from above has small level sets.
-/

namespace Kolmogorov

/-! ### Counting programs -/

/-- There are at most `2 ^ N` strings of length below `N`. -/
theorem encard_length_lt_le (N : ℕ) : {p : BitString | p.length < N}.encard ≤ 2 ^ N := by
  induction N with
  | zero =>
    have : {p : BitString | p.length < 0} = ∅ :=
      Set.eq_empty_of_forall_notMem (fun p hp ↦ by simp at hp)
    rw [this, Set.encard_empty]
    exact zero_le
  | succ N ih =>
    have hsplit : {p : BitString | p.length < N + 1}
        ⊆ {p | p.length < N} ∪ (↑(stringsOfLength N) : Set BitString) := by
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [Finset.mem_coe, memStringsOfLength]; exact h)
    have hlen : (↑(stringsOfLength N) : Set BitString).encard ≤ 2 ^ N := by
      rw [Set.encard_coe_eq_coe_finsetCard, cardStringsOfLength]
      push_cast
      exact le_rfl
    calc {p : BitString | p.length < N + 1}.encard
        ≤ ({p | p.length < N} ∪ (↑(stringsOfLength N) : Set BitString)).encard :=
          Set.encard_le_encard hsplit
      _ ≤ {p : BitString | p.length < N}.encard
            + (↑(stringsOfLength N) : Set BitString).encard := Set.encard_union_le _ _
      _ ≤ 2 ^ N + 2 ^ N := add_le_add ih hlen
      _ = 2 ^ (N + 1) := by ring

/-! ### Counting strings of bounded complexity -/

/-- **Fewer than `2^N` strings have `C(x | y) < N`.** Each such string has a program
of length below `N`, and distinct strings have distinct programs. -/
theorem encard_condK_lt_le (U : Map) (y : BitString) (N : ℕ) :
    {x : BitString | condK U x y < (N : ENat)}.encard ≤ 2 ^ N := by
  classical
  set S := {x : BitString | condK U x y < (N : ENat)} with hS
  have hprog : ∀ x ∈ S, ∃ p : BitString, produces U p y x ∧ p.length < N := by
    intro x hx
    have hne : condK U x y ≠ ⊤ := ne_top_of_lt hx
    obtain ⟨p, hp, hlen⟩ : ∃ p, produces U p y x ∧ (programLength p : ENat) = condK U x y :=
      KP_mem_candidateLengths_of_ne_top (M := U) (x := x) (y := y)
        (by rw [KP_eq_condK]; exact hne)
    refine ⟨p, hp, ?_⟩
    have h : (p.length : ENat) < (N : ENat) := by rw [hlen]; exact hx
    exact_mod_cast h
  choose! f hf using hprog
  have hinj : Set.InjOn f S := by
    intro x hx x' hx' heq
    have h1 := (hf x hx).1
    have h2 := (hf x' hx').1
    rw [heq] at h1
    exact Part.mem_unique h1 h2
  have himg : f '' S ⊆ {p : BitString | p.length < N} := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hf x hx).2
  calc S.encard = (f '' S).encard := hinj.encard_image.symm
    _ ≤ {p : BitString | p.length < N}.encard := Set.encard_le_encard himg
    _ ≤ 2 ^ N := encard_length_lt_le N

/-- The unconditional form: fewer than `2^N` strings have `C(x) < N`. -/
theorem encard_plainK_lt_le (U : Map) (N : ℕ) :
    {x : BitString | plainK U x < (N : ENat)}.encard ≤ 2 ^ N :=
  encard_condK_lt_le U [] N

/-- The level set `{x | C(x | y) < N}` is finite. -/
theorem finite_condK_lt (U : Map) (y : BitString) (N : ℕ) :
    {x : BitString | condK U x y < (N : ENat)}.Finite :=
  Set.finite_of_encard_le_coe (k := 2 ^ N) (by
    calc _ ≤ (2 : ℕ∞) ^ N := encard_condK_lt_le U y N
      _ = ((2 ^ N : ℕ) : ℕ∞) := by push_cast; rfl)

/-! ### Corollary 1.3.7 -/

/-- Only finitely many numbers have complexity at most `L`. -/
theorem finite_plainKNat_le (U : Map) (L : ℕ) :
    {n : ℕ | plainKNat U n ≤ (L : ENat)}.Finite := by
  have h1 := finite_condK_lt U [] (L + 1)
  have hinj : Function.Injective Nat.bits := Function.LeftInverse.injective bitsToNat_bits
  have h2 : {n : ℕ | plainKNat U n ≤ (L : ENat)}
      ⊆ Nat.bits ⁻¹' {x : BitString | condK U x [] < ((L + 1 : ℕ) : ENat)} := by
    intro n hn
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    have hn' : plainK U (Nat.bits n) ≤ (L : ENat) := hn
    calc condK U (Nat.bits n) [] = plainK U (Nat.bits n) := rfl
      _ ≤ (L : ENat) := hn'
      _ < ((L + 1 : ℕ) : ENat) := by exact_mod_cast Nat.lt_succ_self L
  exact (h1.preimage hinj.injOn).subset h2

/-- **Gács Corollary 1.3.7**, elementary form: for every bound `L` there is `N` beyond
which every number has complexity above `L`. -/
theorem plainKNat_eventually_gt (U : Map) (L : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, (L : ENat) < plainKNat U n := by
  obtain ⟨N, hN⟩ := (finite_plainKNat_le U L).bddAbove
  refine ⟨N + 1, fun n hn ↦ ?_⟩
  by_contra h
  have hmem : n ∈ {n : ℕ | plainKNat U n ≤ (L : ENat)} := not_lt.mp h
  have := hN hmem
  omega

/-- **Gács Corollary 1.3.7**, filter form: `C(n) → ∞`. Stated for the natural-number
value of the complexity, which exists because `C` is finite on an optimal machine. -/
theorem plainKNat_toNat_tendsto_atTop (U : Map) (hU : isOptimalConditional U) :
    Filter.Tendsto (fun n ↦ (plainKNat U n).toNat) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro L
  obtain ⟨N, hN⟩ := plainKNat_eventually_gt U L
  refine ⟨N, fun n hn ↦ ?_⟩
  have hlt := hN n hn
  have hfin : plainKNat U n ≠ ⊤ := plainK_ne_top U hU (Nat.bits n)
  rw [← ENat.coe_toNat hfin] at hlt
  exact_mod_cast hlt.le

end Kolmogorov
