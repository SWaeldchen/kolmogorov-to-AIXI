/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.AlgorithmicProbability.Semimeasure
import KolmogorovMathlib.Complexity.Incompressibility

/-!
# Counting the length-`n` descriptions of a string

This module introduces Gács' counting function `f(x, n)` from *Lecture Notes on
Descriptional Complexity and Randomness* (arXiv:2105.04704), Theorem 1.7.1
(`thm:Hstat`): the number of binary programs of length **exactly** `n` that make
the machine `U` output `x` from the empty context.

The eventual target is the multiplicative form of that theorem,

  `2^{-n} · f(x, n) =× m(x, n)`,

which is the form Gács actually proves and which avoids logarithms,
`ℕ`-subtraction and every `⊤`/`-∞` edge case. This file supplies the two
elementary ingredients:

* `progCount U x n` — the count `f(x, n)` itself, as a natural number;
* `progSlice U x n` — the corresponding *slice* of a priori mass, namely the
  total weight `∑ 2^{-|p|}` carried by those same programs.

The only substantive lemma here is `progSlice_eq_progCount`, which says the two
agree up to the uniform factor `2^{-n}`. That is immediate — every program in the
slice has the *same* length `n`, so the sum is a constant times a cardinality —
but it is exactly the bridge that lets a counting statement be proved by
semimeasure arguments, and vice versa.

Nothing here mentions prefix-freeness, optimality, or the coding theorem: those
enter only when the slice is compared with `m(x, n)`.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The set of length-`n` descriptions -/

open Classical in
/-- The **length-`n` description set** of `x`: those programs of length exactly
`n` that produce `x` from the empty context on `U`.

Decidability of `produces` is supplied classically; the definition is therefore
`noncomputable`, which costs nothing since it is only ever used as an index set
for counting and summation. -/
noncomputable def progSet (U : Map) (x : BitString) (n : ℕ) : Finset BitString :=
  (stringsOfLength n).filter (fun p ↦ produces U p [] x)

/-- Membership in the description set, unfolded: a program belongs exactly when
it has length `n` and produces `x`. -/
theorem mem_progSet {U : Map} {x p : BitString} {n : ℕ} :
    p ∈ progSet U x n ↔ p.length = n ∧ produces U p [] x := by
  classical
  simp [progSet, Finset.mem_filter, memStringsOfLength]

/-- Every program in the description set has length `n`. -/
theorem length_of_mem_progSet {U : Map} {x p : BitString} {n : ℕ}
    (hp : p ∈ progSet U x n) : p.length = n :=
  (mem_progSet.mp hp).1

/-- Every program in the description set produces `x`. -/
theorem produces_of_mem_progSet {U : Map} {x p : BitString} {n : ℕ}
    (hp : p ∈ progSet U x n) : produces U p [] x :=
  (mem_progSet.mp hp).2

/-! ### The description count `f(x, n)` -/

/-- **The description count** `f(x, n)` of Gács' Theorem 1.7.1: the number of
programs of length exactly `n` that produce `x` from the empty context on `U`. -/
noncomputable def progCount (U : Map) (x : BitString) (n : ℕ) : ℕ :=
  (progSet U x n).card

/-- The count is at most `2^n`, since the description set sits inside the set of
all length-`n` strings. -/
theorem progCount_le_two_pow (U : Map) (x : BitString) (n : ℕ) :
    progCount U x n ≤ 2 ^ n := by
  classical
  have h : progSet U x n ⊆ stringsOfLength n := Finset.filter_subset _ _
  calc progCount U x n ≤ (stringsOfLength n).card := Finset.card_le_card h
    _ = 2 ^ n := cardStringsOfLength n

/-! ### The length-`n` slice of a priori mass -/

/-- **The length-`n` program slice**: the total a priori weight `∑ 2^{-|p|}`
carried by the length-`n` programs for `x`.

This is the quantity that the coding theorem can be applied to; `progSlice_eq_progCount`
identifies it with `2^{-n} · f(x, n)`. -/
noncomputable def progSlice (U : Map) (x : BitString) (n : ℕ) : ℝ≥0∞ :=
  ∑ p ∈ progSet U x n, progWeight p

/-- **The slice identity.** Every program in the slice has the same length `n`,
so its weight is the constant `2^{-n}` and the sum collapses to a multiple of the
cardinality:

  `progSlice U x n = 2^{-n} · progCount U x n`.

This is the bridge between the counting formulation of Theorem 1.7.1 and its
semimeasure formulation. -/
theorem progSlice_eq_progCount (U : Map) (x : BitString) (n : ℕ) :
    progSlice U x n = (2 : ℝ≥0∞)⁻¹ ^ n * (progCount U x n : ℝ≥0∞) := by
  classical
  have hconst : ∀ p ∈ progSet U x n, progWeight p = (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro p hp
    simp [progWeight, programLength, length_of_mem_progSet hp]
  rw [progSlice, Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul,
    progCount, mul_comm]

end Kolmogorov
