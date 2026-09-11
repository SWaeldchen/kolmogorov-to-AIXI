/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.Prefix.KraftConverse

/-!
# Gács Lemma 1.6.15: the Shannon–Fano code

Given positive weights `w₁, …, wₙ` with `∑ wⱼ ≤ 1`, there is a prefix code whose
`j`-th codeword has length about `−log wⱼ`.

The repository's converse Kraft inequality (`exists_prefixFree_code_of_kraft_le_one`)
produces a prefix code from any list of lengths with Kraft sum at most `1`. The
Shannon–Fano lemma is the choice of lengths: `lⱼ` = the least `l` with `2^{-l} ≤ wⱼ`,
so that `2^{-lⱼ} ≤ wⱼ < 2^{-(lⱼ - 1)}`. The Kraft sum is then at most `∑ wⱼ ≤ 1`, and
the codeword lengths satisfy the two-sided bound

  `2^{-|pⱼ|} ≤ wⱼ < 2 · 2^{-|pⱼ|}`,   i.e.   `−log wⱼ ≤ |pⱼ| < −log wⱼ + 1`.

This is one bit better than Gács' `+ 2`, because we do not insist that the codewords
be in lexicographic order; his interval construction pays one extra bit for that.

Two restrictions against the source: the family is **finite** (the repository's
converse Kraft inequality is finite), and the bound is stated **multiplicatively**,
without logarithms, as everywhere in this project.
-/

namespace Kolmogorov

/-! ### The Shannon–Fano length -/

/-- Some power of `1/2` lies below any positive real. -/
theorem exists_half_pow_le {w : ℝ} (hw : 0 < w) : ∃ l : ℕ, (1 / 2 : ℝ) ^ l ≤ w := by
  obtain ⟨l, hl⟩ := exists_pow_lt_of_lt_one hw (by norm_num : (1 / 2 : ℝ) < 1)
  exact ⟨l, hl.le⟩

/-- The **Shannon–Fano length** of a positive weight: the least `l` with `2^{-l} ≤ w`. -/
noncomputable def sfLength {w : ℝ} (hw : 0 < w) : ℕ := Nat.find (exists_half_pow_le hw)

/-- `2^{-sfLength w} ≤ w`. -/
theorem half_pow_sfLength_le {w : ℝ} (hw : 0 < w) : (1 / 2 : ℝ) ^ sfLength hw ≤ w :=
  Nat.find_spec (exists_half_pow_le hw)

/-- `w < 2 · 2^{-sfLength w}`, for weights at most `1`. -/
theorem lt_two_mul_half_pow_sfLength {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    w < 2 * (1 / 2 : ℝ) ^ sfLength hw := by
  rcases Nat.eq_zero_or_pos (sfLength hw) with h0 | hpos
  · rw [h0, pow_zero, mul_one]; linarith
  · obtain ⟨m, hm⟩ : ∃ m, sfLength hw = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
    have hlt : m < sfLength hw := by omega
    have hmin : ¬ (1 / 2 : ℝ) ^ m ≤ w := Nat.find_min (exists_half_pow_le hw) hlt
    rw [hm, pow_succ]
    linarith [not_le.mp hmin]

/-! ### Lemma 1.6.15 -/

/-- **Gács Lemma 1.6.15 (Shannon–Fano code).** For positive weights `w : Fin n → ℝ`
with `∑ wⱼ ≤ 1` there is an injective prefix code `p : Fin n → BitString` with
`2^{-|pⱼ|} ≤ wⱼ < 2 · 2^{-|pⱼ|}` for every `j`. -/
theorem exists_shannonFano_code {n : ℕ} (w : Fin n → ℝ) (hpos : ∀ j, 0 < w j)
    (hsum : ∑ j, w j ≤ 1) :
    ∃ p : Fin n → BitString, Function.Injective p ∧ IsPrefixFree (Set.range p) ∧
      ∀ j, (1 / 2 : ℝ) ^ (p j).length ≤ w j ∧ w j < 2 * (1 / 2 : ℝ) ^ (p j).length := by
  -- Each weight is at most one.
  have hle1 : ∀ j, w j ≤ 1 := fun j ↦
    (Finset.single_le_sum (fun i _ ↦ (hpos i).le) (Finset.mem_univ j)).trans hsum
  -- The Shannon–Fano lengths and their Kraft sum.
  have hK : ((List.ofFn (fun j ↦ sfLength (hpos j))).map (fun l ↦ (1 / 2 : ℝ) ^ l)).sum
      ≤ 1 := by
    rw [List.map_ofFn, List.sum_ofFn]
    calc ∑ j, (1 / 2 : ℝ) ^ sfLength (hpos j)
        ≤ ∑ j, w j := Finset.sum_le_sum (fun j _ ↦ half_pow_sfLength_le (hpos j))
      _ ≤ 1 := hsum
  obtain ⟨f, hflen, hfinj, hfpre⟩ := exists_prefixFree_code_of_kraft_le_one _ hK
  have hlen : (List.ofFn (fun j ↦ sfLength (hpos j))).length = n := List.length_ofFn
  -- Re-index the code by `Fin n`.
  refine ⟨fun j ↦ f (Fin.cast hlen.symm j), ?_, ?_, fun j ↦ ?_⟩
  · intro j j' h
    have := hfinj h
    simpa using this
  · refine IsPrefixFree.mono hfpre ?_
    rintro _ ⟨j, rfl⟩
    exact ⟨_, rfl⟩
  · have hj : (f (Fin.cast hlen.symm j)).length = sfLength (hpos j) := by
      rw [hflen, List.get_ofFn]
      simp
    rw [hj]
    exact ⟨half_pow_sfLength_le (hpos j), lt_two_mul_half_pow_sfLength (hpos j) (hle1 j)⟩

end Kolmogorov
