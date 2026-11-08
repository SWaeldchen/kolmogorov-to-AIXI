/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.SeqTest

/-!
# Prefix-free sums and level sums (combinatorics for §§2.3.6–2.3.8)

Elementary facts about finite sums over the binary tree, used by the Levin–Schnorr
theorem (`LevinSchnorr.lean`) and by Theorem 2.3.7 (`RandomnessViaM.lean`).

* `upTo n`: the strings of length at most `n`.
* `sum_le_levelMass_of_prefixFree`: for a measure, a finite prefix-free family of strings
  of length `≤ n` has total mass at most the level-`n` mass of the open set it generates
  (its cylinders are disjoint).
* `sum_le_of_prefixFree`: for a continuous semimeasure, a finite prefix-free family of
  extensions of `x` has total mass at most the mass of `x`.
* `sum_ext_take_mul`: a level-`m` sum of `g(z_{1:j}) μ(z)` regroups as a level-`j` sum of
  `g(y) μ(y)`.
* `tsum_levels_le`, `le_of_forall_levels`: the dyadic layer-cake inequalities
  `∑_{k : 2^{k+1} < t} 2^k ≤ t` and its converse `t ≤ 2 + 4b` when every level
  `2^{k+1} < t` gives `2^k ≤ b`.
-/

namespace Kolmogorov.Randomness

open scoped ENNReal

/-! ### Strings of bounded length -/

/-- The strings of length at most `n`. -/
def upTo (n : ℕ) : Finset BitString := (Finset.range (n + 1)).biUnion (ext [])

theorem mem_upTo {n : ℕ} {z : BitString} : z ∈ upTo n ↔ z.length ≤ n := by
  unfold upTo
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨j, hj, hz⟩
    rw [ext_zero_length j hz]; exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  · intro h
    exact ⟨z.length, Finset.mem_range.mpr (Nat.lt_succ_of_le h),
      mem_ext.mpr ⟨List.nil_prefix, by simp⟩⟩

theorem subset_upTo (s : Finset BitString) : s ⊆ upTo (s.sup List.length) := fun _ hz ↦
  mem_upTo.mpr (Finset.le_sup (f := List.length) hz)

/-! ### Prefix-free families -/

/-- Extensions of incomparable strings are disjoint. -/
theorem ext_disjoint_of_incomparable {x y : BitString} (hxy : ¬ x <+: y) (hyx : ¬ y <+: x)
    (m k : ℕ) : Disjoint (ext x m) (ext y k) := by
  rw [Finset.disjoint_left]
  intro z hzx hzy
  obtain ⟨hx, _⟩ := mem_ext.mp hzx
  obtain ⟨hy, _⟩ := mem_ext.mp hzy
  rcases le_total x.length y.length with h | h
  · exact hxy (List.prefix_of_prefix_length_le hx hy h)
  · exact hyx (List.prefix_of_prefix_length_le hy hx h)

/-- **Prefix-free mass bound for a measure.** -/
theorem sum_le_levelMass_of_prefixFree {μ : BitString → ℝ≥0∞} (hμ : IsSeqMeasure μ)
    (S : Finset BitString) (hpf : ∀ x ∈ S, ∀ y ∈ S, x <+: y → x = y) {n : ℕ}
    (hn : ∀ x ∈ S, x.length ≤ n) :
    ∑ x ∈ S, μ x ≤ levelMass μ (S : Set BitString) n := by
  classical
  calc ∑ x ∈ S, μ x = ∑ x ∈ S, ∑ z ∈ ext x (n - x.length), μ z :=
        Finset.sum_congr rfl fun x _ ↦ (sum_ext_eq hμ x _).symm
    _ = ∑ z ∈ S.biUnion (fun x ↦ ext x (n - x.length)), μ z := by
        rw [Finset.sum_biUnion]
        intro x hx y hy hne
        exact ext_disjoint_of_incomparable
          (fun h ↦ hne (hpf x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) h))
          (fun h ↦ hne (hpf y (Finset.mem_coe.mp hy) x (Finset.mem_coe.mp hx) h).symm) _ _
    _ ≤ levelMass μ (S : Set BitString) n := by
        unfold levelMass
        have hsub : S.biUnion (fun x ↦ ext x (n - x.length)) ⊆ ext [] n := by
          intro z hz
          obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
          obtain ⟨hxz, hl⟩ := mem_ext.mp hzx
          refine mem_ext.mpr ⟨List.nil_prefix, ?_⟩
          have := hn x hx
          simp only [List.length_nil, zero_add]
          omega
        refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ zero_le))
        refine Finset.sum_le_sum fun z hz ↦ ?_
        obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
        rw [if_pos ⟨x, Finset.mem_coe.mpr hx, (mem_ext.mp hzx).1⟩]

/-- A proper extension of `x` extends `x0` or `x1`. -/
theorem prefix_append_or_of_prefix {x y : BitString} (hxy : x <+: y) (hne : y ≠ x) :
    x ++ [false] <+: y ∨ x ++ [true] <+: y := by
  obtain ⟨t, rfl⟩ := hxy
  cases t with
  | nil => exact absurd (List.append_nil x) hne
  | cons b t' =>
    cases b
    · exact Or.inl ⟨t', by simp⟩
    · exact Or.inr ⟨t', by simp⟩

/-- **Prefix-free mass bound for a continuous semimeasure**, below a fixed node. -/
theorem sum_le_of_prefixFree {M : BitString → ℝ≥0∞}
    (hM : ∀ x, M (x ++ [false]) + M (x ++ [true]) ≤ M x) :
    ∀ (n : ℕ) (x : BitString) (S : Finset BitString),
      (∀ y ∈ S, ∀ z ∈ S, y <+: z → y = z) →
      (∀ y ∈ S, x <+: y ∧ y.length ≤ x.length + n) → ∑ y ∈ S, M y ≤ M x := by
  classical
  -- If every member of `S` equals `x`, the sum is at most `M x`.
  have hsingle : ∀ (x : BitString) (S : Finset BitString), (∀ y ∈ S, y = x) →
      ∑ y ∈ S, M y ≤ M x := fun x S h ↦ by
    calc ∑ y ∈ S, M y ≤ ∑ y ∈ ({x} : Finset BitString), M y :=
          Finset.sum_le_sum_of_subset (fun y hy ↦ Finset.mem_singleton.mpr (h y hy))
      _ = M x := Finset.sum_singleton _ _
  intro n
  induction n with
  | zero =>
    intro x S _ hS
    exact hsingle x S fun y hy ↦ ((hS y hy).1.eq_of_length
      (by have := (hS y hy).2; have := (hS y hy).1.length_le; omega)).symm
  | succ n ih =>
    intro x S hpf hS
    by_cases hx : x ∈ S
    · exact hsingle x S fun y hy ↦ (hpf x hx y hy (hS y hy).1).symm
    · set p : BitString → Prop := fun y ↦ x ++ [false] <+: y
      rw [← Finset.sum_filter_add_sum_filter_not S p]
      have hsub : ∀ T ⊆ S, ∀ y ∈ T, ∀ z ∈ T, y <+: z → y = z := fun T hT y hy z hz ↦
        hpf y (hT hy) z (hT hz)
      refine le_trans (add_le_add (ih (x ++ [false]) _ (hsub _ (Finset.filter_subset _ _)) ?_)
        (ih (x ++ [true]) _ (hsub _ (Finset.filter_subset _ _)) ?_)) (hM x)
      · intro y hy
        obtain ⟨hyS, hpy⟩ := Finset.mem_filter.mp hy
        refine ⟨hpy, ?_⟩
        have := (hS y hyS).2
        simp only [List.length_append, List.length_singleton]
        omega
      · intro y hy
        obtain ⟨hyS, hpy⟩ := Finset.mem_filter.mp hy
        have hne : y ≠ x := fun h ↦ hx (h ▸ hyS)
        refine ⟨(prefix_append_or_of_prefix (hS y hyS).1 hne).resolve_left hpy, ?_⟩
        have := (hS y hyS).2
        simp only [List.length_append, List.length_singleton]
        omega

/-- For a continuous semimeasure, a finite prefix-free family has total mass at most `1`. -/
theorem sum_le_one_of_prefixFree {M : BitString → ℝ≥0∞} (hM : IsContSemimeasure M)
    (S : Finset BitString) (hpf : ∀ y ∈ S, ∀ z ∈ S, y <+: z → y = z) :
    ∑ y ∈ S, M y ≤ 1 :=
  (sum_le_of_prefixFree hM.2 (S.sup List.length) [] S hpf fun y hy ↦
    ⟨List.nil_prefix, by simpa using Finset.le_sup (f := List.length) hy⟩).trans hM.1

/-! ### Regrouping a level sum by prefixes -/

/-- `∑_{z ∈ ext x m} g(z_{1:|x|+j}) μ(z) = ∑_{y ∈ ext x j} g(y) μ(y)` for `j ≤ m`. -/
theorem sum_ext_take_mul {μ : BitString → ℝ≥0∞} (hμ : IsSeqMeasure μ) (g : BitString → ℝ≥0∞) :
    ∀ (j : ℕ) (x : BitString) (m : ℕ), j ≤ m →
      ∑ z ∈ ext x m, g (z.take (x.length + j)) * μ z = ∑ y ∈ ext x j, g y * μ y := by
  intro j
  induction j with
  | zero =>
    intro x m _
    calc ∑ z ∈ ext x m, g (z.take (x.length + 0)) * μ z = ∑ z ∈ ext x m, g x * μ z := by
          refine Finset.sum_congr rfl fun z hz ↦ ?_
          rw [add_zero, ← List.prefix_iff_eq_take.mp (mem_ext.mp hz).1]
      _ = g x * μ x := by rw [← Finset.mul_sum, sum_ext_eq hμ]
      _ = ∑ y ∈ ext x 0, g y * μ y := by simp [ext]
  | succ j ih =>
    intro x m hjm
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hl : ∀ b : Bool, x.length + (j + 1) = (x ++ [b]).length + j := fun b ↦ by
      simp only [List.length_append, List.length_singleton]; omega
    simp only [ext]
    rw [Finset.sum_union (ext_disjoint x m'), Finset.sum_union (ext_disjoint x j), hl false,
      ih (x ++ [false]) m' (by omega), ← hl false, hl true, ih (x ++ [true]) m' (by omega)]

/-! ### Dyadic layer cake -/

/-- `∑_{k : 2^{k+1} < t} 2^k ≤ t`. -/
theorem tsum_levels_le (t : ℝ≥0∞) :
    ∑' k : ℕ, (if (2 : ℝ≥0∞) ^ (k + 1) < t then (2 : ℝ≥0∞) ^ k else 0) ≤ t := by
  refine ENNReal.tsum_le_of_sum_range_le fun N ↦ ?_
  -- Invariant: `S_N + 1 ≤ 2^N` and (`S_N = 0` or `S_N + 1 ≤ t`).
  have key : ∀ N : ℕ,
      (∑ k ∈ Finset.range N, (if (2 : ℝ≥0∞) ^ (k + 1) < t then (2 : ℝ≥0∞) ^ k else 0)) + 1
          ≤ 2 ^ N ∧
        ((∑ k ∈ Finset.range N,
            (if (2 : ℝ≥0∞) ^ (k + 1) < t then (2 : ℝ≥0∞) ^ k else 0)) = 0 ∨
          (∑ k ∈ Finset.range N,
            (if (2 : ℝ≥0∞) ^ (k + 1) < t then (2 : ℝ≥0∞) ^ k else 0)) + 1 ≤ t) := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [Finset.sum_range_succ]
      split_ifs with ht
      · have h3 : (∑ k ∈ Finset.range N,
            (if (2 : ℝ≥0∞) ^ (k + 1) < t then (2 : ℝ≥0∞) ^ k else 0)) + 2 ^ N + 1
              ≤ 2 ^ (N + 1) := by
          calc _ = (∑ k ∈ Finset.range N,
                (if (2 : ℝ≥0∞) ^ (k + 1) < t then (2 : ℝ≥0∞) ^ k else 0)) + 1 + 2 ^ N := by
                ring
            _ ≤ 2 ^ N + 2 ^ N := add_le_add h1 le_rfl
            _ = 2 ^ (N + 1) := by rw [pow_succ, mul_two]
        exact ⟨h3, Or.inr (h3.trans ht.le)⟩
      · rw [add_zero]
        exact ⟨h1.trans (pow_le_pow_right₀ one_le_two (Nat.le_succ N)), h2⟩
  obtain ⟨_, h2⟩ := key N
  rcases h2 with h | h
  · rw [h]; exact zero_le
  · exact le_self_add.trans h

/-- Converse layer cake: if every level `2^{k+1} < t` forces `2^k ≤ b`, then `t ≤ 2 + 4b`. -/
theorem le_of_forall_levels {t b : ℝ≥0∞}
    (h : ∀ k : ℕ, (2 : ℝ≥0∞) ^ (k + 1) < t → (2 : ℝ≥0∞) ^ k ≤ b) : t ≤ 2 + 4 * b := by
  by_contra hlt
  rw [not_le] at hlt
  have hb : b ≠ ⊤ := fun hb ↦ by simp [hb] at hlt
  by_cases ht : t = ⊤
  · refine hb (eq_top_of_forall_two_pow_le fun k ↦ h k ?_)
    rw [ht]; exact lt_top_iff_ne_top.mpr (two_pow_ne_top' _)
  · have hex : ∃ j : ℕ, t ≤ 2 ^ (j + 1) := by
      obtain ⟨K, hK⟩ := ENNReal.exists_nat_gt ht
      refine ⟨K, hK.le.trans ?_⟩
      have : (K : ℝ≥0∞) ≤ 2 ^ K := by exact_mod_cast (Nat.lt_two_pow_self (n := K)).le
      exact this.trans (pow_le_pow_right₀ one_le_two (Nat.le_succ K))
    classical
    set j := Nat.find hex with hj
    have hjt : t ≤ 2 ^ (j + 1) := Nat.find_spec hex
    have h2 : (2 : ℝ≥0∞) ≤ 2 + 4 * b := le_self_add
    rcases Nat.eq_zero_or_eq_succ_pred j with h0 | hs
    · rw [h0, zero_add, pow_one] at hjt
      exact absurd (hjt.trans h2) (not_le.mpr hlt)
    · set i := j.pred
      have hmin : ¬ t ≤ 2 ^ (i + 1) := Nat.find_min hex (by omega)
      have hib : (2 : ℝ≥0∞) ^ i ≤ b := h i (not_le.mp hmin)
      have : t ≤ 4 * b := by
        calc t ≤ 2 ^ (j + 1) := hjt
          _ = 4 * 2 ^ i := by rw [hs, show i.succ + 1 = i + 2 by omega, pow_add]; norm_num; ring
          _ ≤ 4 * b := mul_le_mul' le_rfl hib
      exact absurd (this.trans le_add_self) (not_le.mpr hlt)

end Kolmogorov.Randomness
