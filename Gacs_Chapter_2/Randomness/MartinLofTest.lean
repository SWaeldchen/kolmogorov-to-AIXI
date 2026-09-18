/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.LowerSemicomputable

/-!
# Gács §2.1: Martin-Löf tests for the uniform distribution

A **Martin-Löf test** (Definition 2.1.2) is a lower semicomputable `d` with

  `|{x ∈ B^n : d(x) > k}| ≤ 2^{n-k}`   for all `n, k`  (2.1.1),

and **Theorem 2.1.1** (Martin-Löf) says `d₀(x) = |x| − C(x | |x|)` is a universal one:
it is a test, and every test `d` satisfies `d ≤⁺ d₀`.

## Multiplicative form

A test is carried as `t = 2^d : BitString → ℝ≥0∞`. Condition (2.1.1) becomes

  `|{x ∈ B^n : 2^k < t x}| · 2^k ≤ 2^n`,

universality becomes `t x ≤ 2^c · t₀ x`, and `d₀` becomes

  `mlDeficiency U x = 2^{|x|} · 2^{-C(x | |x|)}`,

the length encoded as `Nat.bits x.length` in the condition, as elsewhere in the
repository. No logarithm appears.

## Proof

*Test property.* Lower semicomputability of `t₀` comes from upper semicomputability
of `C` through `isLSC₁_complexityWeight_of_isRE`. The count is
`{x ∈ B^n : 2^k < t₀ x} = {x ∈ B^n : C(x | n) < n − k}`, which has fewer than `2^{n-k}`
elements (`encard_condK_lt_le`).

*Universality.* This is Gács' argument verbatim: given a test `t`, define
`F(x, y) = |x| − d(x)` when `y = |x|` and `∞` otherwise, check that `F` is upper
semicomputable and has small level sets, and apply Levin's Theorem 1.5.3
(`condK_le_of_encard_lt_le`) to get `C(x | |x|) ≤⁺ |x| − d(x)`. In multiplicative
form `F(x, |x|)` is the least `m` with `2^{|x|} < 2^m · t x`, a ceiling of `|x| − d(x)`,
and minimality gives `2^F · t x ≤ 2^{|x|+1}`, which is the one-bit slack in the
constant.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Definitions -/

open Classical in
/-- **Martin-Löf test for the uniform distribution**, multiplicative form: lower
semicomputable, with at most `2^{n-k}` strings of length `n` exceeding `2^k`. -/
def IsMLTestUniform (t : BitString → ℝ≥0∞) : Prop :=
  IsLSC₁ t ∧ ∀ n k : ℕ,
    ((stringsOfLength n).filter (fun x ↦ (2 : ℝ≥0∞) ^ k < t x)).card * 2 ^ k ≤ 2 ^ n

/-- A **universal** ML-test dominates every ML-test up to a multiplicative constant. -/
def IsUniversalMLTestUniform (t₀ : BitString → ℝ≥0∞) : Prop :=
  IsMLTestUniform t₀ ∧ ∀ t, IsMLTestUniform t → ∃ c : ℕ, ∀ x, t x ≤ 2 ^ c * t₀ x

/-- **Gács' `d₀`**, Definition 2.1.3, in multiplicative form:
`2^{|x|} · 2^{-C(x | |x|)}`. -/
noncomputable def mlDeficiency (U : Map) (x : BitString) : ℝ≥0∞ :=
  2 ^ x.length * complexityWeight (condK U x (Nat.bits x.length))

/-! ### Arithmetic of powers of two in `ℝ≥0∞` -/

theorem two_pow_mul_inv_two_pow_of_le {n c : ℕ} (h : c ≤ n) :
    (2 : ℝ≥0∞) ^ n * 2⁻¹ ^ c = 2 ^ (n - c) := by
  have : (2 : ℝ≥0∞) ^ n = 2 ^ (n - c) * 2 ^ c := by rw [← pow_add]; congr 1; omega
  rw [this, mul_assoc, ← ENNReal.inv_pow,
    ENNReal.mul_inv_cancel (two_pow_ne_zero' c) (two_pow_ne_top' c), mul_one]

theorem two_pow_mul_inv_two_pow_le_one {n c : ℕ} (h : n ≤ c) :
    (2 : ℝ≥0∞) ^ n * 2⁻¹ ^ c ≤ 1 := by
  have : (2 : ℝ≥0∞)⁻¹ ^ c = 2⁻¹ ^ (c - n) * 2⁻¹ ^ n := by rw [← pow_add]; congr 1; omega
  rw [this, mul_comm, mul_assoc,
    show (2 : ℝ≥0∞)⁻¹ ^ n = ((2 : ℝ≥0∞) ^ n)⁻¹ from ENNReal.inv_pow.symm,
    ENNReal.inv_mul_cancel (two_pow_ne_zero' n) (two_pow_ne_top' n), mul_one]
  exact pow_le_one₀ (zero_le) (ENNReal.inv_le_one.mpr one_le_two)

theorem two_pow_lt_two_pow_iff' (a b : ℕ) : (2 : ℝ≥0∞) ^ a < 2 ^ b ↔ a < b := by
  rw [show (2 : ℝ≥0∞) ^ a = ((2 ^ a : ℕ) : ℝ≥0∞) by push_cast; rfl,
    show (2 : ℝ≥0∞) ^ b = ((2 ^ b : ℕ) : ℝ≥0∞) by push_cast; rfl, Nat.cast_lt]
  exact Nat.pow_lt_pow_iff_right (by norm_num)

/-- `2^k < 2^n · 2^{-C}` iff `C < n − k`, for strings of length `n` and `k ≤ n`. -/
theorem two_pow_lt_mlDeficiency_iff (U : Map) {x : BitString} {n k : ℕ} (hx : x.length = n)
    (hk : k ≤ n) :
    (2 : ℝ≥0∞) ^ k < mlDeficiency U x ↔ condK U x (Nat.bits n) < ((n - k : ℕ) : ENat) := by
  unfold mlDeficiency
  rw [hx]
  rcases eq_or_ne (condK U x (Nat.bits n)) ⊤ with htop | hne
  · rw [htop, complexityWeight_top, mul_zero]; simp
  · lift condK U x (Nat.bits n) to ℕ using hne with c hc
    rw [complexityWeight_coe, Nat.cast_lt]
    rcases le_or_gt c n with hcn | hcn
    · rw [two_pow_mul_inv_two_pow_of_le hcn, two_pow_lt_two_pow_iff']; omega
    · have h1 := two_pow_mul_inv_two_pow_le_one hcn.le
      constructor
      · intro h
        exact absurd (h.trans_le h1) (not_lt.mpr (one_le_pow₀ one_le_two))
      · intro h; omega

/-! ### Theorem 2.1.1, first half: `d₀` is a Martin-Löf test -/

/-- **`d₀` is a Martin-Löf test.** -/
theorem mlDeficiency_isMLTestUniform (U : Map) (hU : isOptimalConditional U) :
    IsMLTestUniform (mlDeficiency U) := by
  classical
  refine ⟨?_, fun n k ↦ ?_⟩
  · -- Lower semicomputable, from upper semicomputability of `C`.
    have hRE : IsRE (fun q : BitString × ℕ ↦
        condK U q.1 (Nat.bits q.1.length) ≤ (q.2 : ENat)) :=
      (condKLeIsRe U hU).comp
        (g := fun q : BitString × ℕ ↦ (q.1, Nat.bits q.1.length, q.2))
        (Computable.pair Computable.fst (Computable.pair
          (natBitsComputable.comp (Computable.list_length.comp Computable.fst)) Computable.snd))
    have h := (isLSC₁_complexityWeight_of_isRE (fun x ↦ condK U x (Nat.bits x.length))
      hRE).mul_natCast_left
      (g := fun x ↦ 2 ^ x.length)
      (natPow_primrec.to_comp.comp (Computable.const 2) Computable.list_length)
    exact h.congr (fun x ↦ by rw [mlDeficiency]; push_cast; ring)
  · rcases le_or_gt k n with hk | hk
    · -- The exceeding strings are those with `C(x | n) < n − k`.
      have hsub : (↑((stringsOfLength n).filter (fun x ↦ (2 : ℝ≥0∞) ^ k < mlDeficiency U x))
          : Set BitString) ⊆ {x | condK U x (Nat.bits n) < ((n - k : ℕ) : ENat)} := by
        intro x hx
        rw [Finset.mem_coe, Finset.mem_filter, memStringsOfLength] at hx
        exact (two_pow_lt_mlDeficiency_iff U hx.1 hk).mp hx.2
      have hcard : ((stringsOfLength n).filter
          (fun x ↦ (2 : ℝ≥0∞) ^ k < mlDeficiency U x)).card ≤ 2 ^ (n - k) := by
        have h1 := (Set.encard_le_encard hsub).trans (encard_condK_lt_le U (Nat.bits n) (n - k))
        rw [Set.encard_coe_eq_coe_finsetCard] at h1
        have h2 : (((stringsOfLength n).filter
            (fun x ↦ (2 : ℝ≥0∞) ^ k < mlDeficiency U x)).card : ℕ∞)
            ≤ ((2 ^ (n - k) : ℕ) : ℕ∞) := by push_cast; exact h1
        exact_mod_cast h2
      calc _ ≤ 2 ^ (n - k) * 2 ^ k := Nat.mul_le_mul_right _ hcard
        _ = 2 ^ n := by rw [← pow_add]; congr 1; omega
    · -- No string of length `n` has `t₀ x > 2^k` when `k > n`.
      have hempty : (stringsOfLength n).filter (fun x ↦ (2 : ℝ≥0∞) ^ k < mlDeficiency U x) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro x hx
        rw [memStringsOfLength] at hx
        rw [not_lt]
        unfold mlDeficiency; rw [hx]
        calc 2 ^ n * complexityWeight (condK U x (Nat.bits n)) ≤ 2 ^ n * 1 := by
              gcongr; exact complexityWeight_le_one _
          _ ≤ 2 ^ k := by rw [mul_one]; exact pow_le_pow_right₀ (one_le_two : (1 : ℝ≥0∞) ≤ 2) hk.le
      rw [hempty, Finset.card_empty, zero_mul]
      exact zero_le

/-! ### Theorem 2.1.1, second half: universality via Levin's theorem -/

open Classical in
/-- **Gács' auxiliary function** `F(x, y) = |x| − d(x)` for `y = |x|`, `∞` otherwise.
Multiplicatively: the least `m` with `2^{|x|} < 2^m · t x`. -/
noncomputable def levinF (t : BitString → ℝ≥0∞) (x y : BitString) : ENat :=
  if y = Nat.bits x.length then
    (if h : ∃ m : ℕ, (2 : ℝ≥0∞) ^ x.length < 2 ^ m * t x then (Nat.find h : ENat) else ⊤)
  else ⊤

theorem levinF_lt_iff (t : BitString → ℝ≥0∞) {x y : BitString} (hy : y = Nat.bits x.length)
    (m : ℕ) : levinF t x y < (m : ENat) ↔ ∃ m' < m, (2 : ℝ≥0∞) ^ x.length < 2 ^ m' * t x := by
  classical
  unfold levinF
  rw [if_pos hy]
  split_ifs with h
  · rw [Nat.cast_lt]
    constructor
    · intro hlt; exact ⟨Nat.find h, hlt, Nat.find_spec h⟩
    · rintro ⟨m', hm', hP⟩; exact (Nat.find_min' h hP).trans_lt hm'
  · simp only [not_top_lt, false_iff, not_exists, not_and]
    intro m' _ hP
    exact h ⟨m', hP⟩

theorem not_levinF_lt_of_ne (t : BitString → ℝ≥0∞) {x y : BitString}
    (hy : y ≠ Nat.bits x.length) (m : ℕ) : ¬ levinF t x y < (m : ENat) := by
  unfold levinF; rw [if_neg hy]; exact not_top_lt

theorem two_pow_mul_mono {a b : ℕ} (h : a ≤ b) (u : ℝ≥0∞) :
    (2 : ℝ≥0∞) ^ a * u ≤ 2 ^ b * u := by
  gcongr
  exact one_le_two

/-- The level condition, in the monotone form used for enumeration and counting. -/
theorem levinF_lt_iff' (t : BitString → ℝ≥0∞) {x y : BitString} (hy : y = Nat.bits x.length)
    (m : ℕ) : levinF t x y < (m : ENat) ↔ 0 < m ∧ (2 : ℝ≥0∞) ^ x.length < 2 ^ (m - 1) * t x := by
  rw [levinF_lt_iff t hy]
  constructor
  · rintro ⟨m', hm', hP⟩
    exact ⟨by omega, hP.trans_le (two_pow_mul_mono (by omega) _)⟩
  · rintro ⟨hm, hP⟩
    exact ⟨m - 1, by omega, hP⟩

/-- `F` is upper semicomputable. -/
theorem levinF_upperSemicomputable {t : BitString → ℝ≥0∞} (ht : IsMLTestUniform t) :
    UpperSemicomputable (levinF t) := by
  unfold UpperSemicomputable
  have hre := (ht.1.dyadic_lt_isRE.comp
    (g := fun q : (BitString × BitString) × ℕ ↦ (q.1.1, (2 ^ q.1.1.length, q.2 - 1)))
    (Computable.pair (Computable.fst.comp Computable.fst) (Computable.pair
      (natPow_primrec.to_comp.comp (Computable.const 2)
        (Computable.list_length.comp (Computable.fst.comp Computable.fst)))
      (Primrec.nat_sub.to_comp.comp Computable.snd (Computable.const 1))))).inter_decidable
    (fun q : (BitString × BitString) × ℕ ↦ q.1.2 = Nat.bits q.1.1.length ∧ 0 < q.2) ?_
  · refine hre.congr (fun q ↦ ?_)
    obtain ⟨⟨x, y⟩, m⟩ := q
    simp only
    by_cases hy : y = Nat.bits x.length
    · rw [levinF_lt_iff' t hy]
      have hdy : dyadicValue (2 ^ x.length) (m - 1) < t x
          ↔ (2 : ℝ≥0∞) ^ x.length < 2 ^ (m - 1) * t x := by
        unfold dyadicValue
        push_cast
        rw [ENNReal.div_lt_iff (Or.inl (two_pow_ne_zero' _)) (Or.inl (two_pow_ne_top' _)),
          mul_comm]
      rw [hdy]
      tauto
    · simp [hy, not_levinF_lt_of_ne t hy m]
  · have hA : Computable (fun q : (BitString × BitString) × ℕ ↦
        decide (q.1.2 = Nat.bits q.1.1.length)) :=
      (bitStringEq_primrec.to_comp.comp (Computable.pair (Computable.snd.comp Computable.fst)
        (natBitsComputable.comp (Computable.list_length.comp
          (Computable.fst.comp Computable.fst))))).of_eq (fun _ ↦ rfl)
    have hB : Computable (fun q : (BitString × BitString) × ℕ ↦ decide (0 < q.2)) :=
      (natLt_primrec.to_comp.comp (Computable.pair (Computable.const 0) Computable.snd)).of_eq
        (fun _ ↦ rfl)
    exact (Primrec.and.to_comp.comp hA hB).of_eq (fun q ↦ by simp)

/-- `F` has small level sets: at most `2^m` strings have `F(x, y) < m`. This is Levin's
hypothesis (1.5.1) with constant `0`. -/
theorem levinF_encard_le {t : BitString → ℝ≥0∞} (ht : IsMLTestUniform t) (y : BitString)
    (m : ℕ) : {x | levinF t x y < (m : ENat)}.encard ≤ 2 ^ (m + 0) := by
  classical
  rw [add_zero]
  have hmem : ∀ x, levinF t x y < (m : ENat) → x.length = bitsToNat y ∧ y = Nat.bits x.length := by
    intro x hx
    by_cases hy : y = Nat.bits x.length
    · exact ⟨by rw [hy, bitsToNat_bits], hy⟩
    · exact absurd hx (not_levinF_lt_of_ne t hy m)
  set n := bitsToNat y with hn
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · have : {x | levinF t x y < (m : ENat)} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      obtain ⟨_, hy⟩ := hmem x hx
      rw [levinF_lt_iff' t hy] at hx
      omega
    rw [this, Set.encard_empty]
    exact zero_le
  · have hsub : {x | levinF t x y < (m : ENat)} ⊆
        ↑((stringsOfLength n).filter (fun x ↦ (2 : ℝ≥0∞) ^ n < 2 ^ (m - 1) * t x)) := by
      intro x hx
      have hx' : levinF t x y < (m : ENat) := hx
      obtain ⟨hlen, hy⟩ := hmem x hx'
      rw [levinF_lt_iff' t hy] at hx'
      rw [Finset.mem_coe, Finset.mem_filter, memStringsOfLength]
      exact ⟨hlen, by rw [← hlen]; exact hx'.2⟩
    refine (Set.encard_le_encard hsub).trans ?_
    rw [Set.encard_coe_eq_coe_finsetCard]
    have hcard : ((stringsOfLength n).filter
        (fun x ↦ (2 : ℝ≥0∞) ^ n < 2 ^ (m - 1) * t x)).card ≤ 2 ^ m := by
      rcases le_or_gt (m - 1) n with hmn | hmn
      · have hiff : ∀ x, ((2 : ℝ≥0∞) ^ n < 2 ^ (m - 1) * t x)
            ↔ (2 : ℝ≥0∞) ^ (n - (m - 1)) < t x := by
          intro x
          have e : (2 : ℝ≥0∞) ^ n = 2 ^ (n - (m - 1)) * 2 ^ (m - 1) := by
            rw [← pow_add]; congr 1; omega
          rw [e, mul_comm ((2 : ℝ≥0∞) ^ (m - 1)) (t x)]
          constructor
          · intro h
            by_contra hle
            have hle' := not_lt.mp hle
            exact absurd h (not_lt.mpr (by gcongr))
          · intro h
            rw [mul_comm _ ((2 : ℝ≥0∞) ^ (m - 1)), mul_comm (t x)]
            exact ENNReal.mul_lt_mul_right (two_pow_ne_zero' _) (two_pow_ne_top' _) h
        rw [Finset.filter_congr (fun x _ ↦ hiff x)]
        have hML := ht.2 n (n - (m - 1))
        have e2 : 2 ^ n = 2 ^ (m - 1) * 2 ^ (n - (m - 1)) := by rw [← pow_add]; congr 1; omega
        rw [e2] at hML
        have hc := Nat.le_of_mul_le_mul_right hML (by positivity)
        exact hc.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      · calc _ ≤ (stringsOfLength n).card := Finset.card_filter_le _ _
          _ = 2 ^ n := cardStringsOfLength n
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : (((stringsOfLength n).filter
        (fun x ↦ (2 : ℝ≥0∞) ^ n < 2 ^ (m - 1) * t x)).card : ℕ∞) ≤ ((2 ^ m : ℕ) : ℕ∞) := by
      exact_mod_cast hcard
    push_cast at h2
    exact h2

/-- **Theorem 2.1.1, universality.** Every Martin-Löf test is dominated by `d₀`:
`t x ≤ 2^c · t₀ x`. -/
theorem mlTest_le_mlDeficiency (U : Map) (hU : isOptimalConditional U) {t : BitString → ℝ≥0∞}
    (ht : IsMLTestUniform t) : ∃ c : ℕ, ∀ x, t x ≤ 2 ^ c * mlDeficiency U x := by
  classical
  obtain ⟨c, hc⟩ := condK_le_of_encard_lt_le U hU (levinF t) (levinF_upperSemicomputable ht) 0
    (levinF_encard_le ht)
  refine ⟨c + 1, fun x ↦ ?_⟩
  rcases eq_or_ne (t x) 0 with h0 | h0
  · rw [h0]; exact zero_le
  -- Some `m` has `2^{|x|} < 2^m · t x`.
  have hex : ∃ m : ℕ, (2 : ℝ≥0∞) ^ x.length < 2 ^ m * t x := by
    rcases eq_or_ne (t x) ⊤ with htop | hfin
    · exact ⟨0, by rw [htop, pow_zero, one_mul]; exact lt_top_iff_ne_top.mpr (two_pow_ne_top' _)⟩
    · obtain ⟨m, hm⟩ := ENNReal.exists_nat_gt (ENNReal.div_ne_top (two_pow_ne_top' x.length) h0)
      refine ⟨m, ?_⟩
      rw [ENNReal.div_lt_iff (Or.inl h0) (Or.inl hfin)] at hm
      calc (2 : ℝ≥0∞) ^ x.length < m * t x := hm
        _ ≤ 2 ^ m * t x := by
            gcongr
            exact_mod_cast (Nat.lt_two_pow_self (n := m)).le
  have hF : levinF t x (Nat.bits x.length) = (Nat.find hex : ENat) := by
    unfold levinF; rw [if_pos rfl, dif_pos hex]
  set j := Nat.find hex with hj
  have hcond := hc x (Nat.bits x.length)
  rw [hF] at hcond
  -- Minimality of `j`, or the test bound at level `|x| + 1`: `2^j · t x ≤ 2^{|x|+1}`.
  have hbound : (2 : ℝ≥0∞) ^ j * t x ≤ 2 ^ (x.length + 1) := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, pow_zero, one_mul]
      have hML := ht.2 x.length (x.length + 1)
      by_contra hlt
      rw [not_le] at hlt
      have hmem : x ∈ (stringsOfLength x.length).filter
          (fun z ↦ (2 : ℝ≥0∞) ^ (x.length + 1) < t z) :=
        Finset.mem_filter.mpr ⟨(memStringsOfLength _ _).mpr rfl, hlt⟩
      have hpos : 0 < ((stringsOfLength x.length).filter
          (fun z ↦ (2 : ℝ≥0∞) ^ (x.length + 1) < t z)).card := Finset.card_pos.mpr ⟨x, hmem⟩
      have h1 : 2 ^ (x.length + 1) ≤ 2 ^ x.length :=
        le_trans (Nat.le_mul_of_pos_left _ hpos) hML
      have h2 := Nat.pow_lt_pow_right (by norm_num : 1 < 2) (Nat.lt_succ_self x.length)
      omega
    · obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hmin : ¬ (2 : ℝ≥0∞) ^ x.length < 2 ^ i * t x :=
        Nat.find_min hex (by omega : i < Nat.find hex)
      rw [not_lt] at hmin
      calc (2 : ℝ≥0∞) ^ j * t x = 2 * (2 ^ i * t x) := by rw [hi]; ring
        _ ≤ 2 * 2 ^ x.length := by gcongr
        _ = 2 ^ (x.length + 1) := by ring
  -- From `C ≤ j + c`: `2^{-j} ≤ 2^c · 2^{-C}`.
  have hcw : (2 : ℝ≥0∞)⁻¹ ^ j ≤ 2 ^ c * complexityWeight (condK U x (Nat.bits x.length)) := by
    have h1 := complexityWeight_le_of_le hcond
    rw [← Nat.cast_add, complexityWeight_coe, pow_add] at h1
    calc (2 : ℝ≥0∞)⁻¹ ^ j = 2 ^ c * (2⁻¹ ^ j * 2⁻¹ ^ c) := by
          rw [mul_comm ((2 : ℝ≥0∞)⁻¹ ^ j), ← mul_assoc,
            show (2 : ℝ≥0∞)⁻¹ ^ c = ((2 : ℝ≥0∞) ^ c)⁻¹ from ENNReal.inv_pow.symm,
            ENNReal.mul_inv_cancel (two_pow_ne_zero' c) (two_pow_ne_top' c), one_mul]
      _ ≤ 2 ^ c * complexityWeight (condK U x (Nat.bits x.length)) := by gcongr
  calc t x = 2⁻¹ ^ j * (2 ^ j * t x) := by
        rw [← mul_assoc, show (2 : ℝ≥0∞)⁻¹ ^ j = ((2 : ℝ≥0∞) ^ j)⁻¹ from ENNReal.inv_pow.symm,
          ENNReal.inv_mul_cancel (two_pow_ne_zero' j) (two_pow_ne_top' j), one_mul]
    _ ≤ 2⁻¹ ^ j * 2 ^ (x.length + 1) := by gcongr
    _ ≤ (2 ^ c * complexityWeight (condK U x (Nat.bits x.length))) * 2 ^ (x.length + 1) := by
        gcongr
    _ = 2 ^ (c + 1) * mlDeficiency U x := by unfold mlDeficiency; ring

/-- **Gács Theorem 2.1.1 (Martin-Löf).** `d₀(x) = |x| − C(x | |x|)` is a universal
Martin-Löf test for the uniform distribution. -/
theorem mlDeficiency_isUniversalMLTestUniform (U : Map) (hU : isOptimalConditional U) :
    IsUniversalMLTestUniform (mlDeficiency U) :=
  ⟨mlDeficiency_isMLTestUniform U hU, fun _ ht ↦ mlTest_le_mlDeficiency U hU ht⟩

end Kolmogorov
