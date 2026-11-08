/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.CompComp.Search
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.PaperTheorems

/-!
# Gács Theorem 3.1.5: complexity is sometimes complex (§3.3.1)

**Theorem 3.1.5.** There is a constant `c` such that for every `n` some string `x` of length
`n` has `K(K(x) ∣ x) ≥ log n − log log n − c` (`exists_KK_ge`). `K(x)` inside the
complexity is written in the unary code `natCode` used by the upstream addition theorem;
any other computable encoding changes `K(K(x) ∣ x)` by `O(1)`.

## Proof (Gács' argument, made explicit)

Let `s = max_{|x| = n} K(K(x) ∣ x)`. If `s ≥ log n` we are done; otherwise:

* `cnt x` counts the programs `p`, `|p| ≤ s`, suitable for `x` (`Search.lean`), and
  `a j = |M_j| = #{x : |x| = n, cnt x ≥ j}`. Every `x` has a suitable program (the one of
  length `≤ s` printing `K(x)`), so `a 1 = 2^n`; there are fewer than `2^{s+1}` programs, so
  `a (2^{s+1}) = 0`.
* **Slow decrease** (`slow_decrease`): `a i + 1 ≤ (A + 1)(a (i+1) + 1)` with
  `A = 2^{14 log n + O(1)}`. With `D = a i − a (i+1) = #{x : cnt x = i}` and `m = ⌊log D⌋`, some
  `x₀` with `cnt x₀ = i` has `K(x₀) ≥ m` (counting), so the search machine `dec`, run on
  `(n, s, i, a (i+1), m)`, outputs an `x` with `K(x) ≥ m` (`dec_spec`). Hence
  `m ≤ K(⟨n, s, i, a(i+1), m⟩) + O(1) ≤ log a(i+1) + 14 log n + O(1)`, i.e.
  `D ≤ (a(i+1) + 1) · A`.
* Iterating from `a 1 = 2^n` to `a (2^{s+1}) = 0` gives `2^n < (A + 1)^{2^{s+1}}`, so
  `n < (14 log n + O(1)) 2^{s+1}`, and taking logarithms `log n ≤ s + log log n + O(1)`.

Gács' constant `4 log n` becomes `14 log n` here because all five parameters are coded
self-delimitingly with the crude bound `K(v) ≤ |v| + 2 log |v| + O(1)`; only `log log n`
survives in the final bound, so this does not matter.
-/

namespace Kolmogorov.Information.CompComp

open Nat.Partrec (Code)

/-! ### Complexities as natural numbers -/

/-- `K(x)` as a natural number (finite for an optimal machine). -/
noncomputable def kp (U : Map) (x : BitString) : ℕ := (KP U x []).toNat

section KP

variable {U : Map} (hU : IsOptimalPrefixConditional U)
include hU

theorem KP_eq_kp (x : BitString) : KP U x [] = (kp U x : ENat) :=
  (ENat.coe_toNat (KP_ne_top_of_optimal U hU x [])).symm

theorem exists_kp_pairCode_le : ∃ c : ℕ, ∀ u v, kp U (pairCode u v) ≤ kp U u + kp U v + c := by
  obtain ⟨c₁, h₁⟩ := KPPair_le_KPPlain_add_KP U hU
  obtain ⟨c₂, h₂⟩ := KP_le_KPPlain U hU
  refine ⟨c₁ + c₂, fun u v ↦ ?_⟩
  have h := h₁ u v
  have h' := h₂ v u
  unfold KPPair KPPlain at h
  unfold KPPlain at h'
  rw [KP_eq_kp hU, KP_eq_kp hU] at h
  rw [KP_eq_kp hU] at h'
  have : (kp U (pairCode u v) : ENat) ≤ ((kp U u + kp U v + (c₁ + c₂) : ℕ) : ENat) := by
    calc (kp U (pairCode u v) : ENat) ≤ kp U u + KP U v u + c₁ := h
      _ ≤ kp U u + (kp U v + c₂) + c₁ := by gcongr
      _ = ((kp U u + kp U v + (c₁ + c₂) : ℕ) : ENat) := by push_cast; ring
  exact_mod_cast this

/-- The code length of a number: `|v| + 2 log |v|`, with `|v| = size v`. -/
def numLen (v : ℕ) : ℕ := v.size + 2 * v.size.size

theorem exists_kp_bits_le : ∃ c : ℕ, ∀ v : ℕ, kp U (Nat.bits v) ≤ numLen v + c := by
  obtain ⟨c, hc⟩ := KPPlain_le_length_add_log U hU
  refine ⟨c, fun v ↦ ?_⟩
  have h := hc (Nat.bits v)
  unfold KPPlain at h
  rw [KP_eq_kp hU, Nat.size_eq_bits_len, Nat.size_eq_bits_len] at h
  unfold numLen
  exact_mod_cast h

theorem exists_kp_encParams_le : ∃ c : ℕ, ∀ n s i N m : ℕ,
    kp U (encParams (n, s, i, N, m)) ≤
      numLen n + numLen s + numLen i + numLen N + numLen m + c := by
  obtain ⟨c₁, h₁⟩ := exists_kp_pairCode_le hU
  obtain ⟨c₂, h₂⟩ := exists_kp_bits_le hU
  refine ⟨4 * c₁ + 5 * c₂, fun n s i N m ↦ ?_⟩
  unfold encParams
  simp only
  have := h₁ (Nat.bits n) (pairCode (Nat.bits s) (pairCode (Nat.bits i)
    (pairCode (Nat.bits N) (Nat.bits m))))
  have := h₁ (Nat.bits s) (pairCode (Nat.bits i) (pairCode (Nat.bits N) (Nat.bits m)))
  have := h₁ (Nat.bits i) (pairCode (Nat.bits N) (Nat.bits m))
  have := h₁ (Nat.bits N) (Nat.bits m)
  have := h₂ n
  have := h₂ s
  have := h₂ i
  have := h₂ N
  have := h₂ m
  omega

/-- The search machine costs only a constant. -/
theorem exists_kp_dec_le (c : Code) : ∃ c₁ : ℕ, ∀ a x, x ∈ dec c a → kp U x ≤ kp U a + c₁ := by
  obtain ⟨c₁, h⟩ := KP_partrec_cond_first_map_le U hU (fun _ a ↦ dec c a)
    ((dec_partrec c).comp Computable.fst)
  refine ⟨c₁, fun a x hx ↦ ?_⟩
  have := h a x [] hx
  rw [KP_eq_kp hU, KP_eq_kp hU] at this
  exact_mod_cast this

/-- **Counting.** A set of at least `2^m` strings contains one with `K ≥ m`. -/
theorem exists_kp_ge_of_card (S : Finset BitString) (m : ℕ) (hS : 2 ^ m ≤ S.card) :
    ∃ x ∈ S, m ≤ kp U x := by
  classical
  by_contra hall
  simp only [not_exists, not_and, not_le] at hall
  have hm : 0 < m := by
    obtain ⟨x, hx⟩ : S.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by positivity) hS)
    exact lt_of_le_of_lt (Nat.zero_le _) (hall x hx)
  have hprog : ∀ x ∈ S, ∃ p : BitString, p.length < m ∧ x ∈ U (p, []) := by
    intro x hx
    obtain ⟨p, hp, hlen⟩ := exists_program_of_KP_ne_top (KP_ne_top_of_optimal U hU x [])
    refine ⟨p, ?_, hp⟩
    have h1 : (p.length : ENat) = kp U x := by rw [← KP_eq_kp hU]; exact hlen
    have h2 : p.length = kp U x := by exact_mod_cast h1
    rw [h2]; exact hall x hx
  choose! f hf using hprog
  have hcard : S.card ≤ (boundedPrograms (m - 1)).toFinset.card := by
    refine Finset.card_le_card_of_injOn f (fun x hx ↦ ?_) (fun x hx y hy hxy ↦ ?_)
    · rw [Finset.mem_coe, List.mem_toFinset, mem_boundedPrograms_iff]
      have := (hf x hx).1; omega
    · have h1 := (hf x hx).2
      have h2 := (hf y hy).2
      rw [hxy] at h1
      exact Part.mem_unique h1 h2
  have hlen : (boundedPrograms (m - 1)).toFinset.card < 2 ^ m := by
    have := length_boundedPrograms_lt (m - 1)
    rw [show m - 1 + 1 = m by omega] at this
    exact lt_of_le_of_lt (List.toFinset_card_le _) this
  omega

end KP

/-! ### Counting lemmas for the sets `M_j` -/

theorem countP_le_split {β : Type*} (l : List β) (f : β → ℕ) (i : ℕ) :
    l.countP (fun x ↦ decide (i ≤ f x)) =
      l.countP (fun x ↦ decide (f x = i)) + l.countP (fun x ↦ decide (i + 1 ≤ f x)) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons, ih]
    split_ifs with h1 h2 h3 h3 h2 h3 h3 <;> simp only [decide_eq_true_eq] at * <;> omega

/-- Iterating the slow decrease. -/
theorem iterate_slow (a : ℕ → ℕ) (A : ℕ) (h : ∀ i, a i + 1 ≤ (A + 1) * (a (i + 1) + 1)) :
    ∀ k, a 1 + 1 ≤ (A + 1) ^ k * (a (1 + k) + 1) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    calc a 1 + 1 ≤ (A + 1) ^ k * (a (1 + k) + 1) := ih
      _ ≤ (A + 1) ^ k * ((A + 1) * (a (1 + k + 1) + 1)) := Nat.mul_le_mul_left _ (h _)
      _ = (A + 1) ^ (k + 1) * (a (1 + (k + 1)) + 1) := by rw [pow_succ]; ring_nf

/-! ### Logarithm arithmetic -/

theorem size_le_log_succ {v : ℕ} : v.size ≤ Nat.log 2 v + 1 :=
  Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) v)

theorem two_pow_size_le (N : ℕ) : 2 ^ N.size ≤ 2 * (N + 1) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have hs : 0 < N.size := Nat.size_pos.mpr hN
    have : 2 ^ (N.size - 1) ≤ N := Nat.lt_size.mp (by omega)
    calc 2 ^ N.size = 2 * 2 ^ (N.size - 1) := by
          rw [← pow_succ']; congr 1; omega
      _ ≤ 2 * (N + 1) := by omega

theorem log_mul_le (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b + 1 := by
  have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) a
  have h2 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) b
  have : a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    calc a * b < 2 ^ (Nat.log 2 a).succ * 2 ^ (Nat.log 2 b).succ :=
          Nat.mul_lt_mul'' h1 h2
      _ = 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by rw [← pow_add]; congr 1; omega
  have := Nat.log_lt_of_lt_pow (Nat.mul_ne_zero ha hb) this
  omega

/-- From `n < P · 2^{s+1}` to `log n ≤ log P + s + 1`. -/
theorem log_le_of_lt_mul_pow {n P s : ℕ} (h : n < P * 2 ^ (s + 1)) :
    Nat.log 2 n ≤ Nat.log 2 P + s + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h1 := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) P
  have : n < 2 ^ (Nat.log 2 P + s + 2) := by
    calc n < P * 2 ^ (s + 1) := h
      _ ≤ 2 ^ (Nat.log 2 P).succ * 2 ^ (s + 1) := Nat.mul_le_mul_right _ h1.le
      _ = 2 ^ (Nat.log 2 P + s + 2) := by rw [← pow_add]; congr 1; omega
  have := Nat.log_lt_of_lt_pow (by omega) this
  omega

/-! ### The main argument -/

section Main

variable {U : Map} (hU : IsOptimalPrefixConditional U)
include hU

/-- **Slow decrease** of `|M_j|`, Gács (3.3.2). For `n ≥ 1`, `s < log n` and `|x| = n`
implying a program of length `≤ s` printing `K(x)` in unary,
`a i + 1 ≤ (A + 1)(a (i+1) + 1)` with `A = 2^{14 log n + K₀ + 18}`. -/
theorem slow_decrease (c : Code) (hc : CodeOf U c) {c₁ c₂ : ℕ}
    (hdec : ∀ a x, x ∈ dec c a → kp U x ≤ kp U a + c₁)
    (henc : ∀ n s i N m : ℕ, kp U (encParams (n, s, i, N, m)) ≤
      numLen n + numLen s + numLen i + numLen N + numLen m + c₂)
    {n s : ℕ} (hsL : s < Nat.log 2 n)
    (hs : ∀ x : BitString, x.length = n → ∃ p, p.length ≤ s ∧ ∃ y, y ∈ U (p, x) ∧
      KP U x [] = ((y.length - 1 : ℕ) : ENat)) (i : ℕ) :
    (exactLengthPrograms n).countP (fun x ↦ decide (i ≤ cnt U s x)) + 1 ≤
      (2 ^ (14 * Nat.log 2 n + c₁ + c₂ + 18) + 1) *
        ((exactLengthPrograms n).countP (fun x ↦ decide (i + 1 ≤ cnt U s x)) + 1) := by
  classical
  set L := Nat.log 2 n with hL
  set l := exactLengthPrograms n with hl
  set N := l.countP (fun x ↦ decide (i + 1 ≤ cnt U s x)) with hN
  set D := l.countP (fun x ↦ decide (cnt U s x = i)) with hD
  set A := 2 ^ (14 * L + c₁ + c₂ + 18) with hA
  rw [countP_le_split l (cnt U s) i]
  change D + N + 1 ≤ (A + 1) * (N + 1)
  -- Suffices: `D ≤ (N + 1) · A`.
  suffices hDle : D ≤ (N + 1) * A by nlinarith
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · rw [hD0]; exact Nat.zero_le _
  -- Indices beyond the number of programs give nothing.
  have hcnt_lt : ∀ x, cnt U s x < 2 ^ (s + 1) := fun x ↦
    lt_of_le_of_lt (List.countP_le_length) (length_boundedPrograms_lt s)
  have hi : i < 2 ^ (s + 1) := by
    obtain ⟨x, _, hx⟩ := List.countP_pos_iff.mp hDpos
    rw [decide_eq_true_iff] at hx
    rw [← hx]; exact hcnt_lt x
  -- The set of `x` with exactly `i` suitable programs, and a complex element of it.
  set m := Nat.log 2 D with hm
  set S := (l.filter (fun x ↦ decide (cnt U s x = i))).toFinset with hS
  have hScard : S.card = D := by
    rw [hS, List.toFinset_card_of_nodup ((exactLengthPrograms_nodup n).filter _), hD,
      List.countP_eq_length_filter]
  have h2m : 2 ^ m ≤ S.card := by rw [hScard]; exact Nat.pow_log_le_self 2 hDpos.ne'
  obtain ⟨x₀, hx₀S, hx₀K⟩ := exists_kp_ge_of_card hU S m h2m
  rw [hS, List.mem_toFinset, List.mem_filter, decide_eq_true_iff] at hx₀S
  obtain ⟨x, hxdec, hxK⟩ := dec_spec hc (n := n) (s := s) (i := i) (N := N) (m := m) hs rfl
    ⟨x₀, exactLengthPrograms_length_eq n x₀ hx₀S.1, hx₀S.2,
      by rw [KP_eq_kp hU]; exact_mod_cast hx₀K⟩
  rw [KP_eq_kp hU] at hxK
  have hmK : m ≤ kp U x := by exact_mod_cast hxK
  have hK := (hdec _ x hxdec).trans (Nat.add_le_add_right (henc n s i N m) c₁)
  -- Bounding the parameter lengths.
  have hnL : n.size ≤ L + 1 := size_le_log_succ
  have hD2 : D ≤ 2 ^ n := by
    rw [hD, ← length_exactLengthPrograms n]; exact List.countP_le_length
  have hmn : m ≤ n := by
    rw [hm]
    calc Nat.log 2 D ≤ Nat.log 2 (2 ^ n) := Nat.log_mono_right hD2
      _ = n := Nat.log_pow (by norm_num) n
  have hsize_le_self : ∀ v : ℕ, v.size ≤ v := fun v ↦
    Nat.size_le.mpr (Nat.lt_two_pow_self)
  have hsmall : ∀ v : ℕ, v.size ≤ L + 1 → numLen v ≤ 3 * (L + 1) := fun v hv ↦ by
    unfold numLen
    have := hsize_le_self v.size
    omega
  have hn' := hsmall n hnL
  have hs' := hsmall s (by have := hsize_le_self s; omega)
  have hi' := hsmall i (by
    have : i.size ≤ s + 1 := Nat.size_le.mpr hi
    omega)
  have hm' := hsmall m (by have := Nat.size_le_size hmn; omega)
  have hNsize : N.size.size ≤ L + 2 := by
    have hN2 : N ≤ 2 ^ n := by
      rw [hN, ← length_exactLengthPrograms n]; exact List.countP_le_length
    have h1 : N.size ≤ n + 1 := Nat.size_le.mpr (by
      calc N ≤ 2 ^ n := hN2
        _ < 2 ^ (n + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega))
    have h2 : n + 1 < 2 ^ (L + 2) := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
      rw [← hL] at this
      calc n + 1 ≤ 2 ^ (L + 1) := this
        _ < 2 ^ (L + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact Nat.size_le.mpr (lt_of_le_of_lt h1 h2)
  have hNl : numLen N ≤ N.size + 2 * (L + 2) := by unfold numLen; omega
  -- `m ≤ size N + 14 L + 16 + c₁ + c₂`.
  have hmbound : m ≤ N.size + (14 * L + c₁ + c₂ + 16) := by omega
  have hDlt : D < 2 ^ (m + 1) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) D
    rw [← hm] at this; exact this
  calc D ≤ 2 ^ (m + 1) := hDlt.le
    _ ≤ 2 ^ (N.size + (14 * L + c₁ + c₂ + 16) + 1) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 2 ^ N.size * 2 ^ (14 * L + c₁ + c₂ + 17) := by rw [← pow_add]; congr 1
    _ ≤ (2 * (N + 1)) * 2 ^ (14 * L + c₁ + c₂ + 17) :=
        Nat.mul_le_mul_right _ (two_pow_size_le N)
    _ = (N + 1) * A := by rw [hA, pow_succ]; ring

/-- **Gács Theorem 3.1.5.** For every `n` there is a string `x` of length `n` with
`K(K(x) ∣ x) ≥ log n − log log n − c`. Here `K(x)` is written in unary (`natCode`) inside the
complexity, as in the upstream addition theorem. -/
theorem exists_KK_ge : ∃ c : ℕ, ∀ n : ℕ, ∃ x : BitString, x.length = n ∧
    (Nat.log 2 n : ℤ) - Nat.log 2 (Nat.log 2 n) - c ≤
      ((KP U (natCode (KP U x []).toNat) x).toNat : ℤ) := by
  classical
  obtain ⟨c, hc⟩ := exists_codeOf hU.isDecompressor
  obtain ⟨c₁, hdec⟩ := exists_kp_dec_le hU c
  obtain ⟨c₂, henc⟩ := exists_kp_encParams_le hU
  set K₁ := c₁ + c₂ + 21 with hK₁
  refine ⟨Nat.log 2 (14 + K₁) + 2, fun n ↦ ?_⟩
  set L := Nat.log 2 n with hL
  set l := exactLengthPrograms n with hl
  set F : BitString → ℕ := fun x ↦ (KP U (natCode (KP U x []).toNat) x).toNat with hF
  have hl0 : l.toFinset.Nonempty := by
    refine ⟨List.replicate n false, List.mem_toFinset.mpr ?_⟩
    exact mem_exactLengthPrograms_iff.mpr (by simp)
  obtain ⟨x₀, hx₀l, hx₀F⟩ := Finset.exists_mem_eq_sup l.toFinset hl0 F
  set s := l.toFinset.sup F with hsdef
  have hx₀n : x₀.length = n := exactLengthPrograms_length_eq n x₀ (List.mem_toFinset.mp hx₀l)
  refine ⟨x₀, hx₀n, ?_⟩
  change (L : ℤ) - Nat.log 2 L - (Nat.log 2 (14 + K₁) + 2 : ℕ) ≤ (F x₀ : ℤ)
  rw [← hx₀F]
  by_cases hsL : L ≤ s
  · push_cast; omega
  rw [not_le] at hsL
  -- Every `x` of length `n` has a program of length `≤ s` printing `K(x)` in unary.
  have hs : ∀ x : BitString, x.length = n → ∃ p, p.length ≤ s ∧ ∃ y, y ∈ U (p, x) ∧
      KP U x [] = ((y.length - 1 : ℕ) : ENat) := by
    intro x hx
    obtain ⟨p, hp, hlen⟩ := exists_program_of_KP_ne_top
      (KP_ne_top_of_optimal U hU (natCode (KP U x []).toNat) x)
    refine ⟨p, ?_, natCode (KP U x []).toNat, hp, ?_⟩
    · have hle : F x ≤ s := Finset.le_sup (f := F)
        (List.mem_toFinset.mpr (mem_exactLengthPrograms_iff.mpr hx))
      have : p.length = F x := by
        change p.length = (KP U (natCode (KP U x []).toNat) x).toNat
        rw [← hlen, ENat.toNat_coe]
      omega
    · rw [KP_eq_kp hU]
      simp [natCode, kp]
  -- The counts `a j = |M_j|`.
  set a : ℕ → ℕ := fun j ↦ l.countP (fun x ↦ decide (j ≤ cnt U s x)) with ha
  have ha1 : a 1 = 2 ^ n := by
    simp only [ha]
    rw [List.countP_eq_length.mpr, length_exactLengthPrograms]
    intro x hx
    rw [decide_eq_true_iff]
    obtain ⟨p, hps, y, hy, hKy⟩ := hs x (exactLengthPrograms_length_eq n x hx)
    unfold cnt
    exact List.countP_pos_iff.mpr ⟨p, (mem_boundedPrograms_iff p s).mpr hps,
      decide_eq_true (show Suit U p x from ⟨y, hy, hKy.le⟩)⟩
  have haJ : a (2 ^ (s + 1)) = 0 := by
    simp only [ha]
    refine List.countP_eq_zero.mpr fun x _ ↦ ?_
    rw [decide_eq_true_iff, not_le]
    exact lt_of_le_of_lt List.countP_le_length (length_boundedPrograms_lt s)
  set A := 2 ^ (14 * L + c₁ + c₂ + 18) with hA
  have hslow : ∀ i, a i + 1 ≤ (A + 1) * (a (i + 1) + 1) := fun i ↦
    slow_decrease hU c hc hdec henc hsL hs i
  have hit := iterate_slow a A hslow (2 ^ (s + 1) - 1)
  rw [show 1 + (2 ^ (s + 1) - 1) = 2 ^ (s + 1) by
    have := Nat.one_le_two_pow (n := s + 1); omega, haJ, ha1] at hit
  -- `2^n < 2^{(14 L + K₁) 2^{s+1}}`.
  have hA1 : A + 1 ≤ 2 ^ (14 * L + K₁) := by
    rw [hA, hK₁]
    calc 2 ^ (14 * L + c₁ + c₂ + 18) + 1 ≤ 2 ^ (14 * L + c₁ + c₂ + 18) * 2 := by
          have := Nat.one_le_two_pow (n := 14 * L + c₁ + c₂ + 18); omega
      _ = 2 ^ (14 * L + c₁ + c₂ + 19) := by rw [← pow_succ]
      _ ≤ 2 ^ (14 * L + (c₁ + c₂ + 21)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpow : 2 ^ n < 2 ^ ((14 * L + K₁) * 2 ^ (s + 1)) := by
    calc 2 ^ n < 2 ^ n + 1 := Nat.lt_succ_self _
      _ ≤ (A + 1) ^ (2 ^ (s + 1) - 1) * (0 + 1) := hit
      _ ≤ (A + 1) ^ (2 ^ (s + 1)) := by
          rw [zero_add, mul_one]
          exact Nat.pow_le_pow_right (Nat.succ_pos A) (Nat.sub_le _ 1)
      _ ≤ (2 ^ (14 * L + K₁)) ^ (2 ^ (s + 1)) := Nat.pow_le_pow_left hA1 _
      _ = 2 ^ ((14 * L + K₁) * 2 ^ (s + 1)) := by rw [← pow_mul]
  have hnlt : n < (14 * L + K₁) * 2 ^ (s + 1) :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpow
  -- Logarithms.
  have hLpos : 0 < L := by omega
  have hlog1 := log_le_of_lt_mul_pow hnlt
  have hP : 14 * L + K₁ ≤ (14 + K₁) * L := by nlinarith
  have hlog2 : Nat.log 2 (14 * L + K₁) ≤ Nat.log 2 (14 + K₁) + Nat.log 2 L + 1 :=
    (Nat.log_mono_right hP).trans (log_mul_le _ _ (by omega) (by omega))
  rw [← hL] at hlog1
  push_cast
  omega

end Main

end Kolmogorov.Information.CompComp
