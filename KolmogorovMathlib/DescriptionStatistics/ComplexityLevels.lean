/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.HaltingCount

/-!
# Complexity windows and the upper half of Theorem 1.7.2's second assertion

Definition 1.7.2 introduces `g_T(m)`, the number of objects of complexity exactly
`m`, and the moving average `h_T(n, c)` of `g_T` over the window `[n − c, n + c]`.
Theorem 1.7.2 asserts `log h_T(n, c) =⁺ n − K(n)` for a suitable constant `c`.

We work with the window directly rather than through `g_T`: `windowSet U n c` is
the set of objects whose complexity lies within `c` of `n`, and `windowCount` is
its cardinality. Up to the normalising factor `2c + 1`, which Gács himself says may
be dropped, this is `h_T(n, c)`.

## Why the window is finite, and the upper bound

Every object of complexity `m` has a shortest program of length exactly `m`, and a
program has a single output, so choosing a shortest program for each object
(`shortestProg`) injects the window into the halting programs of the lengths in the
window (`windowProgs`), a finite set. That injection gives finiteness and the bound

  `windowCount U n c ≤ Σ_{m ∈ [n−c, n+c]} |D_m|`.

Each `|D_m|` is at most `2^c · 2^{m − K(m)}` by `HaltingCount`, and the shift bound
`K(n) ≤⁺ K(m)` for `|m − n| ≤ c` (`KPPlain_natCode_shift_le`) turns every `K(m)` into
`K(n)`. Because the window has fixed width, that shift bound is a *finite* maximum of
constants, one per offset, each an instance of `KPPlain_partrec_map_le`. No general
continuity theorem for `K` is needed.

The lower half, the Markov argument, is in `ComplexityLevelsLower`.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### A chosen shortest program -/

open Classical in
/-- A shortest program for `x` in the empty context, chosen classically; `[]` when
no program exists. -/
noncomputable def shortestProg (U : Map) (x : BitString) : BitString :=
  if h : KP U x [] ≠ ⊤ then Classical.choose (KP_mem_candidateLengths_of_ne_top h) else []

/-- When `K(x)` is finite, the chosen program produces `x` and has length `K(x)`. -/
theorem shortestProg_spec (U : Map) {x : BitString} (h : KP U x [] ≠ ⊤) :
    produces U (shortestProg U x) [] x ∧
      ((shortestProg U x).length : ENat) = KP U x [] := by
  unfold shortestProg
  rw [dif_pos h]
  exact Classical.choose_spec (KP_mem_candidateLengths_of_ne_top h)

/-- Two objects with finite complexity and the same chosen shortest program are
equal, since a program has one output. -/
theorem shortestProg_inj (U : Map) {x x' : BitString}
    (hx : KP U x [] ≠ ⊤) (hx' : KP U x' [] ≠ ⊤)
    (h : shortestProg U x = shortestProg U x') : x = x' := by
  have h1 := (shortestProg_spec U hx).1
  have h2 := (shortestProg_spec U hx').1
  rw [h] at h1
  exact Part.mem_unique h1 h2

/-! ### The complexity window -/

/-- **The complexity window**: objects whose complexity is finite and within `c` of
`n`. Up to normalisation this is the population counted by Gács' `h_T(n, c)`. -/
def windowSet (U : Map) (n c : ℕ) : Set BitString :=
  {x | ∃ m : ℕ, HasPrefixComplexityValue U x m ∧ n ≤ m + c ∧ m ≤ n + c}

/-- The number of objects in the complexity window. -/
noncomputable def windowCount (U : Map) (n c : ℕ) : ℕ := (windowSet U n c).ncard

/-- The finite set of halting programs of the lengths in the window. -/
noncomputable def windowProgs (U : Map) (n c : ℕ) : Finset BitString :=
  (Finset.Icc (n - c) (n + c)).biUnion (haltSet U)

/-- An object in the window has finite complexity. -/
theorem KP_ne_top_of_mem_windowSet {U : Map} {n c : ℕ} {x : BitString}
    (hx : x ∈ windowSet U n c) : KP U x [] ≠ ⊤ := by
  obtain ⟨m, hm, -, -⟩ := hx
  rw [← KPPlain_eq_KP, ← hm]
  exact ENat.coe_ne_top m

/-- The chosen shortest program sends the window into `windowProgs`. -/
theorem shortestProg_mapsTo_windowProgs (U : Map) (n c : ℕ) :
    Set.MapsTo (shortestProg U) (windowSet U n c) ↑(windowProgs U n c) := by
  intro x hx
  obtain ⟨m, hm, hn, hmn⟩ := hx
  have hne : KP U x [] ≠ ⊤ := by
    rw [← KPPlain_eq_KP, ← hm]; exact ENat.coe_ne_top m
  obtain ⟨hprod, hlen⟩ := shortestProg_spec U hne
  have hlen' : (shortestProg U x).length = m := by
    have : ((shortestProg U x).length : ENat) = (m : ENat) := by
      rw [hlen, ← KPPlain_eq_KP, ← hm]
    exact_mod_cast this
  rw [Finset.mem_coe, windowProgs, Finset.mem_biUnion]
  refine ⟨m, Finset.mem_Icc.mpr ⟨by omega, hmn⟩, ?_⟩
  exact mem_haltSet.mpr ⟨hlen', Part.dom_iff_mem.mpr ⟨x, hprod⟩⟩

/-- The chosen shortest program is injective on the window. -/
theorem shortestProg_injOn_windowSet (U : Map) (n c : ℕ) :
    Set.InjOn (shortestProg U) (windowSet U n c) :=
  fun _ hx _ hx' h ↦
    shortestProg_inj U (KP_ne_top_of_mem_windowSet hx) (KP_ne_top_of_mem_windowSet hx') h

/-- The window is finite. -/
theorem windowSet_finite (U : Map) (n c : ℕ) : (windowSet U n c).Finite :=
  Set.Finite.of_injOn (shortestProg_mapsTo_windowProgs U n c)
    (shortestProg_injOn_windowSet U n c) (Finset.finite_toSet _)

/-- **The window is no larger than the halting sets of its lengths combined.** -/
theorem windowCount_le_sum_haltCount (U : Map) (n c : ℕ) :
    windowCount U n c ≤ ∑ m ∈ Finset.Icc (n - c) (n + c), haltCount U m := by
  classical
  calc windowCount U n c
      ≤ (↑(windowProgs U n c) : Set BitString).ncard :=
        Set.ncard_le_ncard_of_injOn (shortestProg U) (shortestProg_mapsTo_windowProgs U n c)
          (shortestProg_injOn_windowSet U n c) (Finset.finite_toSet _)
    _ = (windowProgs U n c).card := Set.ncard_coe_finset _
    _ ≤ ∑ m ∈ Finset.Icc (n - c) (n + c), haltCount U m := Finset.card_biUnion_le

/-! ### The shift bound: `K(n) ≤⁺ K(m)` for `|m − n| ≤ c` -/

/-- **Shift bound.** For a fixed window width `c`, the complexity of a number is at
most that of any number within `c` of it, up to a constant depending only on `c`.
Each offset `j ∈ [0, 2c]` gives a computable map `natCode m ↦ natCode (m + j − c)`,
hence a constant by `KPPlain_partrec_map_le`; take the maximum over the finitely
many offsets. -/
theorem KPPlain_natCode_shift_le (U : Map) (hU : IsOptimalPrefixConditional U) (c : ℕ) :
    ∃ s : ℕ, ∀ m n : ℕ, n ≤ m + c → m ≤ n + c →
      KPPlain U (natCode n) ≤ KPPlain U (natCode m) + (s : ENat) := by
  have hmap : ∀ j : ℕ, ∃ cj : ℕ, ∀ w : BitString,
      KPPlain U (natCode (w.length - 1 + j - c)) ≤ KPPlain U w + (cj : ENat) := by
    intro j
    have hprim : Primrec (fun w : BitString ↦ natCode (w.length - 1 + j - c)) :=
      natCode_primrec.comp
        (Primrec.nat_sub.comp
          (Primrec.nat_add.comp
            (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1))
            (Primrec.const j))
          (Primrec.const c))
    have hf : Partrec (fun w : BitString ↦
        (Part.some (natCode (w.length - 1 + j - c)) : Part BitString)) :=
      hprim.to_comp
    obtain ⟨cj, hcj⟩ := KPPlain_partrec_map_le U hU _ hf
    exact ⟨cj, fun w ↦ hcj w _ (Part.mem_some _)⟩
  choose cfun hcfun using hmap
  refine ⟨(Finset.range (2 * c + 1)).sup cfun, fun m n hn hm ↦ ?_⟩
  have hjlt : n + c - m < 2 * c + 1 := by omega
  have hval : (natCode m).length - 1 + (n + c - m) - c = n := by
    rw [length_natCode]; omega
  have h := hcfun (n + c - m) (natCode m)
  rw [hval] at h
  calc KPPlain U (natCode n)
      ≤ KPPlain U (natCode m) + (cfun (n + c - m) : ENat) := h
    _ ≤ KPPlain U (natCode m) + (((Finset.range (2 * c + 1)).sup cfun : ℕ) : ENat) := by
        gcongr
        exact_mod_cast Finset.le_sup (f := cfun) (Finset.mem_range.mpr hjlt)

/-! ### The upper half -/

/-- **Theorem 1.7.2, second assertion, upper direction.** For every window width `c`
there is a constant `C` with `2^{-n} · windowCount U n c ≤ 2^C · 2^{-K(n)}` for all
`n`. No hypothesis on `n` is needed. -/
theorem windowCount_le_complexityWeight (U : Map) (hU : IsOptimalPrefixConditional U)
    (c : ℕ) :
    ∃ C : ℕ, ∀ n : ℕ,
      (2 : ℝ≥0∞)⁻¹ ^ n * (windowCount U n c : ℝ≥0∞)
        ≤ (2 : ℝ≥0∞) ^ C * complexityWeight (KPPlain U (natCode n)) := by
  obtain ⟨c₁, hc₁⟩ := haltCount_le_complexityWeight U hU
  obtain ⟨s, hs⟩ := KPPlain_natCode_shift_le U hU c
  refine ⟨2 * c + 1 + (c₁ + c + s), fun n ↦ ?_⟩
  -- Each halting count in the window is bounded in terms of `K(n)`.
  have hterm : ∀ m ∈ Finset.Icc (n - c) (n + c),
      (haltCount U m : ℝ≥0∞)
        ≤ (2 : ℝ≥0∞) ^ (c₁ + c + s)
            * ((2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (natCode n))) := by
    intro m hm
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hm
    -- `|D_m| ≤ 2^{c₁} · 2^m · 2^{-K(m)}`.
    have h1 : (haltCount U m : ℝ≥0∞)
        ≤ (2 : ℝ≥0∞) ^ m * ((2 : ℝ≥0∞) ^ c₁ * complexityWeight (KPPlain U (natCode m))) :=
      le_two_pow_mul_of_inv_two_pow_mul_le (hc₁ m)
    -- `2^{-K(m)} ≤ 2^s · 2^{-K(n)}` from the shift bound.
    have h2 : complexityWeight (KPPlain U (natCode m))
        ≤ (2 : ℝ≥0∞) ^ s * complexityWeight (KPPlain U (natCode n)) := by
      have h := complexityWeight_le_of_le (hs m n (by omega) hhi)
      rw [complexityWeight_add_nat, mul_comm] at h
      exact le_two_pow_mul_of_inv_two_pow_mul_le h
    -- `2^m ≤ 2^{n + c}`.
    have h3 : (2 : ℝ≥0∞) ^ m ≤ (2 : ℝ≥0∞) ^ (n + c) := by
      gcongr
      · exact one_le_two
    calc (haltCount U m : ℝ≥0∞)
        ≤ (2 : ℝ≥0∞) ^ m * ((2 : ℝ≥0∞) ^ c₁ * complexityWeight (KPPlain U (natCode m))) := h1
      _ ≤ (2 : ℝ≥0∞) ^ (n + c)
            * ((2 : ℝ≥0∞) ^ c₁ * ((2 : ℝ≥0∞) ^ s * complexityWeight (KPPlain U (natCode n)))) := by
          gcongr
      _ = (2 : ℝ≥0∞) ^ (c₁ + c + s)
            * ((2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (natCode n))) := by
          rw [pow_add, pow_add, pow_add]; ring
  -- The window has at most `2c + 1 ≤ 2^{2c+1}` lengths.
  have hcard : ((Finset.Icc (n - c) (n + c)).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (2 * c + 1) := by
    have h1 : (Finset.Icc (n - c) (n + c)).card ≤ 2 * c + 1 := by
      rw [Nat.card_Icc]; omega
    have h2 : 2 * c + 1 ≤ 2 ^ (2 * c + 1) := (Nat.lt_two_pow_self).le
    exact_mod_cast h1.trans h2
  -- Sum the termwise bounds.
  have hsum : (windowCount U n c : ℝ≥0∞)
      ≤ (2 : ℝ≥0∞) ^ (2 * c + 1 + (c₁ + c + s))
          * ((2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (natCode n))) := by
    calc (windowCount U n c : ℝ≥0∞)
        ≤ ((∑ m ∈ Finset.Icc (n - c) (n + c), haltCount U m : ℕ) : ℝ≥0∞) := by
          exact_mod_cast windowCount_le_sum_haltCount U n c
      _ = ∑ m ∈ Finset.Icc (n - c) (n + c), (haltCount U m : ℝ≥0∞) := by push_cast; rfl
      _ ≤ ∑ m ∈ Finset.Icc (n - c) (n + c), (2 : ℝ≥0∞) ^ (c₁ + c + s)
            * ((2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (natCode n))) :=
          Finset.sum_le_sum hterm
      _ = ((Finset.Icc (n - c) (n + c)).card : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (c₁ + c + s)
            * ((2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (natCode n)))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ≥0∞) ^ (2 * c + 1) * ((2 : ℝ≥0∞) ^ (c₁ + c + s)
            * ((2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (natCode n)))) := by
          gcongr
      _ = (2 : ℝ≥0∞) ^ (2 * c + 1 + (c₁ + c + s))
            * ((2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (natCode n))) := by
          ring
  -- Multiply by `2^{-n}` and cancel `2^{-n} · 2^n`.
  have hcancel : (2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ n = 1 := by
    rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  calc (2 : ℝ≥0∞)⁻¹ ^ n * (windowCount U n c : ℝ≥0∞)
      ≤ (2 : ℝ≥0∞)⁻¹ ^ n * ((2 : ℝ≥0∞) ^ (2 * c + 1 + (c₁ + c + s))
          * ((2 : ℝ≥0∞) ^ n * complexityWeight (KPPlain U (natCode n)))) := by gcongr
    _ = (2 : ℝ≥0∞) ^ (2 * c + 1 + (c₁ + c + s)) * complexityWeight (KPPlain U (natCode n))
          * ((2 : ℝ≥0∞)⁻¹ ^ n * (2 : ℝ≥0∞) ^ n) := by ring
    _ = (2 : ℝ≥0∞) ^ (2 * c + 1 + (c₁ + c + s)) * complexityWeight (KPPlain U (natCode n)) := by
        rw [hcancel, mul_one]

end Kolmogorov
