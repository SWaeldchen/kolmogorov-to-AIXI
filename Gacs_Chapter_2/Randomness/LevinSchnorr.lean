/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.PrefixFreeMass
import Gacs_Chapter_2.Randomness.UniversalTest

/-!
# Randomness and complexity on sequences (Gács Theorems 2.3.1, 2.3.3, 2.3.4, Cor. 2.3.30)

Fix a computable probability measure `P` on sequences and an optimal prefix machine `U`.
Write `w(x) = 2^{-K(x)}` and

  `R(ξ) = sup_n w(ξ_{1:n}) / P(ξ_{1:n})`,

the multiplicative form of Gács' `sup_n (−log P(ξ_{1:n}) − K(ξ_{1:n}))`.

## The key lemma (`seqVal_le_of_isIntegrableSeqTest`)

Every integrable test `T` on sequences satisfies `T(ξ) ≤ 2^c R(ξ)`. This is the hard half
of Theorem 2.3.4, Gács' "proof of `≤`" after [GacsExact80, Thm 5.2]. Gács decomposes
`2^{⌈d⌉}` as a supremum of `2^{k_i} 1_{y_i}` with increasing `k_i` along every sequence and
leaves the bookkeeping implicit. We make it explicit with **dyadic levels**:

* `pmApprox a s z = max_{y ⊑ z} a_s(y)` turns a stage approximation of `T` into one that is
  monotone along prefixes at every stage.
* `hitB a k z`: level `k` is reached at `z`, at stage `|z|`: `2^{k+1} < pmApprox a |z| z`.
  Decidable, monotone along prefixes, implies `2^{k+1} < T(z)`, and every sequence passing
  through `{T > 2^{k+1}}` eventually hits.
* `firstB a k z`: `z` hits level `k` and no proper prefix does. For each `k` these strings
  form a decidable **prefix-free** generating set of `{T > 2^{k+1}}`.
* `γ(z) = ∑_{k : firstB a k z} 2^k` (`gamN`) is computable, and the layer cake
  (`tsum_levels_le`) together with prefix-freeness gives `∑_z P(z) γ(z) ≤ ∫ T dP ≤ 1`.
  So `P·γ` is a lower semicomputable semimeasure and the coding theorem yields
  `γ ≤ 2^c w / P`.
* Along a sequence, `T(ξ_{1:n}) > 2^{k+1}` produces a prefix `y` with `γ(y) ≥ 2^k`; the
  converse layer cake (`le_of_forall_levels`) finishes.

## Consequences

* **Theorem 2.3.3** (`canonicalSeqTest_isUniversal`): `canonicalSeqTest U P =
  max_{y ⊑ ·} w(y)/P(y)` is a universal integrable test; its value along `ξ` is exactly
  `R(ξ)` (`seqVal_canonicalSeqTest`). Integrability is the easy half of Theorem 2.3.4:
  regroup the level sums by prefixes (`sum_ext_take_mul`) and use Kraft.
* **Theorem 2.3.4** (`universalSeqTest_equiv`): every universal integrable test is within a
  constant factor of `R`.
* **Theorem 2.3.1** (`isConstructiveNull_universalNull`, `subset_universalNull`): the set
  `{ξ : R(ξ) = ∞}` is a constructive null set containing every constructive null set.
  Hence `ξ` is `P`-random iff `R(ξ) < ∞` (`isRandomSeq_iff`).
* **Corollary 2.3.30** (`uniform_universalSeqTest_equiv`) and the **Levin–Schnorr
  theorem** (`isRandomSeq_uniform_iff`): `ξ` is random for the coin-tossing measure iff
  `n ≤ K(ξ_{1:n}) + c` for some `c` and all `n`.

All constants depend on `P` (and on the test); the `K(P)` bookkeeping of Gács' Theorem 2.3.3
is not formalized here.
-/

namespace Kolmogorov.Randomness

open scoped ENNReal

/-! ### Small facts -/

theorem ComputableSeqMeasure.mass_le_one (P : ComputableSeqMeasure) (x : BitString) :
    P.mass x ≤ 1 := by
  rw [← P.root, ← sum_ext_eq P.additive [] x.length]
  exact Finset.single_le_sum (f := P.mass) (fun _ _ ↦ zero_le)
    (mem_ext.mpr ⟨List.nil_prefix, by simp⟩)

theorem ComputableSeqMeasure.mass_ne_top (P : ComputableSeqMeasure) (x : BitString) :
    P.mass x ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (P.mass_le_one x)

theorem prefixComplexityWeight_ne_zero_of_optimal (U : Map) (hU : IsOptimalPrefixConditional U)
    (x : BitString) : prefixComplexityWeight U x ≠ 0 := by
  unfold prefixComplexityWeight
  obtain ⟨k, hk⟩ : ∃ k : ℕ, KP U x [] = (k : ENat) :=
    ⟨_, (ENat.coe_toNat (KP_ne_top_of_optimal U hU x [])).symm⟩
  rw [hk, complexityWeight_coe]
  exact pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)

/-- From `2^{-c} p g ≤ w` (domination) to `g ≤ 2^c w / p`. -/
theorem le_two_pow_mul_div {g p w : ℝ≥0∞} {c : ℕ} (hw : w ≠ 0) (hp : p ≠ ⊤)
    (h : 2⁻¹ ^ c * (p * g) ≤ w) : g ≤ 2 ^ c * (w / p) := by
  rcases eq_or_ne p 0 with hp0 | hp0
  · rw [hp0, ENNReal.div_zero hw, ENNReal.mul_top (two_pow_ne_zero' c)]; exact le_top
  · rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hp0) (Or.inl hp)]
    calc g * p = 2 ^ c * (2⁻¹ ^ c * (p * g)) := by
          rw [← mul_assoc, ← ENNReal.inv_pow,
            ENNReal.mul_inv_cancel (two_pow_ne_zero' c) (two_pow_ne_top' c), one_mul, mul_comm]
      _ ≤ 2 ^ c * w := by gcongr

theorem dyadicValue_mul_two_pow (n s : ℕ) : dyadicValue (n * 2 ^ s) s = n := by
  unfold dyadicValue
  push_cast
  rw [mul_div_assoc, ENNReal.div_self (two_pow_ne_zero' s) (two_pow_ne_top' s), mul_one]

/-- A computable natural-valued function is lower semicomputable. -/
theorem isLSC₁_natCast {g : BitString → ℕ} (hg : Computable g) :
    IsLSC₁ (fun x ↦ (g x : ℝ≥0∞)) := by
  refine ⟨fun s x ↦ g x * 2 ^ s, fun s x ↦ ?_, fun x ↦ ?_, ?_⟩
  · rw [dyadicValue_mul_two_pow, dyadicValue_mul_two_pow]
  · simp only [dyadicValue_mul_two_pow, iSup_const]
  · exact Primrec.nat_mul.to_comp.comp (hg.comp Computable.snd)
      (natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst)

theorem take_seqTake (ξ : Seq) {j n : ℕ} (h : j ≤ n) : (seqTake ξ n).take j = seqTake ξ j := by
  have := List.prefix_iff_eq_take.mp (seqTake_prefix (ξ := ξ) h)
  rw [length_seqTake] at this
  exact this.symm

/-! ### Stage approximations made monotone along prefixes -/

/-- `max_{k ≤ |z|} a_s(z_{1:k})`. -/
def pmApprox (a : ℕ → BitString → ℕ) (s : ℕ) (z : BitString) : ℕ :=
  (Finset.range (z.length + 1)).sup (fun k ↦ a s (z.take k))

theorem le_pmApprox (a : ℕ → BitString → ℕ) (s : ℕ) {y z : BitString} (h : y <+: z) :
    a s y ≤ pmApprox a s z := by
  have hy : y = z.take y.length := List.prefix_iff_eq_take.mp h
  have hlen := h.length_le
  unfold pmApprox
  rw [hy]
  exact Finset.le_sup (f := fun k ↦ a s (z.take k))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa using hlen)))

theorem pmApprox_mono_prefix (a : ℕ → BitString → ℕ) (s : ℕ) {y z : BitString}
    (h : y <+: z) : pmApprox a s y ≤ pmApprox a s z :=
  Finset.sup_le fun k _ ↦ le_pmApprox a s ((List.take_prefix k y).trans h)

theorem pmApprox_computable {a : ℕ → BitString → ℕ}
    (ha : Computable (fun p : ℕ × BitString ↦ a p.1 p.2)) :
    Computable (fun p : ℕ × BitString ↦ pmApprox a p.1 p.2) := by
  have hg : Computable (fun q : (ℕ × BitString) × ℕ ↦ a q.1.1 (q.1.2.take q.2)) :=
    (ha.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (primrec_list_take.to_comp.comp (Computable.snd.comp Computable.fst)
        Computable.snd))).of_eq (fun _ ↦ rfl)
  exact computable_finset_range_sup (fun p : ℕ × BitString ↦ p.2.length + 1)
    (fun (p : ℕ × BitString) k ↦ a p.1 (p.2.take k))
    (Computable.succ.comp (Computable.list_length.comp Computable.snd)) hg

section Approx

variable {T : BitString → ℝ≥0∞} {a : ℕ → BitString → ℕ}

theorem dyadic_pmApprox_le (hsup : ∀ x, ⨆ s, dyadicValue (a s x) s = T x) (hT : IsMonoStr T)
    (s : ℕ) (z : BitString) : dyadicValue (pmApprox a s z) s ≤ T z := by
  unfold pmApprox
  rw [dyadicValue_finset_sup _ ⟨0, by simp⟩]
  refine Finset.sup_le fun k _ ↦ ?_
  calc dyadicValue (a s (z.take k)) s ≤ T (z.take k) := by
        rw [← hsup]; exact le_iSup (fun s ↦ dyadicValue (a s (z.take k)) s) s
    _ ≤ T z := hT _ _ (List.take_prefix k z)

theorem dyadic_pmApprox_mono
    (hmono : ∀ s x, dyadicValue (a s x) s ≤ dyadicValue (a (s + 1) x) (s + 1))
    (z : BitString) : Monotone (fun s ↦ dyadicValue (pmApprox a s z) s) := by
  refine monotone_nat_of_le_succ fun s ↦ ?_
  change dyadicValue (pmApprox a s z) s ≤ dyadicValue (pmApprox a (s + 1) z) (s + 1)
  unfold pmApprox
  rw [dyadicValue_finset_sup _ ⟨0, by simp⟩, dyadicValue_finset_sup _ ⟨0, by simp⟩]
  exact Finset.sup_mono_fun fun k _ ↦ hmono s _

theorem le_iSup_dyadic_pmApprox (hsup : ∀ x, ⨆ s, dyadicValue (a s x) s = T x)
    (z : BitString) : T z ≤ ⨆ s, dyadicValue (pmApprox a s z) s := by
  rw [← hsup z]
  refine iSup_mono fun s ↦ ?_
  unfold dyadicValue
  gcongr
  exact_mod_cast le_pmApprox a s List.prefix_rfl

end Approx

/-! ### Dyadic levels and their first hits -/

/-- Level `k` is reached at `z` at stage `|z|`: `2^{k+1} < max_{y ⊑ z} T_{|z|}(y)`. -/
def hitB (a : ℕ → BitString → ℕ) (k : ℕ) (z : BitString) : Bool :=
  decide (2 ^ (k + 1 + z.length) < pmApprox a z.length z)

/-- `z` reaches level `k` and no proper prefix of `z` does. -/
def firstB (a : ℕ → BitString → ℕ) (k : ℕ) (z : BitString) : Bool :=
  hitB a k z &&
    decide ((∑ j ∈ Finset.range z.length, if hitB a k (z.take j) then 1 else 0) = 0)

/-- `γ(z) = ∑_{k : z first reaches level k} 2^k`, a finite sum. -/
def gamN (a : ℕ → BitString → ℕ) (z : BitString) : ℕ :=
  ∑ k ∈ Finset.range (pmApprox a z.length z), if firstB a k z then 2 ^ k else 0

theorem hitB_iff (a : ℕ → BitString → ℕ) (k : ℕ) (z : BitString) :
    hitB a k z = true ↔
      (2 : ℝ≥0∞) ^ (k + 1) < dyadicValue (pmApprox a z.length z) z.length := by
  rw [hitB, decide_eq_true_iff, ← dyadicValue_two_pow_zero, dyadicValue_lt_dyadicValue_iff,
    pow_zero, mul_one, ← pow_add]

theorem firstB_iff (a : ℕ → BitString → ℕ) (k : ℕ) (z : BitString) :
    firstB a k z = true ↔
      hitB a k z = true ∧ ∀ j < z.length, hitB a k (z.take j) = false := by
  simp only [firstB, Bool.and_eq_true, decide_eq_true_eq, Finset.sum_eq_zero_iff,
    Finset.mem_range, ite_eq_right_iff, one_ne_zero, imp_false, Bool.not_eq_true]

theorem lt_of_hitB {a : ℕ → BitString → ℕ} {k : ℕ} {z : BitString} (h : hitB a k z = true) :
    k < pmApprox a z.length z := by
  unfold hitB at h
  rw [decide_eq_true_iff] at h
  calc k < 2 ^ k := Nat.lt_two_pow_self
    _ ≤ 2 ^ (k + 1 + z.length) := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ < _ := h

section Levels

variable {T : BitString → ℝ≥0∞} {a : ℕ → BitString → ℕ}

theorem lt_of_hitB_true (hsup : ∀ x, ⨆ s, dyadicValue (a s x) s = T x) (hT : IsMonoStr T)
    {k : ℕ} {z : BitString} (h : hitB a k z = true) : (2 : ℝ≥0∞) ^ (k + 1) < T z :=
  ((hitB_iff a k z).mp h).trans_le (dyadic_pmApprox_le hsup hT _ z)

theorem hitB_mono
    (hmono : ∀ s x, dyadicValue (a s x) s ≤ dyadicValue (a (s + 1) x) (s + 1))
    {k : ℕ} {y z : BitString} (hyz : y <+: z) (h : hitB a k y = true) : hitB a k z = true := by
  rw [hitB_iff] at h ⊢
  calc (2 : ℝ≥0∞) ^ (k + 1) < dyadicValue (pmApprox a y.length y) y.length := h
    _ ≤ dyadicValue (pmApprox a z.length y) z.length :=
        dyadic_pmApprox_mono hmono y hyz.length_le
    _ ≤ dyadicValue (pmApprox a z.length z) z.length := by
        unfold dyadicValue
        gcongr
        exact_mod_cast pmApprox_mono_prefix a _ hyz

theorem exists_hitB
    (hmono : ∀ s x, dyadicValue (a s x) s ≤ dyadicValue (a (s + 1) x) (s + 1))
    (hsup : ∀ x, ⨆ s, dyadicValue (a s x) s = T x) {k : ℕ} {y : BitString} {ξ : Seq}
    (hy : IsPrefixOfSeq y ξ) (hlt : (2 : ℝ≥0∞) ^ (k + 1) < T y) :
    ∃ N, hitB a k (seqTake ξ N) = true := by
  obtain ⟨s, hs⟩ := lt_iSup_iff.mp (hlt.trans_le (le_iSup_dyadic_pmApprox hsup y))
  set N := max s y.length
  have hyz : y <+: seqTake ξ N :=
    prefix_of_isPrefixOfSeq hy (isPrefixOfSeq_seqTake ξ N) (by simp [N])
  refine ⟨N, (hitB_iff a k _).mpr ?_⟩
  rw [length_seqTake]
  calc (2 : ℝ≥0∞) ^ (k + 1) < dyadicValue (pmApprox a s y) s := hs
    _ ≤ dyadicValue (pmApprox a N y) N := dyadic_pmApprox_mono hmono y (le_max_left _ _)
    _ ≤ dyadicValue (pmApprox a N (seqTake ξ N)) N := by
        unfold dyadicValue
        gcongr
        exact_mod_cast pmApprox_mono_prefix a _ hyz

end Levels

theorem firstB_prefixFree {a : ℕ → BitString → ℕ} {k : ℕ} {y z : BitString}
    (hy : firstB a k y = true) (hz : firstB a k z = true) (hyz : y <+: z) : y = z := by
  by_contra hne
  have hlt : y.length < z.length := by
    rcases lt_or_eq_of_le hyz.length_le with h | h
    · exact h
    · exact absurd (hyz.eq_of_length h) hne
  have htake : z.take y.length = y := (List.prefix_iff_eq_take.mp hyz).symm
  have h1 := ((firstB_iff a k z).mp hz).2 y.length hlt
  rw [htake, ((firstB_iff a k y).mp hy).1] at h1
  exact Bool.noConfusion h1

theorem exists_firstB {a : ℕ → BitString → ℕ} {k : ℕ} {ξ : Seq} {N : ℕ}
    (h : hitB a k (seqTake ξ N) = true) : ∃ n ≤ N, firstB a k (seqTake ξ n) = true := by
  classical
  have hex : ∃ n, hitB a k (seqTake ξ n) = true := ⟨N, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex h, (firstB_iff a k _).mpr ⟨Nat.find_spec hex, ?_⟩⟩
  intro j hj
  rw [length_seqTake] at hj
  rw [take_seqTake ξ hj.le]
  exact Bool.eq_false_iff.mpr (Nat.find_min hex hj)

theorem gamN_eq_tsum (a : ℕ → BitString → ℕ) (z : BitString) :
    (gamN a z : ℝ≥0∞) = ∑' k, if firstB a k z then (2 : ℝ≥0∞) ^ k else 0 := by
  have hz : ∀ k ∉ Finset.range (pmApprox a z.length z),
      (if firstB a k z then (2 : ℝ≥0∞) ^ k else 0) = 0 := fun k hk ↦ by
    rw [if_neg]
    intro hf
    exact hk (Finset.mem_range.mpr (lt_of_hitB ((firstB_iff a k z).mp hf).1))
  rw [tsum_eq_sum hz]
  unfold gamN
  rw [Nat.cast_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  split_ifs <;> simp

theorem two_pow_le_gamN {a : ℕ → BitString → ℕ} {k : ℕ} {z : BitString}
    (h : firstB a k z = true) : (2 : ℝ≥0∞) ^ k ≤ gamN a z := by
  rw [gamN_eq_tsum]
  calc (2 : ℝ≥0∞) ^ k = if firstB a k z then (2 : ℝ≥0∞) ^ k else 0 := by rw [if_pos h]
    _ ≤ _ := ENNReal.le_tsum (f := fun k ↦ if firstB a k z then (2 : ℝ≥0∞) ^ k else 0) k

/-! ### Computability of `γ` -/

theorem hitB_computable {a : ℕ → BitString → ℕ}
    (ha : Computable (fun p : ℕ × BitString ↦ a p.1 p.2)) :
    Computable (fun p : ℕ × BitString ↦ hitB a p.1 p.2) := by
  have hpm := (pmApprox_computable ha).comp
    (Computable.pair (Computable.list_length.comp (Computable.snd (α := ℕ) (β := BitString)))
      (Computable.snd (α := ℕ) (β := BitString)))
  have hl := natPow_primrec.comp (Primrec.const 2)
    (Primrec.nat_add.comp (Primrec.succ.comp Primrec.fst)
      (Primrec.list_length.comp (Primrec.snd (α := ℕ) (β := BitString))))
  have h := natLt_primrec.to_comp.comp (Computable.pair hl.to_comp hpm)
  exact h.of_eq fun _ ↦ rfl

theorem firstB_computable {a : ℕ → BitString → ℕ}
    (ha : Computable (fun p : ℕ × BitString ↦ a p.1 p.2)) :
    Computable (fun p : ℕ × BitString ↦ firstB a p.1 p.2) := by
  have hh := hitB_computable ha
  have hterm : Computable₂ (fun (p : ℕ × BitString) (j : ℕ) ↦
      if hitB a p.1 (p.2.take j) then 1 else 0) := by
    have h1 := hh.comp (Computable.pair (Computable.fst.comp Computable.fst)
      (primrec_list_take.to_comp.comp (Computable.snd.comp Computable.fst)
        (Computable.snd (α := ℕ × BitString) (β := ℕ))))
    have h2 := Computable.cond h1 (Computable.const 1) (Computable.const 0)
    exact h2.of_eq fun q ↦ by dsimp only; cases hitB a q.1.1 (q.1.2.take q.2) <;> rfl
  have hsum := computable_range_sum _ hterm (fun p ↦ p.2.length)
    (Computable.list_length.comp Computable.snd)
  have hz := (Kolmogorov.Randomness.natLe_primrec.to_comp.comp
    (Computable.pair hsum (Computable.const 0)))
  have h := Primrec.and.to_comp.comp hh hz
  exact h.of_eq fun p ↦ by simp [firstB]

theorem gamN_computable {a : ℕ → BitString → ℕ}
    (ha : Computable (fun p : ℕ × BitString ↦ a p.1 p.2)) : Computable (gamN a) := by
  have hterm : Computable₂ (fun (z : BitString) (k : ℕ) ↦ if firstB a k z then 2 ^ k else 0) := by
    have h1 := (firstB_computable ha).comp
      (Computable.pair Computable.snd (Computable.fst (α := BitString) (β := ℕ)))
    have h2 := Computable.cond h1
      (natPow_primrec.to_comp.comp (Computable.const 2) Computable.snd) (Computable.const 0)
    exact h2.of_eq fun q ↦ by dsimp only; cases firstB a q.2 q.1 <;> rfl
  have hb := (pmApprox_computable ha).comp
    (Computable.pair Computable.list_length (Computable.id (α := BitString)))
  have h := computable_range_sum _ hterm (fun z ↦ pmApprox a z.length z) hb
  exact h.of_eq fun _ ↦ rfl

/-! ### The layer cake: `∑ P γ ≤ ∫ T dP` -/

section LayerCake

variable {P : ComputableSeqMeasure} {T : BitString → ℝ≥0∞} {a : ℕ → BitString → ℕ}

theorem sum_upTo_mul_gamN_le (hsup : ∀ x, ⨆ s, dyadicValue (a s x) s = T x)
    (hT : IsMonoStr T) (n : ℕ) :
    ∑ z ∈ upTo n, P.mass z * (gamN a z : ℝ≥0∞) ≤ levelIntegral P T n := by
  have hk : ∀ k : ℕ, ∑ z ∈ upTo n, P.mass z * (if firstB a k z then (2 : ℝ≥0∞) ^ k else 0)
      ≤ ∑ w ∈ ext [] n,
          P.mass w * (if (2 : ℝ≥0∞) ^ (k + 1) < T w then (2 : ℝ≥0∞) ^ k else 0) := by
    intro k
    obtain ⟨S, hS⟩ : ∃ S, S = (upTo n).filter (fun z ↦ firstB a k z = true) := ⟨_, rfl⟩
    have hpf : ∀ x ∈ S, ∀ y ∈ S, x <+: y → x = y := fun x hx y hy hxy ↦ by
      rw [hS] at hx hy
      exact firstB_prefixFree (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hy).2 hxy
    have hlen : ∀ x ∈ S, x.length ≤ n := fun x hx ↦ by
      rw [hS] at hx; exact mem_upTo.mp (Finset.mem_filter.mp hx).1
    calc ∑ z ∈ upTo n, P.mass z * (if firstB a k z then (2 : ℝ≥0∞) ^ k else 0)
        = (∑ z ∈ S, P.mass z) * 2 ^ k := by
          rw [hS, Finset.sum_mul, Finset.sum_filter]
          refine Finset.sum_congr rfl fun z _ ↦ ?_
          split_ifs <;> simp
      _ ≤ levelMass P.mass (S : Set BitString) n * 2 ^ k :=
          mul_le_mul' (sum_le_levelMass_of_prefixFree P.additive S hpf hlen) le_rfl
      _ ≤ _ := by
          unfold levelMass
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun w _ ↦ ?_
          split_ifs with h1 h2
          · exact le_rfl
          · exfalso
            obtain ⟨x, hx, hxw⟩ := h1
            rw [Finset.mem_coe, hS] at hx
            exact h2 ((lt_of_hitB_true hsup hT
              ((firstB_iff a k x).mp (Finset.mem_filter.mp hx).2).1).trans_le (hT x w hxw))
          · simp
          · simp
  calc ∑ z ∈ upTo n, P.mass z * (gamN a z : ℝ≥0∞)
      = ∑ z ∈ upTo n, ∑' k, P.mass z * (if firstB a k z then (2 : ℝ≥0∞) ^ k else 0) := by
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        rw [gamN_eq_tsum, ENNReal.tsum_mul_left]
    _ = ∑' k, ∑ z ∈ upTo n, P.mass z * (if firstB a k z then (2 : ℝ≥0∞) ^ k else 0) :=
        finsetSum_tsum_comm _ (fun k z ↦ P.mass z * (if firstB a k z then (2 : ℝ≥0∞) ^ k else 0))
    _ ≤ ∑' k, ∑ w ∈ ext [] n,
          P.mass w * (if (2 : ℝ≥0∞) ^ (k + 1) < T w then (2 : ℝ≥0∞) ^ k else 0) :=
        ENNReal.tsum_le_tsum hk
    _ = ∑ w ∈ ext [] n, ∑' k,
          P.mass w * (if (2 : ℝ≥0∞) ^ (k + 1) < T w then (2 : ℝ≥0∞) ^ k else 0) :=
        (finsetSum_tsum_comm _ _).symm
    _ ≤ ∑ w ∈ ext [] n, P.mass w * T w := by
        refine Finset.sum_le_sum fun w _ ↦ ?_
        rw [ENNReal.tsum_mul_left]
        exact mul_le_mul' le_rfl (tsum_levels_le (T w))
    _ = levelIntegral P T n := rfl

theorem tsum_mass_mul_gamN_le (hsup : ∀ x, ⨆ s, dyadicValue (a s x) s = T x)
    (hT : IsMonoStr T) (hint : ∀ n, levelIntegral P T n ≤ 1) :
    ∑' z, P.mass z * (gamN a z : ℝ≥0∞) ≤ 1 := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  calc ∑ z ∈ s, P.mass z * (gamN a z : ℝ≥0∞)
      ≤ ∑ z ∈ upTo (s.sup List.length), P.mass z * (gamN a z : ℝ≥0∞) :=
        Finset.sum_le_sum_of_subset (subset_upTo s)
    _ ≤ levelIntegral P T _ := sum_upTo_mul_gamN_le hsup hT _
    _ ≤ 1 := hint _

end LayerCake

/-! ### The key lemma -/

/-- `R(ξ) = sup_n 2^{-K(ξ_{1:n})} / P(ξ_{1:n})`, the multiplicative form of Gács'
`sup_n (−log P(ξ_{1:n}) − K(ξ_{1:n}))`. -/
noncomputable def complexityRatioSup (U : Map) (P : ComputableSeqMeasure) (ξ : Seq) : ℝ≥0∞ :=
  ⨆ n, prefixComplexityWeight U (seqTake ξ n) / P.mass (seqTake ξ n)

/-- **Key lemma (Gács Theorem 2.3.4, `≤` direction).** Every integrable test on sequences is
dominated along every sequence by `sup_n 2^{-K(ξ_{1:n})} / P(ξ_{1:n})`. -/
theorem seqVal_le_of_isIntegrableSeqTest (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableSeqMeasure) {T : BitString → ℝ≥0∞} (hT : IsIntegrableSeqTest P T) :
    ∃ c : ℕ, ∀ ξ, seqVal T ξ ≤ 2 ^ c * complexityRatioSup U P ξ := by
  obtain ⟨⟨a, hmono, hsup, ha⟩, hTm, hint⟩ := hT
  -- `ν = P γ` is a lower semicomputable discrete semimeasure.
  have hν : IsLowerSemicomputableSemimeasure (fun z ↦ P.mass z * (gamN a z : ℝ≥0∞)) :=
    ⟨tsum_mass_mul_gamN_le hsup hTm hint,
      (P.computable.isLSC₁.mul (isLSC₁_natCast (gamN_computable ha))).toCond⟩
  obtain ⟨c, hc⟩ := lowerSemicomputableSemimeasure_le_prefixComplexityWeight hν hU
  have hγ : ∀ z, (gamN a z : ℝ≥0∞) ≤
      2 ^ c * (prefixComplexityWeight U z / P.mass z) := fun z ↦
    le_two_pow_mul_div (prefixComplexityWeight_ne_zero_of_optimal U hU z) (P.mass_ne_top z)
      (hc z)
  -- A positive lower bound for `R` from the empty prefix.
  obtain ⟨c₀, hc₀⟩ := exists_inv_two_pow_le_of_pos
    (pos_iff_ne_zero.mpr (prefixComplexityWeight_ne_zero_of_optimal U hU []))
  refine ⟨max (c₀ + 1) (c + 2) + 1, fun ξ ↦ ?_⟩
  set R := complexityRatioSup U P ξ with hR
  have hR0 : (2 : ℝ≥0∞)⁻¹ ^ c₀ ≤ R := by
    calc (2 : ℝ≥0∞)⁻¹ ^ c₀ ≤ prefixComplexityWeight U [] := hc₀
      _ = prefixComplexityWeight U (seqTake ξ 0) / P.mass (seqTake ξ 0) := by
          simp [seqTake, P.root]
      _ ≤ R := le_iSup (fun n ↦ prefixComplexityWeight U (seqTake ξ n) / P.mass (seqTake ξ n)) 0
  have hlev : ∀ n k, (2 : ℝ≥0∞) ^ (k + 1) < T (seqTake ξ n) → (2 : ℝ≥0∞) ^ k ≤ 2 ^ c * R := by
    intro n k hk
    obtain ⟨N, hN⟩ := exists_hitB hmono hsup (isPrefixOfSeq_seqTake ξ n) hk
    obtain ⟨m, -, hm⟩ := exists_firstB hN
    calc (2 : ℝ≥0∞) ^ k ≤ gamN a (seqTake ξ m) := two_pow_le_gamN hm
      _ ≤ 2 ^ c * (prefixComplexityWeight U (seqTake ξ m) / P.mass (seqTake ξ m)) := hγ _
      _ ≤ 2 ^ c * R := mul_le_mul' le_rfl
          (le_iSup (fun n ↦ prefixComplexityWeight U (seqTake ξ n) / P.mass (seqTake ξ n)) m)
  set M := max (c₀ + 1) (c + 2)
  have h1 : (2 : ℝ≥0∞) ≤ 2 ^ M * R := by
    calc (2 : ℝ≥0∞) = 2 ^ (c₀ + 1) * 2⁻¹ ^ c₀ := by
          rw [pow_succ, mul_comm (2 ^ c₀) 2, mul_assoc, ← ENNReal.inv_pow,
            ENNReal.mul_inv_cancel (two_pow_ne_zero' c₀) (two_pow_ne_top' c₀), mul_one]
      _ ≤ 2 ^ M * R := mul_le_mul' (pow_le_pow_right₀ one_le_two (le_max_left _ _)) hR0
  have h2 : 4 * (2 ^ c * R) ≤ 2 ^ M * R := by
    calc 4 * (2 ^ c * R) = 2 ^ (c + 2) * R := by rw [pow_add]; ring
      _ ≤ 2 ^ M * R := mul_le_mul' (pow_le_pow_right₀ one_le_two (le_max_right _ _)) le_rfl
  refine iSup_le fun n ↦ ?_
  calc T (seqTake ξ n) ≤ 2 + 4 * (2 ^ c * R) := le_of_forall_levels (hlev n)
    _ ≤ 2 ^ M * R + 2 ^ M * R := add_le_add h1 h2
    _ = 2 ^ (M + 1) * R := by rw [pow_succ]; ring

/-! ### Theorem 2.3.3: the universal integrable test on sequences -/

/-- **Gács' `t_P` on sequences**: `max_{y ⊑ z} 2^{-K(y)} / P(y)`. -/
noncomputable def canonicalSeqTest (U : Map) (P : ComputableSeqMeasure) : BitString → ℝ≥0∞ :=
  prefixMax (fun y ↦ prefixComplexityWeight U y / P.mass y)

theorem seqVal_prefixMax (f : BitString → ℝ≥0∞) (ξ : Seq) :
    seqVal (prefixMax f) ξ = ⨆ n, f (seqTake ξ n) := by
  apply le_antisymm
  · refine iSup_le fun n ↦ prefixMax_le f fun y hy ↦ ?_
    rw [eq_seqTake_of_isPrefixOfSeq (IsPrefixOfSeq.of_prefix hy (isPrefixOfSeq_seqTake ξ n))]
    exact le_iSup (fun n ↦ f (seqTake ξ n)) y.length
  · exact iSup_mono fun n ↦ le_prefixMax_self f _

/-- Along a sequence the canonical test is exactly `R(ξ)`. -/
theorem seqVal_canonicalSeqTest (U : Map) (P : ComputableSeqMeasure) (ξ : Seq) :
    seqVal (canonicalSeqTest U P) ξ = complexityRatioSup U P ξ :=
  seqVal_prefixMax _ ξ

/-- Strings of different lengths have disjoint level sets. -/
theorem ext_nil_disjoint {i j : ℕ} (h : i ≠ j) : Disjoint (ext [] i) (ext [] j) := by
  rw [Finset.disjoint_left]
  intro z hi hj
  exact h ((ext_zero_length i hi).symm.trans (ext_zero_length j hj))

/-- **Theorem 2.3.4, `≥` direction / test property**: the canonical test is integrable. -/
theorem levelIntegral_canonicalSeqTest_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableSeqMeasure) (n : ℕ) : levelIntegral P (canonicalSeqTest U P) n ≤ 1 := by
  set f : BitString → ℝ≥0∞ := fun y ↦ prefixComplexityWeight U y / P.mass y with hf
  calc levelIntegral P (canonicalSeqTest U P) n
      ≤ ∑ z ∈ ext [] n, P.mass z * ∑ j ∈ Finset.range (n + 1), f (z.take j) := by
        refine Finset.sum_le_sum fun z hz ↦ mul_le_mul' le_rfl ?_
        unfold canonicalSeqTest prefixMax
        refine Finset.sup_le fun j hj ↦ ?_
        rw [ext_zero_length n hz] at hj
        exact Finset.single_le_sum (f := fun j ↦ f (z.take j)) (fun _ _ ↦ zero_le) hj
    _ = ∑ j ∈ Finset.range (n + 1), ∑ z ∈ ext [] n, f (z.take (([] : BitString).length + j)) *
          P.mass z := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        simp [mul_comm]
    _ = ∑ j ∈ Finset.range (n + 1), ∑ y ∈ ext [] j, f y * P.mass y := by
        refine Finset.sum_congr rfl fun j hj ↦ ?_
        exact sum_ext_take_mul P.additive f j [] n
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
    _ ≤ ∑ j ∈ Finset.range (n + 1), ∑ y ∈ ext [] j, prefixComplexityWeight U y := by
        refine Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun y _ ↦ ?_
        rw [hf, mul_comm]
        exact ENNReal.mul_div_le
    _ = ∑ y ∈ upTo n, prefixComplexityWeight U y := by
        rw [upTo, Finset.sum_biUnion]
        intro i _ j _ hij
        exact ext_nil_disjoint hij
    _ ≤ ∑' y, prefixComplexityWeight U y := ENNReal.sum_le_tsum _
    _ ≤ 1 := KP_kraft_sum_le_one U hU.isPrefixDecompressor []

theorem canonicalSeqTest_isIntegrable (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableSeqMeasure) : IsIntegrableSeqTest P (canonicalSeqTest U P) :=
  ⟨prefixMax_isLSC₁ (((prefixComplexityWeight_isLSC₁ U hU.isDecompressor).mul
      P.computable.inv_isLSC₁).congr (fun x ↦ by rw [div_eq_mul_inv])),
    prefixMax_isMonoStr _, levelIntegral_canonicalSeqTest_le U hU P⟩

/-- **Gács Theorem 2.3.3.** `max_{y ⊑ ·} 2^{-K(y)}/P(y)` is a universal integrable test on
sequences, for every computable probability measure `P`. -/
theorem canonicalSeqTest_isUniversal (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableSeqMeasure) : IsUniversalIntegrableSeqTest P (canonicalSeqTest U P) := by
  refine ⟨canonicalSeqTest_isIntegrable U hU P, fun T hT ↦ ?_⟩
  obtain ⟨c, hc⟩ := seqVal_le_of_isIntegrableSeqTest U hU P hT
  exact ⟨c, fun ξ ↦ by rw [seqVal_canonicalSeqTest]; exact hc ξ⟩

/-! ### Theorem 2.3.4: deficiency of randomness via complexity -/

/-- **Gács Theorem 2.3.4.** Every universal integrable test `T₀` satisfies
`d̄_P(ξ) =⁺ sup_n (−log P(ξ_{1:n}) − K(ξ_{1:n}))`, in multiplicative form. -/
theorem universalSeqTest_equiv (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableSeqMeasure) {T₀ : BitString → ℝ≥0∞} (hT₀ : IsUniversalIntegrableSeqTest P T₀) :
    ∃ c : ℕ, ∀ ξ, seqVal T₀ ξ ≤ 2 ^ c * complexityRatioSup U P ξ ∧
      complexityRatioSup U P ξ ≤ 2 ^ c * seqVal T₀ ξ := by
  obtain ⟨c₁, h₁⟩ := seqVal_le_of_isIntegrableSeqTest U hU P hT₀.1
  obtain ⟨c₂, h₂⟩ := hT₀.2 _ (canonicalSeqTest_isIntegrable U hU P)
  refine ⟨max c₁ c₂, fun ξ ↦ ⟨(h₁ ξ).trans ?_, ?_⟩⟩
  · exact mul_le_mul' (pow_le_pow_right₀ one_le_two (le_max_left _ _)) le_rfl
  · rw [← seqVal_canonicalSeqTest]
    exact (h₂ ξ).trans (mul_le_mul' (pow_le_pow_right₀ one_le_two (le_max_right _ _)) le_rfl)

/-! ### Theorem 2.3.1: the universal constructive null set -/

/-- **Gács Theorem 2.3.1, first half.** `{ξ : R(ξ) = ∞}` is a constructive null set. -/
theorem isConstructiveNull_universalNull (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableSeqMeasure) :
    IsConstructiveNull P.mass {ξ | complexityRatioSup U P ξ = ⊤} := by
  have h := isConstructiveNull_seqVal_top (canonicalSeqTest_isIntegrable U hU P).isMLSeqTest
  simpa only [seqVal_canonicalSeqTest] using h

/-- **Gács Theorem 2.3.1, second half.** Every constructive null set is contained in
`{ξ : R(ξ) = ∞}`: the set of nonrandom sequences is itself a constructive null set. -/
theorem subset_universalNull (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableSeqMeasure) {N : Set Seq} (hN : IsConstructiveNull P.mass N) :
    N ⊆ {ξ | complexityRatioSup U P ξ = ⊤} := by
  obtain ⟨T, hT, hNT⟩ := exists_integrableSeqTest_of_constructiveNull P hN
  obtain ⟨c, hc⟩ := seqVal_le_of_isIntegrableSeqTest U hU P hT
  intro ξ hξ
  have htop : seqVal T ξ = ⊤ := hNT hξ
  by_contra hne
  have := hc ξ
  rw [htop, top_le_iff] at this
  exact ENNReal.mul_ne_top (two_pow_ne_top' c) hne this

/-- **Randomness via complexity.** `ξ` is `P`-random iff `sup_n 2^{-K(ξ_{1:n})}/P(ξ_{1:n})` is
finite. -/
theorem isRandomSeq_iff (U : Map) (hU : IsOptimalPrefixConditional U)
    (P : ComputableSeqMeasure) (ξ : Seq) :
    IsRandomSeq P.mass ξ ↔ complexityRatioSup U P ξ ≠ ⊤ := by
  constructor
  · intro h htop
    exact h _ (isConstructiveNull_universalNull U hU P) htop
  · intro h N hN hξ
    exact h (subset_universalNull U hU P hN hξ)

/-! ### Corollary 2.3.30 and the Levin–Schnorr theorem -/

theorem div_inv_two_pow (w : ℝ≥0∞) (n : ℕ) : w / (2 : ℝ≥0∞)⁻¹ ^ n = 2 ^ n * w := by
  rw [div_eq_mul_inv, ← ENNReal.inv_pow, inv_inv, mul_comm]

theorem complexityRatioSup_uniform (U : Map) (ξ : Seq) :
    complexityRatioSup U uniformSeqMeasure ξ =
      ⨆ n, 2 ^ n * prefixComplexityWeight U (seqTake ξ n) := by
  unfold complexityRatioSup
  refine iSup_congr fun n ↦ ?_
  change prefixComplexityWeight U (seqTake ξ n) / (2 : ℝ≥0∞)⁻¹ ^ (seqTake ξ n).length = _
  rw [length_seqTake, div_inv_two_pow]

/-- **Gács Corollary 2.3.30.** For the uniform measure,
`d̄_λ(ξ) =⁺ sup_n (n − K(ξ_{1:n}))`. -/
theorem uniform_universalSeqTest_equiv (U : Map) (hU : IsOptimalPrefixConditional U)
    {T₀ : BitString → ℝ≥0∞} (hT₀ : IsUniversalIntegrableSeqTest uniformSeqMeasure T₀) :
    ∃ c : ℕ, ∀ ξ, seqVal T₀ ξ ≤ 2 ^ c * ⨆ n, 2 ^ n * prefixComplexityWeight U (seqTake ξ n) ∧
      (⨆ n, 2 ^ n * prefixComplexityWeight U (seqTake ξ n)) ≤ 2 ^ c * seqVal T₀ ξ := by
  obtain ⟨c, hc⟩ := universalSeqTest_equiv U hU uniformSeqMeasure hT₀
  exact ⟨c, fun ξ ↦ by simpa only [complexityRatioSup_uniform] using hc ξ⟩

/-- `2^n · 2^{-K} ≤ 2^c` iff `n ≤ K + c`. -/
theorem two_pow_mul_complexityWeight_le_iff (n c : ℕ) (K : ENat) (hK : K ≠ ⊤) :
    (2 : ℝ≥0∞) ^ n * complexityWeight K ≤ 2 ^ c ↔ (n : ENat) ≤ K + c := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, K = (k : ENat) := ⟨K.toNat, (ENat.coe_toNat hK).symm⟩
  rw [complexityWeight_coe, ← ENNReal.inv_pow, ← div_eq_mul_inv,
    ENNReal.div_le_iff (two_pow_ne_zero' k) (two_pow_ne_top' k), ← pow_add]
  have hcast : ∀ m : ℕ, (2 : ℝ≥0∞) ^ m = ((2 ^ m : ℕ) : ℝ≥0∞) := fun m ↦ by push_cast; rfl
  rw [hcast, hcast, Nat.cast_le, Nat.pow_le_pow_iff_right (by norm_num)]
  constructor
  · intro h; exact_mod_cast (by omega : n ≤ k + c)
  · intro h
    have : n ≤ k + c := by exact_mod_cast h
    omega

/-- **The Levin–Schnorr theorem** (Gács Corollary 2.3.30, in words): an infinite binary
sequence is random for the coin-tossing measure iff the prefix complexity of its initial
segments never drops below their length by more than a constant. -/
theorem isRandomSeq_uniform_iff (U : Map) (hU : IsOptimalPrefixConditional U) (ξ : Seq) :
    IsRandomSeq uniformSeqMeasure.mass ξ ↔
      ∃ c : ℕ, ∀ n : ℕ, (n : ENat) ≤ KP U (seqTake ξ n) [] + c := by
  rw [isRandomSeq_iff U hU, complexityRatioSup_uniform]
  have hK : ∀ n, KP U (seqTake ξ n) [] ≠ ⊤ := fun n ↦ KP_ne_top_of_optimal U hU _ []
  constructor
  · intro h
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt h
    refine ⟨N, fun n ↦ (two_pow_mul_complexityWeight_le_iff n N _ (hK n)).mp ?_⟩
    calc (2 : ℝ≥0∞) ^ n * complexityWeight (KP U (seqTake ξ n) [])
        ≤ ⨆ n, 2 ^ n * prefixComplexityWeight U (seqTake ξ n) :=
          le_iSup (fun n ↦ 2 ^ n * prefixComplexityWeight U (seqTake ξ n)) n
      _ ≤ N := hN.le
      _ ≤ 2 ^ N := by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
  · rintro ⟨c, hc⟩
    refine ne_top_of_le_ne_top (two_pow_ne_top' c) (iSup_le fun n ↦ ?_)
    exact (two_pow_mul_complexityWeight_le_iff n c _ (hK n)).mpr (hc n)

end Kolmogorov.Randomness
