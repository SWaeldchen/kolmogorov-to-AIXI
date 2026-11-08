/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Turing.RecursiveIn
import Gacs_Chapter_3.Halting.RarelyComplex
import Gacs_Chapter_3.Oracle.Defs
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Gács Theorem 3.2.3: `Ω` and `χ` are Turing-equivalent

`U` is an exactly universal prefix machine (`IsExactUniversal`, Gács' optimal machine `T`).
Programs are numbered by `idx` (`p ↦ bitsToNat (p ++ [1])`), `χ = chi U` is the indicator of the
halting set `E = domainAt U []`, and `omegaBit U n` is the `(n+1)`-st binary digit of `Ω`
(the last digit of `Ω(1:n+1)`, i.e. `⌊Ω 2^{n+1}⌋ mod 2`, with the clamp of `omegaDigits`).
As Mathlib partial functions `ℕ →. ℕ`:

  **`toPart (chiNat U) ≡ᵀ toPart (omegaBit U)`** (`chi_turingEquivalent_omega`).

## Proof

* **`χ ≤_T Ω`** (`chi_le_omega`). The first `i + 1` digits of `Ω` give `a = ⌊Ω 2^{i+1}⌋`
  (`digitsFold_tableOf`). At the first stage `t` with `Ω^t + 2^{-(i+1)} > a 2^{-(i+1)}`, every
  halting program of length `≤ i` has halted (`halts_of_short`); a program numbered `i` has
  length `< i`. This only uses that `U` is a prefix machine.
* **Many-one completeness** (`exists_reduction`). For any computable `b`, the prefix machine
  `natCode (encode a) ↦ [search for t with b a t]` is simulated by `U` behind a tag, so
  `∃ t, b a t ↔ χ(idx (tag ++ natCode (encode a)))`.
* **`χ` is not computable** (`chi_not_computable`): reduce Mathlib's halting problem.
* **`Ω` is not a dyadic rational** (`omega_ne_dyadic`): otherwise its digits are computable and
  `χ ≤_T Ω` would make `χ` computable.
* **`Ω ≤_T χ`** (`omega_le_chi`). `{(k, N) : k 2^{-N} < Ω}` is r.e., hence reduces to `E`, and
  `⌊Ω 2^N⌋ = #{k ∈ [1, 2^N) : k 2^{-N} < Ω}` because `Ω` is not dyadic
  (`countBelow_lt_omega`).

The reductions go through `turingReducible_of_table` (`RecursiveIn.lean`).
-/

namespace Kolmogorov.Information.Turing

open Kolmogorov
open Kolmogorov.Information.Halting
open Kolmogorov.Information.Oracle (IsExactUniversal)
open Nat.Partrec (Code)
open Encodable
open scoped ENNReal Computability
open Kolmogorov.Randomness (two_pow_ne_zero' two_pow_ne_top' natPow_primrec)

/-! ### The digits of `Ω` -/

/-- The digit number `n + 1` of `Ω` (0-indexed `n`): `⌊Ω 2^{n+1}⌋ mod 2`. -/
noncomputable def omegaBit (U : Map) (n : ℕ) : ℕ := omegaDigits U (n + 1) % 2

theorem omegaDigits_zero (U : Map) : omegaDigits U 0 = 0 := by simp [omegaDigits]

theorem omegaDigits_succ_div (U : Map) (n : ℕ) :
    omegaDigits U (n + 1) / 2 = omegaDigits U n := by
  set x : NNReal := (omega U).toNNReal * 2 ^ n with hx
  have hfl : ⌊(omega U).toNNReal * 2 ^ (n + 1)⌋₊ / 2 = ⌊x⌋₊ := by
    have h := Nat.floor_div_natCast ((omega U).toNNReal * 2 ^ (n + 1)) 2
    rw [← h]
    congr 1
    rw [hx, pow_succ]
    push_cast
    field_simp
  unfold omegaDigits
  rw [← hx]
  have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
  have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  generalize ⌊(omega U).toNNReal * 2 ^ (n + 1)⌋₊ = m at hfl
  rw [hpow]
  omega

theorem omegaDigits_succ (U : Map) (n : ℕ) :
    omegaDigits U (n + 1) = 2 * omegaDigits U n + omegaBit U n := by
  have h := Nat.div_add_mod (omegaDigits U (n + 1)) 2
  rw [omegaDigits_succ_div] at h
  unfold omegaBit
  omega

/-- Reading a binary numeral, most significant digit first. -/
def digitsFold (l : List ℕ) : ℕ := l.foldl (fun acc b ↦ 2 * acc + b) 0

theorem digitsFold_tableOf (U : Map) (n : ℕ) :
    digitsFold (tableOf (omegaBit U) n) = omegaDigits U n := by
  induction n with
  | zero => simp [digitsFold, tableOf, omegaDigits_zero]
  | succ n ih =>
    rw [tableOf_succ, digitsFold, List.foldl_append, ← digitsFold, ih, omegaDigits_succ]
    rfl

theorem digitsFold_primrec : Primrec digitsFold := by
  have h := Primrec.list_foldl (f := fun l : List ℕ ↦ l) (g := fun _ ↦ 0)
    (h := fun _ (p : ℕ × ℕ) ↦ 2 * p.1 + p.2) Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq fun _ ↦ rfl

/-! ### `χ ≤_T Ω` -/

/-- `χ` with values in `{0, 1}`. -/
noncomputable def chiNat (U : Map) (n : ℕ) : ℕ := if chi U n then 1 else 0

theorem chi_iff (U : Map) (i : ℕ) :
    chi U i = true ↔ ∃ p ∈ Halting.haltSet U, idx p = i := by
  simp [chi]

theorem chi_idx (U : Map) (q : BitString) : chi U (idx q) = true ↔ q ∈ Halting.haltSet U := by
  rw [chi_iff]
  exact ⟨fun ⟨p, hp, h⟩ ↦ idx_injective h ▸ hp, fun h ↦ ⟨q, h, rfl⟩⟩

/-- The halting test from a table of digits of `Ω`. -/
def chiTest (c : Code) (i t : ℕ) : ℕ :=
  if (boundedPrograms t).any (fun p ↦ decide (idx p = i) && haltsIn c t p) then 1 else 0

/-- The decision procedure for `χ(i)` from the first digits of `Ω`. -/
def chiFromTable (c : Code) (q : ℕ × List ℕ) : Part ℕ :=
  (rfindB fun t ↦ stageGood c q.2.length (digitsFold q.2) t).map (chiTest c q.1)

theorem chiTest_primrec (c : Code) : Primrec fun r : ℕ × ℕ ↦ chiTest c r.1 r.2 := by
  have hp : Primrec₂ fun (r : ℕ × ℕ) (p : BitString) ↦
      decide (idx p = r.1) && haltsIn c r.2 p := by
    have h1 : Primrec fun s : (ℕ × ℕ) × BitString ↦ decide (idx s.2 = s.1.1) :=
      PrimrecPred.decide (Primrec.eq.comp (idx_primrec.comp Primrec.snd)
        (Primrec.fst.comp Primrec.fst))
    have h2 : Primrec fun s : (ℕ × ℕ) × BitString ↦ haltsIn c s.1.2 s.2 :=
      (haltsIn_primrec c).comp (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
    exact (Primrec.and.comp h1 h2).to₂
  have hany := list_any_primrec (primrec_boundedPrograms.comp Primrec.snd) hp
  exact (Primrec.ite (Primrec.eq.comp hany (Primrec.const true)) (Primrec.const 1)
    (Primrec.const 0)).of_eq fun r ↦ by simp [chiTest]

theorem chiFromTable_partrec (c : Code) : Partrec (chiFromTable c) := by
  have hb : Computable₂ fun (q : ℕ × List ℕ) (t : ℕ) ↦
      stageGood c q.2.length (digitsFold q.2) t :=
    ((stageGood_primrec c).comp (Primrec.pair (Primrec.pair
      (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))
      (digitsFold_primrec.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)).to_comp.to₂
  have hm : Computable₂ fun (q : ℕ × List ℕ) (t : ℕ) ↦ chiTest c q.1 t :=
    ((chiTest_primrec c).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      Primrec.snd)).to_comp.to₂
  exact ((rfindB_partrec hb).map hm).of_eq fun _ ↦ rfl

theorem chiFromTable_eq {U : Map} (hU : IsPrefixMachine U) {c : Code} (hc : IsCodeOf U c)
    (i : ℕ) : toPart (chiNat U) i = chiFromTable c (i, tableOf (omegaBit U) (i + 1)) := by
  unfold chiFromTable toPart
  simp only [length_tableOf, digitsFold_tableOf]
  obtain ⟨t, ht⟩ := exists_mem_rfindB (exists_stageGood hU hc (i + 1))
  have hgood : stageGood c (i + 1) (omegaDigits U (i + 1)) t = true := (mem_rfindB.mp ht).1
  rw [Part.eq_some_iff.mpr (Part.mem_map (chiTest c i) ht)]
  congr 1
  unfold chiTest chiNat
  have hiff : ((boundedPrograms t).any fun p ↦ decide (idx p = i) && haltsIn c t p) = true ↔
      chi U i = true := by
    rw [List.any_eq_true, chi_iff]
    constructor
    · rintro ⟨p, -, hp⟩
      rw [Bool.and_eq_true, decide_eq_true_iff] at hp
      exact ⟨p, mem_domain_of_haltsIn hc hp.2, hp.1⟩
    · rintro ⟨p, hp, rfl⟩
      have hlen : p.length < idx p + 1 := by
        have := (idx_bounds p).1
        have := Nat.lt_two_pow_self (n := p.length)
        omega
      obtain ⟨hb, hh⟩ := halts_of_short hU hc hgood hp hlen
      exact ⟨p, hb, by simp [hh]⟩
  by_cases h : chi U i = true
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg (fun h' ↦ h (hiff.mp h'))]

/-- **`χ ≤_T Ω`.** Only uses that `U` is a prefix decompressor. -/
theorem chi_le_omega {U : Map} (hU : IsPrefixDecompressor U) :
    TuringReducible (toPart (chiNat U)) (toPart (omegaBit U)) := by
  obtain ⟨c, hc⟩ := exists_isCodeOf hU.1
  exact turingReducible_of_table (chiFromTable_partrec c) Computable.succ
    (chiFromTable_eq hU.2 hc)

/-! ### Many-one completeness of the halting set -/

/-- The prefix machine with domain `{natCode (encode a) : ∃ t, b a t}`. -/
noncomputable def reductionMachine {α : Type} [Primcodable α] (b : α → ℕ → Bool) : Map :=
  fun pr ↦ cond (decide (pr.1 = natCode (natOfCode pr.1)))
    ((Part.ofOption (decode (α := α) (natOfCode pr.1))).bind
      fun a ↦ (rfindB (b a)).map fun _ ↦ ([] : BitString))
    Part.none

theorem natCode_primrec' : Primrec natCode :=
  (Primrec.list_append.comp (Primrec.list_replicate.comp Primrec.id (Primrec.const true))
    (Primrec.const [false])).of_eq fun _ ↦ rfl

theorem reductionMachine_isPrefixDecompressor {α : Type} [Primcodable α] {b : α → ℕ → Bool}
    (hb : Computable₂ b) : IsPrefixDecompressor (reductionMachine b) := by
  refine ⟨?_, ?_⟩
  · have hc : Computable fun pr : BitString × BitString ↦
        decide (pr.1 = natCode (natOfCode pr.1)) :=
      (bitStringEq_primrec.comp (Primrec.pair Primrec.fst
        (natCode_primrec'.comp (natOfCode_primrec.comp Primrec.fst)))).to_comp
    have hdec : Computable fun pr : BitString × BitString ↦
        decode (α := α) (natOfCode pr.1) :=
      Computable.decode.comp (natOfCode_primrec.to_comp.comp Computable.fst)
    have hr : Partrec₂ fun (_ : BitString × BitString) (a : α) ↦
        (rfindB (b a)).map fun _ ↦ ([] : BitString) :=
      (((rfindB_partrec hb).comp Computable.snd).map
        ((Computable.const ([] : BitString)).comp Computable.fst).to₂).to₂
    exact Partrec.cond hc ((Computable.ofOption hdec).bind hr) Partrec.none
  · intro y p hp q hq hpq
    have hdom : ∀ r, (reductionMachine b (r, y)).Dom → r = natCode (natOfCode r) := by
      intro r hr
      by_contra hne
      dsimp only [reductionMachine] at hr
      rw [decide_eq_false hne, cond_false] at hr
      exact Part.not_none_dom hr
    rw [hdom p hp, hdom q hq] at hpq ⊢
    rw [natCode_prefix_iff.mp hpq]

theorem reductionMachine_dom {α : Type} [Primcodable α] (b : α → ℕ → Bool) (a : α)
    (y : BitString) :
    (reductionMachine b (natCode (encode a), y)).Dom ↔ ∃ t, b a t = true := by
  simp only [reductionMachine, natOfCode_natCode, decide_true, cond_true, encodek,
    Part.coe_some, Part.bind_some, Part.map_Dom]
  exact ⟨fun h ↦ ⟨_, (mem_rfindB.mp (Part.get_mem h)).1⟩, rfindB_dom⟩

/-- **Many-one completeness of `E`.** Every `Σ₁` predicate reduces to the halting set. -/
theorem exists_reduction {U : Map} (hU : IsExactUniversal U) {α : Type} [Primcodable α]
    {b : α → ℕ → Bool} (hb : Computable₂ b) :
    ∃ tag : BitString, ∀ a, (∃ t, b a t = true) ↔
      chi U (idx (tag ++ natCode (encode a))) = true := by
  obtain ⟨tag, htag⟩ := hU.2 _ (reductionMachine_isPrefixDecompressor hb)
  refine ⟨tag, fun a ↦ ?_⟩
  rw [chi_idx, Halting.haltSet, ← reductionMachine_dom b a []]
  change _ ↔ (U (tag ++ natCode (encode a), [])).Dom
  rw [htag]

/-! ### `χ` is not computable; `Ω` is not dyadic -/

/-- **The halting set of an exactly universal machine is undecidable.** -/
theorem chi_not_computable {U : Map} (hU : IsExactUniversal U) : ¬ Computable (chi U) := by
  intro hchi
  have hb : Computable₂ fun (c : Code) (t : ℕ) ↦ (Code.evaln t c 0).isSome :=
    (Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair Primrec.snd Primrec.fst) (Primrec.const 0)))).to_comp.to₂
  obtain ⟨tag, htag⟩ := exists_reduction hU hb
  apply ComputablePred.halting_problem 0
  rw [ComputablePred.computable_iff]
  refine ⟨fun c ↦ chi U (idx (tag ++ natCode (encode c))), ?_, ?_⟩
  · exact hchi.comp (idx_primrec.to_comp.comp ((Primrec.list_append.comp (Primrec.const tag)
      (natCode_primrec'.comp Primrec.encode)).to_comp))
  · funext c
    rw [← htag]
    apply propext
    constructor
    · intro h
      obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp h
      obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
      exact ⟨k, Option.isSome_iff_exists.mpr ⟨v, hk⟩⟩
    · rintro ⟨k, hk⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hk
      exact Part.dom_iff_mem.mpr ⟨v, Nat.Partrec.Code.evaln_sound hv⟩

theorem omegaDigits_of_eq {U : Map} {N j : ℕ} (hjN : j < 2 ^ N)
    (hΩ : omega U = (j : ℝ≥0∞) * 2⁻¹ ^ N) (n : ℕ) : omegaDigits U n = j * 2 ^ n / 2 ^ N := by
  have htn : (omega U).toNNReal = (j : NNReal) / 2 ^ N := by
    rw [hΩ, ENNReal.toNNReal_mul, ENNReal.toNNReal_pow, ENNReal.toNNReal_inv,
      ENNReal.toNNReal_ofNat, ENNReal.toNNReal_natCast, div_eq_mul_inv, inv_pow]
  have hfl : ⌊(omega U).toNNReal * 2 ^ n⌋₊ = j * 2 ^ n / 2 ^ N := by
    rw [htn, div_mul_eq_mul_div]
    exact_mod_cast Nat.floor_div_eq_div (K := NNReal) (j * 2 ^ n) (2 ^ N)
  unfold omegaDigits
  rw [hfl]
  have hlt : j * 2 ^ n / 2 ^ N < 2 ^ n := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc j * 2 ^ n < 2 ^ N * 2 ^ n := Nat.mul_lt_mul_of_pos_right hjN (by positivity)
      _ = 2 ^ n * 2 ^ N := by ring
  omega

/-- **`Ω` is not a dyadic rational** (below `1`). -/
theorem omega_ne_dyadic {U : Map} (hU : IsExactUniversal U) {N j : ℕ} (hjN : j < 2 ^ N) :
    omega U ≠ (j : ℝ≥0∞) * 2⁻¹ ^ N := by
  intro hΩ
  apply chi_not_computable hU
  have hbit : Computable (omegaBit U) := by
    have h : Primrec fun n : ℕ ↦ j * 2 ^ (n + 1) / 2 ^ N % 2 :=
      Primrec.nat_mod.comp (Primrec.nat_div.comp (Primrec.nat_mul.comp (Primrec.const j)
        (natPow_primrec.comp (Primrec.const 2) Primrec.succ))
        (Primrec.const (2 ^ N))) (Primrec.const 2)
    exact h.to_comp.of_eq fun n ↦ by rw [omegaBit, omegaDigits_of_eq hjN hΩ]
  have hred := chi_le_omega hU.1
  have hpart : Partrec (toPart (chiNat U)) :=
    RecursiveIn.partrec_of_oracle (fun g hg ↦ by rw [Set.mem_singleton_iff.mp hg]; exact hbit)
      hred
  have hcn : Computable (chiNat U) := hpart
  have h : Computable fun n ↦ decide (chiNat U n = 1) :=
    (PrimrecPred.decide (Primrec.eq.comp Primrec.id (Primrec.const 1))).to_comp.comp hcn
  exact h.of_eq fun n ↦ by unfold chiNat; cases chi U n <;> simp

/-! ### `Ω ≤_T χ` -/

theorem inv_pow_lt_iff (k m N t : ℕ) :
    (k : ℝ≥0∞) * 2⁻¹ ^ N < m * 2⁻¹ ^ t ↔ k * 2 ^ t < m * 2 ^ N := by
  have h0 : (2 : ℝ≥0∞) ^ t * 2 ^ N ≠ 0 := mul_ne_zero (two_pow_ne_zero' t) (two_pow_ne_zero' N)
  have ht : (2 : ℝ≥0∞) ^ t * 2 ^ N ≠ ⊤ :=
    ENNReal.mul_ne_top (two_pow_ne_top' t) (two_pow_ne_top' N)
  have hinv : ∀ e : ℕ, (2 : ℝ≥0∞)⁻¹ ^ e * 2 ^ e = 1 := fun e ↦ by
    rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel (two_pow_ne_zero' e) (two_pow_ne_top' e)]
  rw [← ENNReal.mul_lt_mul_iff_left h0 ht]
  have hl : (k : ℝ≥0∞) * 2⁻¹ ^ N * (2 ^ t * 2 ^ N) = ((k * 2 ^ t : ℕ) : ℝ≥0∞) := by
    push_cast
    calc (k : ℝ≥0∞) * 2⁻¹ ^ N * (2 ^ t * 2 ^ N) = k * 2 ^ t * (2⁻¹ ^ N * 2 ^ N) := by ring
      _ = k * 2 ^ t := by rw [hinv, mul_one]
  have hr : (m : ℝ≥0∞) * 2⁻¹ ^ t * (2 ^ t * 2 ^ N) = ((m * 2 ^ N : ℕ) : ℝ≥0∞) := by
    push_cast
    calc (m : ℝ≥0∞) * 2⁻¹ ^ t * (2 ^ t * 2 ^ N) = m * 2 ^ N * (2⁻¹ ^ t * 2 ^ t) := by ring
      _ = m * 2 ^ N := by rw [hinv, mul_one]
  rw [hl, hr, Nat.cast_lt]

/-- `k 2^{-N} < Ω` is `Σ₁`. -/
theorem lt_omega_iff {U : Map} {c : Code} (hc : IsCodeOf U c) (k N : ℕ) :
    (k : ℝ≥0∞) * 2⁻¹ ^ N < omega U ↔ ∃ t, k * 2 ^ t < omegaNum c t * 2 ^ N := by
  rw [omega_eq_iSup hc, lt_iSup_iff]
  simp only [omegaStage_eq, inv_pow_lt_iff]

/-- `⌊Ω 2^N⌋ = #{k ∈ [1, 2^N) : k 2^{-N} < Ω}`, as `Ω` is not dyadic. -/
theorem countBelow_lt_omega {U : Map} (hU : IsExactUniversal U) (N : ℕ) (b : ℕ → Bool)
    (hb : ∀ k < 2 ^ N, (b k = true ↔ 1 ≤ k ∧ (k : ℝ≥0∞) * 2⁻¹ ^ N < omega U)) :
    countBelow b (2 ^ N) = omegaDigits U N := by
  have hpm := hU.1.2
  rw [countBelow_eq_card]
  set a := omegaDigits U N
  have ha := omegaDigits_lt U N
  have hset : (Finset.range (2 ^ N)).filter (fun k ↦ b k = true) = Finset.Icc 1 a := by
    ext k
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hk, hbk⟩
      obtain ⟨h1, hlt⟩ := (hb k hk).mp hbk
      refine ⟨h1, ?_⟩
      have hup := omega_le_omegaDigits_succ hpm N
      have h2 : (k : ℝ≥0∞) * 2⁻¹ ^ N < ((a : ℝ≥0∞) + 1) * 2⁻¹ ^ N := hlt.trans_le hup
      have h' := (ENNReal.mul_lt_mul_iff_left
        (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp)))
        (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero))).mp
        (by rwa [mul_comm, mul_comm (_ + 1)] at h2)
      have : (k : ℝ≥0∞) < ((a + 1 : ℕ) : ℝ≥0∞) := by push_cast; exact h'
      exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
    · rintro ⟨h1, hka⟩
      refine ⟨by omega, (hb k (by omega)).mpr ⟨h1, lt_of_le_of_ne ?_ ?_⟩⟩
      · exact (mul_le_mul' (by exact_mod_cast hka) le_rfl).trans (omegaDigits_le hpm N)
      · exact fun h ↦ omega_ne_dyadic hU (by omega : k < 2 ^ N) h.symm
  rw [hset, Nat.card_Icc]
  omega

/-- The index queried for `k 2^{-N} < Ω`. -/
def queryIdx (tag : BitString) (k N : ℕ) : ℕ := idx (tag ++ natCode (encode (k, N)))

theorem queryIdx_primrec (tag : BitString) : Primrec fun p : ℕ × ℕ ↦ queryIdx tag p.1 p.2 :=
  (idx_primrec.comp (Primrec.list_append.comp (Primrec.const tag)
    (natCode_primrec'.comp (Primrec.encode.comp Primrec.id)))).of_eq fun _ ↦ rfl

/-- The table length needed for digit `n`: `1 + max_{k < 2^{n+1}} queryIdx k (n+1)`. -/
def queryLen (tag : BitString) (n : ℕ) : ℕ :=
  (List.range (2 ^ (n + 1))).foldr (fun k acc ↦ max (queryIdx tag k (n + 1) + 1) acc) 0

theorem lt_queryLen (tag : BitString) {n k : ℕ} (hk : k < 2 ^ (n + 1)) :
    queryIdx tag k (n + 1) < queryLen tag n := by
  unfold queryLen
  have : ∀ l : List ℕ, k ∈ l → queryIdx tag k (n + 1) + 1 ≤
      l.foldr (fun k acc ↦ max (queryIdx tag k (n + 1) + 1) acc) 0 := by
    intro l hl
    induction l with
    | nil => simp at hl
    | cons a l ih =>
      rcases List.mem_cons.mp hl with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)
  exact this _ (List.mem_range.mpr hk)

theorem queryLen_primrec (tag : BitString) : Primrec (queryLen tag) := by
  have hh : Primrec₂ fun (n : ℕ) (p : ℕ × ℕ) ↦ max (queryIdx tag p.1 (n + 1) + 1) p.2 :=
    (Primrec.nat_max.comp (Primrec.succ.comp ((queryIdx_primrec tag).comp
      (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.succ.comp Primrec.fst))))
      (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr (Primrec.list_range.comp (natPow_primrec.comp (Primrec.const 2)
    Primrec.succ)) (Primrec.const 0) hh).of_eq fun _ ↦ rfl

/-- The digit `n` of `Ω` from a table of `χ`. -/
def omegaFromTable (tag : BitString) (q : ℕ × List ℕ) : ℕ :=
  countBelow (fun k ↦ decide (1 ≤ k) && decide (q.2.getD (queryIdx tag k (q.1 + 1)) 0 = 1))
    (2 ^ (q.1 + 1)) % 2

theorem omegaFromTable_primrec (tag : BitString) : Primrec (omegaFromTable tag) := by
  have hq : Primrec fun r : (ℕ × List ℕ) × ℕ ↦ queryIdx tag r.2 (r.1.1 + 1) := by
    have h := (queryIdx_primrec tag).comp (Primrec.pair (Primrec.snd (α := ℕ × List ℕ) (β := ℕ))
      (Primrec.succ.comp (Primrec.fst.comp (Primrec.fst (α := ℕ × List ℕ) (β := ℕ)))))
    exact h.of_eq fun _ ↦ rfl
  have hg : Primrec fun r : (ℕ × List ℕ) × ℕ ↦ r.1.2.getD (queryIdx tag r.2 (r.1.1 + 1)) 0 := by
    have h := (Primrec.list_getD 0).comp
      (Primrec.snd.comp (Primrec.fst (α := ℕ × List ℕ) (β := ℕ))) hq
    exact h.of_eq fun _ ↦ rfl
  have h1 : Primrec fun r : (ℕ × List ℕ) × ℕ ↦ decide (1 ≤ r.2) :=
    PrimrecPred.decide (Primrec.nat_le.comp (Primrec.const 1) Primrec.snd)
  have h2 : Primrec fun r : (ℕ × List ℕ) × ℕ ↦
      decide (r.1.2.getD (queryIdx tag r.2 (r.1.1 + 1)) 0 = 1) :=
    PrimrecPred.decide (Primrec.eq.comp hg (Primrec.const 1))
  have hb : Primrec₂ fun (q : ℕ × List ℕ) (k : ℕ) ↦
      decide (1 ≤ k) && decide (q.2.getD (queryIdx tag k (q.1 + 1)) 0 = 1) :=
    (Primrec.and.comp h1 h2).to₂
  have hN : Primrec fun q : ℕ × List ℕ ↦ 2 ^ (q.1 + 1) :=
    natPow_primrec.comp (Primrec.const 2) (Primrec.succ.comp Primrec.fst)
  have hc := countBelow_primrec hb hN
  exact (Primrec.nat_mod.comp hc (Primrec.const 2)).of_eq fun _ ↦ rfl

/-- **`Ω ≤_T χ`.** -/
theorem omega_le_chi {U : Map} (hU : IsExactUniversal U) :
    TuringReducible (toPart (omegaBit U)) (toPart (chiNat U)) := by
  obtain ⟨c, hc⟩ := exists_isCodeOf hU.1.1
  have hlhs : Primrec fun r : (ℕ × ℕ) × ℕ ↦ r.1.1 * 2 ^ r.2 :=
    Primrec.nat_mul.comp (Primrec.fst.comp Primrec.fst)
      (natPow_primrec.comp (Primrec.const 2) Primrec.snd)
  have hrhs : Primrec fun r : (ℕ × ℕ) × ℕ ↦ omegaNum c r.2 * 2 ^ r.1.2 :=
    Primrec.nat_mul.comp ((omegaNum_primrec c).comp Primrec.snd)
      (natPow_primrec.comp (Primrec.const 2) (Primrec.snd.comp Primrec.fst))
  have hdec : Primrec fun r : (ℕ × ℕ) × ℕ ↦
      decide (r.1.1 * 2 ^ r.2 < omegaNum c r.2 * 2 ^ r.1.2) :=
    PrimrecPred.decide (Primrec.nat_lt.comp hlhs hrhs)
  have hb : Computable₂ fun (p : ℕ × ℕ) (t : ℕ) ↦
      decide (p.1 * 2 ^ t < omegaNum c t * 2 ^ p.2) := hdec.to_comp.to₂
  obtain ⟨tag, htag⟩ := exists_reduction hU hb
  refine turingReducible_of_table (Φ := fun q ↦ Part.some (omegaFromTable tag q))
    (omegaFromTable_primrec tag).to_comp.partrec (queryLen_primrec tag).to_comp fun n ↦ ?_
  unfold toPart
  congr 1
  unfold omegaFromTable omegaBit
  congr 1
  refine (countBelow_lt_omega hU (n + 1) _ fun k hk ↦ ?_).symm
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  refine and_congr_right fun _ ↦ ?_
  rw [getD_tableOf _ (lt_queryLen tag hk), lt_omega_iff hc, chiNat]
  have h := htag (k, n + 1)
  simp only [decide_eq_true_iff] at h
  unfold queryIdx
  simp [h]

/-! ### Theorem 3.2.3 -/

/-- **Gács Theorem 3.2.3.** For an exactly universal prefix machine `U`, the halting sequence
`χ` and the binary digits of Chaitin's `Ω` are Turing-equivalent. -/
theorem chi_turingEquivalent_omega {U : Map} (hU : IsExactUniversal U) :
    toPart (chiNat U) ≡ᵀ toPart (omegaBit U) :=
  ⟨chi_le_omega hU.1, omega_le_chi hU⟩

end Kolmogorov.Information.Turing
