/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Halting.Barzdin
import Gacs_Chapter_2.Randomness.RandomizedConservation
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting
import KolmogorovMathlib.Prefix.CountableKraft

/-!
# The halting set and Chaitin's `Ω` (Gács Definitions 3.2.3, 3.2.4, Theorem 3.2.4)

Fix a prefix decompressor `U` and a `Nat.Partrec.Code` `c` computing it (`IsCodeOf U c`).
"Halts in `< t` steps" is read as "`evaln t c` halts", so:

* `E^t` is `{p ∈ boundedPrograms t : haltsIn c t p}`; `E = domainAt U []`, and `χ = chi U`
  is its indicator with programs numbered by `idx` (Definition 3.2.3).
* `Ω^t = ∑_{p ∈ E^t} 2^{-|p|}` (`omegaStage`, equal to `omegaNum c t / 2^t`) and
  `Ω = ∑_{p ∈ E} 2^{-|p|}` (`omega U`, the upstream `domainWeight U []`), with
  `Ω = sup_t Ω^t` (`omega_eq_iSup`) and `Ω ≤ 1` (Definition 3.2.4).
* `Ω(1:n)` (`omegaPrefix U n`) is the `n`-bit binary expansion, most significant bit first, of
  `a_n = min(⌊Ω 2^n⌋, 2^n − 1)` (`omegaDigits`). It satisfies
  `a_n 2^{-n} ≤ Ω ≤ (a_n + 1) 2^{-n}` (`omegaDigits_le`, `omega_le_omegaDigits_succ`); the
  clamp only matters if `Ω = 1`.
* **Theorem 3.2.4** (`le_KP_omegaPrefix`): `K(Ω(1:n)) ≥ n − c`. From `Ω(1:n)` one finds the
  first stage `t` with `Ω^t + 2^{-n} > a_n 2^{-n}`; then every halting program of length
  `< n` has halted by stage `t` (`halts_of_short`), so the first string `0^j` not output by
  `E^t` has complexity `≥ n`. Using the threshold `a_n 2^{-n} − 2^{-n}` instead of Gács'
  `Ω(1:n)` avoids any appeal to the irrationality of `Ω`.
-/

namespace Kolmogorov.Information.Halting

open Kolmogorov
open Nat.Partrec (Code)
open scoped ENNReal
open Kolmogorov.Randomness (two_pow_ne_zero' two_pow_ne_top')

/-! ### Running the machine with a time bound -/

/-- `c` computes the prefix decompressor `U`. -/
def IsCodeOf (U : Map) (c : Code) : Prop :=
  Code.eval c = fun n ↦ Part.bind (Encodable.decode (α := BitString × BitString) n)
    fun a ↦ (U a).map Encodable.encode

theorem exists_isCodeOf {U : Map} (hU : isDecompressor U) : ∃ c, IsCodeOf U c :=
  Nat.Partrec.Code.exists_code.mp hU

/-- The (encoded) output of `p` on empty condition within fuel `t`. -/
def runOut (c : Code) (t : ℕ) (p : BitString) : Option ℕ :=
  Code.evaln t c (Encodable.encode (p, ([] : BitString)))

/-- `p` halts within fuel `t`. -/
def haltsIn (c : Code) (t : ℕ) (p : BitString) : Bool := (runOut c t p).isSome

theorem runOut_primrec (c : Code) : Primrec fun q : ℕ × BitString ↦ runOut c q.1 q.2 :=
  Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c))
    ((Primrec.encode (α := BitString × BitString)).comp
      (Primrec.pair Primrec.snd (Primrec.const []))))

theorem haltsIn_primrec (c : Code) : Primrec fun q : ℕ × BitString ↦ haltsIn c q.1 q.2 :=
  Primrec.option_isSome.comp (runOut_primrec c)

section Spec

variable {U : Map} {c : Code}

theorem eval_eq (hc : IsCodeOf U c) (p : BitString) :
    Code.eval c (Encodable.encode (p, ([] : BitString))) = (U (p, [])).map Encodable.encode := by
  rw [hc]; simp [Encodable.encodek, Part.bind_some]

theorem runOut_sound (hc : IsCodeOf U c) {t : ℕ} {p : BitString} {v : ℕ}
    (h : runOut c t p = some v) : ∃ x, v = Encodable.encode x ∧ x ∈ U (p, []) := by
  have h' := Nat.Partrec.Code.evaln_sound (show v ∈ Code.evaln t c _ from h)
  rw [eval_eq hc] at h'
  obtain ⟨x, hx, rfl⟩ := (Part.mem_map_iff _).mp h'
  exact ⟨x, rfl, hx⟩

theorem runOut_complete (hc : IsCodeOf U c) {p x : BitString} (h : x ∈ U (p, [])) :
    ∃ t, runOut c t p = some (Encodable.encode x) := by
  have : Encodable.encode x ∈ Code.eval c (Encodable.encode (p, ([] : BitString))) := by
    rw [eval_eq hc]; exact Part.mem_map _ h
  exact Nat.Partrec.Code.evaln_complete.mp this

theorem runOut_mono {t t' : ℕ} {p : BitString} {v : ℕ} (htt : t ≤ t')
    (h : runOut c t p = some v) : runOut c t' p = some v :=
  Nat.Partrec.Code.evaln_mono htt h

theorem runOut_eq_of_mem (hc : IsCodeOf U c) {t : ℕ} {p x : BitString} (hx : x ∈ U (p, []))
    (h : haltsIn c t p = true) : runOut c t p = some (Encodable.encode x) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨y, rfl, hy⟩ := runOut_sound hc hv
  rw [hv, Part.mem_unique hy hx]

theorem haltsIn_mono {t t' : ℕ} {p : BitString} (htt : t ≤ t') (h : haltsIn c t p = true) :
    haltsIn c t' p = true := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  exact Option.isSome_iff_exists.mpr ⟨v, runOut_mono htt hv⟩

theorem mem_domain_of_haltsIn (hc : IsCodeOf U c) {t : ℕ} {p : BitString}
    (h : haltsIn c t p = true) : p ∈ domainAt U [] := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨x, -, hx⟩ := runOut_sound hc hv
  exact Part.dom_iff_mem.mpr ⟨x, hx⟩

theorem exists_haltsIn (hc : IsCodeOf U c) {p : BitString} (h : p ∈ domainAt U []) :
    ∃ t, haltsIn c t p = true := by
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
  obtain ⟨t, ht⟩ := runOut_complete hc hx
  exact ⟨t, by simp [haltsIn, ht]⟩

end Spec

/-! ### `E`, `χ`, `Ω^t`, `Ω` -/

/-- **The halting set** `E` (Gács Definition 3.2.3). -/
def haltSet (U : Map) : Set BitString := domainAt U []

open Classical in
/-- **`χ`**, the indicator of `E` with programs numbered by `idx` (Definition 3.2.3). -/
noncomputable def chi (U : Map) (n : ℕ) : Bool := decide (∃ p ∈ haltSet U, idx p = n)

/-- **`Ω^t`** (Gács Definition 3.2.4). -/
noncomputable def omegaStage (c : Code) (t : ℕ) : ℝ≥0∞ :=
  ∑ p ∈ (boundedPrograms t).toFinset, if haltsIn c t p then progWeight p else 0

/-- **Chaitin's `Ω`** (Gács Definition 3.2.4): the halting probability of `U` on empty
condition. -/
noncomputable def omega (U : Map) : ℝ≥0∞ := domainWeight U []

/-- The numerator `2^t ∑_{p ∈ boundedPrograms t, b p} 2^{-|p|}`. -/
def foldNum (b : BitString → Bool) (t : ℕ) : ℕ :=
  (boundedPrograms t).foldr (fun p acc ↦ (if b p then 2 ^ (t - p.length) else 0) + acc) 0

theorem sum_ite_progWeight_eq (b : BitString → Bool) (t : ℕ) :
    ∑ p ∈ (boundedPrograms t).toFinset, (if b p then progWeight p else 0) =
      (foldNum b t : ℝ≥0∞) * 2⁻¹ ^ t := by
  have hfold : ∀ l : List BitString,
      l.foldr (fun p acc ↦ (if b p then 2 ^ (t - p.length) else 0) + acc) 0 =
        (l.map fun p ↦ if b p then 2 ^ (t - p.length) else 0).sum := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  rw [List.sum_toFinset _ (boundedPrograms_nodup t), foldNum, hfold,
    Nat.cast_list_sum, List.map_map, ← List.sum_map_mul_right]
  congr 1
  refine List.map_congr_left fun p hp ↦ ?_
  have hpt : p.length ≤ t := (mem_boundedPrograms_iff p t).mp hp
  simp only [Function.comp_apply]
  split_ifs
  · rw [progWeight, Nat.cast_pow, Nat.cast_ofNat]
    have h1 : (2 : ℝ≥0∞) ^ (t - p.length) * 2⁻¹ ^ (t - p.length) = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
    calc (2 : ℝ≥0∞)⁻¹ ^ p.length
        = 2 ^ (t - p.length) * (2⁻¹ ^ (t - p.length) * 2⁻¹ ^ p.length) := by
          rw [← mul_assoc, h1, one_mul]
      _ = 2 ^ (t - p.length) * 2⁻¹ ^ t := by rw [← pow_add, Nat.sub_add_cancel hpt]
  · simp

/-- The numerator `2^t Ω^t`. -/
def omegaNum (c : Code) (t : ℕ) : ℕ := foldNum (haltsIn c t) t

theorem omegaNum_primrec (c : Code) : Primrec (omegaNum c) := by
  have hh : Primrec₂ fun (t : ℕ) (q : BitString × ℕ) ↦
      (if haltsIn c t q.1 then 2 ^ (t - q.1.length) else 0) + q.2 := by
    have h1 : Primrec fun r : ℕ × (BitString × ℕ) ↦ haltsIn c r.1 r.2.1 :=
      (haltsIn_primrec c).comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
    have h2 : Primrec fun r : ℕ × (BitString × ℕ) ↦ 2 ^ (r.1 - r.2.1.length) :=
      Kolmogorov.Randomness.natPow_primrec.comp (Primrec.const 2)
        (Primrec.nat_sub.comp Primrec.fst (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
    exact (Primrec.nat_add.comp (Primrec.ite (Primrec.eq.comp h1 (Primrec.const true)) h2
      (Primrec.const 0)) (Primrec.snd.comp Primrec.snd)).to₂.of_eq fun _ _ ↦ by simp
  exact (Primrec.list_foldr primrec_boundedPrograms (Primrec.const 0) hh).of_eq fun _ ↦ rfl

theorem omegaStage_eq (c : Code) (t : ℕ) :
    omegaStage c t = (omegaNum c t : ℝ≥0∞) * 2⁻¹ ^ t :=
  sum_ite_progWeight_eq _ t

theorem omega_eq_iSup {U : Map} {c : Code} (hc : IsCodeOf U c) :
    omega U = ⨆ t, omegaStage c t := by
  classical
  unfold omega omegaStage domainWeight
  refine (Kolmogorov.Randomness.iSup_sum_boundedPrograms (fun p ↦ ?_) (fun p ↦ ?_)).symm
  · refine monotone_nat_of_le_succ fun t ↦ ?_
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd (haltsIn_mono (Nat.le_succ t) h1) h2
    · exact zero_le
    · exact le_rfl
  · by_cases hp : p ∈ domainAt U []
    · obtain ⟨t, ht⟩ := exists_haltsIn hc hp
      rw [if_pos hp]
      refine le_antisymm (iSup_le fun s ↦ ?_) (le_iSup_of_le t (by rw [if_pos ht]))
      split_ifs <;> simp
    · rw [if_neg hp]
      refine le_antisymm (iSup_le fun s ↦ ?_) zero_le
      rw [if_neg fun h ↦ hp (mem_domain_of_haltsIn hc h)]

theorem omegaStage_le_omega {U : Map} {c : Code} (hc : IsCodeOf U c) (t : ℕ) :
    omegaStage c t ≤ omega U := by
  rw [omega_eq_iSup hc]; exact le_iSup (fun t ↦ omegaStage c t) t

theorem omega_le_one {U : Map} (hU : IsPrefixMachine U) : omega U ≤ 1 :=
  domainWeight_le_one U [] hU

theorem omega_ne_top {U : Map} (hU : IsPrefixMachine U) : omega U ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (omega_le_one hU)

/-- The halting programs outside `E^t` still contribute: `Ω ≥ Ω^t + 2^{-|p|}`. -/
theorem omegaStage_add_le {U : Map} {c : Code} (hc : IsCodeOf U c) {t : ℕ} {p : BitString}
    (hp : p ∈ domainAt U []) (hnot : ¬ (p ∈ boundedPrograms t ∧ haltsIn c t p = true)) :
    omegaStage c t + progWeight p ≤ omega U := by
  classical
  set S := (boundedPrograms t).toFinset.filter fun q ↦ haltsIn c t q = true
  have hS : omegaStage c t = ∑ q ∈ S, progWeight q := by
    rw [omegaStage, Finset.sum_filter]
  have hpS : p ∉ S := fun h ↦ hnot (by
    simp only [S, Finset.mem_filter, List.mem_toFinset] at h; exact h)
  rw [hS, add_comm, ← Finset.sum_insert hpS]
  calc ∑ q ∈ insert p S, progWeight q
      = ∑ q ∈ insert p S, (if q ∈ domainAt U [] then progWeight q else 0) := by
        refine Finset.sum_congr rfl fun q hq ↦ ?_
        rw [if_pos]
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hp
        · exact mem_domain_of_haltsIn hc (Finset.mem_filter.mp hq).2
    _ ≤ omega U := ENNReal.sum_le_tsum _

/-! ### The binary digits of `Ω` -/

/-- `a_n = min(⌊Ω 2^n⌋, 2^n − 1)`. -/
noncomputable def omegaDigits (U : Map) (n : ℕ) : ℕ :=
  min ⌊(omega U).toNNReal * 2 ^ n⌋₊ (2 ^ n - 1)

/-- **`Ω(1:n)`**: the `n` first binary digits of `Ω`, most significant first. -/
noncomputable def omegaPrefix (U : Map) (n : ℕ) : BitString :=
  (padBits n (omegaDigits U n)).reverse

theorem omegaDigits_lt (U : Map) (n : ℕ) : omegaDigits U n < 2 ^ n := by
  have : 0 < 2 ^ n := by positivity
  unfold omegaDigits; omega

theorem length_omegaPrefix (U : Map) (n : ℕ) : (omegaPrefix U n).length = n := by
  rw [omegaPrefix, List.length_reverse, length_padBits (omegaDigits_lt U n)]

theorem bitsToNat_reverse_omegaPrefix (U : Map) (n : ℕ) :
    bitsToNat (omegaPrefix U n).reverse = omegaDigits U n := by
  rw [omegaPrefix, List.reverse_reverse, bitsToNat_padBits]

theorem omegaDigits_le {U : Map} (hU : IsPrefixMachine U) (n : ℕ) :
    (omegaDigits U n : ℝ≥0∞) * 2⁻¹ ^ n ≤ omega U := by
  have hfin := omega_ne_top hU
  have h1 : (omegaDigits U n : NNReal) ≤ (omega U).toNNReal * 2 ^ n :=
    (Nat.cast_le.mpr (min_le_left _ _)).trans (Nat.floor_le (by positivity))
  have h2 : (omegaDigits U n : ℝ≥0∞) ≤ omega U * 2 ^ n := by
    rw [← ENNReal.coe_toNNReal hfin]
    exact_mod_cast h1
  calc (omegaDigits U n : ℝ≥0∞) * 2⁻¹ ^ n ≤ omega U * 2 ^ n * 2⁻¹ ^ n := mul_le_mul' h2 le_rfl
    _ = omega U := by
      rw [mul_assoc, ← ENNReal.inv_pow,
        ENNReal.mul_inv_cancel (two_pow_ne_zero' n) (two_pow_ne_top' n), mul_one]

theorem omega_le_omegaDigits_succ {U : Map} (hU : IsPrefixMachine U) (n : ℕ) :
    omega U ≤ ((omegaDigits U n : ℝ≥0∞) + 1) * 2⁻¹ ^ n := by
  have hfin := omega_ne_top hU
  have hpow : (2 : ℝ≥0∞) ^ n * 2⁻¹ ^ n = 1 := by
    rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel (two_pow_ne_zero' n) (two_pow_ne_top' n)]
  by_cases hcl : ⌊(omega U).toNNReal * 2 ^ n⌋₊ ≤ 2 ^ n - 1
  · have ha : omegaDigits U n = ⌊(omega U).toNNReal * 2 ^ n⌋₊ := min_eq_left hcl
    have hlt : (omega U).toNNReal * 2 ^ n < ⌊(omega U).toNNReal * 2 ^ n⌋₊ + 1 :=
      Nat.lt_floor_add_one _
    have h2 : omega U * 2 ^ n ≤ (omegaDigits U n : ℝ≥0∞) + 1 := by
      rw [← ENNReal.coe_toNNReal hfin, ha]
      exact_mod_cast hlt.le
    calc omega U = omega U * 2 ^ n * 2⁻¹ ^ n := by rw [mul_assoc, hpow, mul_one]
      _ ≤ ((omegaDigits U n : ℝ≥0∞) + 1) * 2⁻¹ ^ n := mul_le_mul' h2 le_rfl
  · have ha : omegaDigits U n = 2 ^ n - 1 := min_eq_right (by omega)
    have : ((omegaDigits U n : ℝ≥0∞) + 1) = 2 ^ n := by
      rw [ha]
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      exact_mod_cast Nat.sub_add_cancel this
    rw [this, hpow]
    exact omega_le_one hU

/-! ### The stage threshold -/

/-- The stage test `Ω^t + 2^{-n} > a 2^{-n}`, in integers: `a 2^t < N_t 2^n + 2^t`. -/
def stageGood (c : Code) (n a t : ℕ) : Bool := decide (a * 2 ^ t < omegaNum c t * 2 ^ n + 2 ^ t)

theorem stageGood_iff (c : Code) (n a t : ℕ) :
    stageGood c n a t = true ↔ (a : ℝ≥0∞) * 2⁻¹ ^ n < omegaStage c t + 2⁻¹ ^ n := by
  rw [stageGood, decide_eq_true_iff, omegaStage_eq]
  have h0 : (2 : ℝ≥0∞) ^ t * 2 ^ n ≠ 0 := mul_ne_zero (two_pow_ne_zero' t) (two_pow_ne_zero' n)
  have ht : (2 : ℝ≥0∞) ^ t * 2 ^ n ≠ ⊤ := ENNReal.mul_ne_top (two_pow_ne_top' t) (two_pow_ne_top' n)
  have hinv : ∀ k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k * 2 ^ k = 1 := fun k ↦ by
    rw [← ENNReal.inv_pow, ENNReal.inv_mul_cancel (two_pow_ne_zero' k) (two_pow_ne_top' k)]
  rw [← ENNReal.mul_lt_mul_iff_left h0 ht]
  have hl : (a : ℝ≥0∞) * 2⁻¹ ^ n * (2 ^ t * 2 ^ n) = ((a * 2 ^ t : ℕ) : ℝ≥0∞) := by
    push_cast
    calc (a : ℝ≥0∞) * 2⁻¹ ^ n * (2 ^ t * 2 ^ n) = a * 2 ^ t * (2⁻¹ ^ n * 2 ^ n) := by ring
      _ = a * 2 ^ t := by rw [hinv, mul_one]
  have hr : ((omegaNum c t : ℝ≥0∞) * 2⁻¹ ^ t + 2⁻¹ ^ n) * (2 ^ t * 2 ^ n) =
      ((omegaNum c t * 2 ^ n + 2 ^ t : ℕ) : ℝ≥0∞) := by
    push_cast
    calc ((omegaNum c t : ℝ≥0∞) * 2⁻¹ ^ t + 2⁻¹ ^ n) * (2 ^ t * 2 ^ n)
        = omegaNum c t * 2 ^ n * (2⁻¹ ^ t * 2 ^ t) + 2 ^ t * (2⁻¹ ^ n * 2 ^ n) := by ring
      _ = omegaNum c t * 2 ^ n + 2 ^ t := by rw [hinv, hinv, mul_one, mul_one]
  rw [hl, hr, Nat.cast_lt]

theorem stageGood_primrec (c : Code) :
    Primrec fun q : (ℕ × ℕ) × ℕ ↦ stageGood c q.1.1 q.1.2 q.2 := by
  have hpow := Kolmogorov.Randomness.natPow_primrec
  have h1 : Primrec fun q : (ℕ × ℕ) × ℕ ↦ q.1.2 * 2 ^ q.2 :=
    Primrec.nat_mul.comp (Primrec.snd.comp Primrec.fst) (hpow.comp (Primrec.const 2) Primrec.snd)
  have h2 : Primrec fun q : (ℕ × ℕ) × ℕ ↦ omegaNum c q.2 * 2 ^ q.1.1 + 2 ^ q.2 :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp ((omegaNum_primrec c).comp Primrec.snd)
      (hpow.comp (Primrec.const 2) (Primrec.fst.comp Primrec.fst)))
      (hpow.comp (Primrec.const 2) Primrec.snd)
  exact (PrimrecPred.decide (Primrec.nat_lt.comp h1 h2)).of_eq fun _ ↦ rfl

/-- At a good stage for `a_n`, every halting program shorter than `n` has halted. -/
theorem halts_of_short {U : Map} (hU : IsPrefixMachine U) {c : Code} (hc : IsCodeOf U c)
    {n t : ℕ} (hgood : stageGood c n (omegaDigits U n) t = true) {p : BitString}
    (hp : p ∈ domainAt U []) (hlen : p.length < n) :
    p ∈ boundedPrograms t ∧ haltsIn c t p = true := by
  by_contra hnot
  have hle := omegaStage_add_le hc hp hnot
  rw [stageGood_iff] at hgood
  have hw : 2⁻¹ ^ n + 2⁻¹ ^ n ≤ progWeight p := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [progWeight, ← two_mul, pow_succ, mul_comm, mul_assoc,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
    exact pow_le_pow_right_of_le_one' (by norm_num) (by unfold programLength; omega)
  have hfin := omega_ne_top hU
  have : omega U < omega U := by
    calc omega U ≤ ((omegaDigits U n : ℝ≥0∞) + 1) * 2⁻¹ ^ n := omega_le_omegaDigits_succ hU n
      _ = (omegaDigits U n : ℝ≥0∞) * 2⁻¹ ^ n + 2⁻¹ ^ n := by ring
      _ < omegaStage c t + 2⁻¹ ^ n + 2⁻¹ ^ n :=
          ENNReal.add_lt_add_right (ENNReal.pow_ne_top (by simp)) hgood
      _ = omegaStage c t + (2⁻¹ ^ n + 2⁻¹ ^ n) := add_assoc _ _ _
      _ ≤ omegaStage c t + progWeight p := add_le_add le_rfl hw
      _ ≤ omega U := hle
  exact lt_irrefl _ this

theorem exists_stageGood {U : Map} (hU : IsPrefixMachine U) {c : Code} (hc : IsCodeOf U c)
    (n : ℕ) : ∃ t, stageGood c n (omegaDigits U n) t = true := by
  simp_rw [stageGood_iff]
  have hlt : (omegaDigits U n : ℝ≥0∞) * 2⁻¹ ^ n < omega U + 2⁻¹ ^ n :=
    lt_of_le_of_lt (omegaDigits_le hU n)
      (ENNReal.lt_add_right (omega_ne_top hU) (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp))))
  rw [omega_eq_iSup hc, ENNReal.iSup_add] at hlt
  exact lt_iSup_iff.mp hlt

/-! ### Theorem 3.2.4 -/

/-- Some program in `E^t` outputs `x`. -/
def outHit (c : Code) (t : ℕ) (x : BitString) : Bool :=
  (boundedPrograms t).any fun p ↦ decide (runOut c t p = some (Encodable.encode x))

theorem outHit_primrec (c : Code) : Primrec fun q : ℕ × BitString ↦ outHit c q.1 q.2 := by
  have hp : Primrec₂ fun (q : ℕ × BitString) (p : BitString) ↦
      decide (runOut c q.1 p = some (Encodable.encode q.2)) := by
    have h1 : Primrec fun r : (ℕ × BitString) × BitString ↦ runOut c r.1.1 r.2 :=
      (runOut_primrec c).comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)
    have h2 : Primrec fun r : (ℕ × BitString) × BitString ↦ some (Encodable.encode r.1.2) :=
      Primrec.option_some.comp (Primrec.encode.comp (Primrec.snd.comp Primrec.fst))
    exact (PrimrecPred.decide (Primrec.eq.comp h1 h2)).to₂
  exact list_any_primrec (primrec_boundedPrograms.comp Primrec.fst) hp

/-- From `Ω(1:n)` compute a string of complexity `≥ n`. -/
def omegaDecode (c : Code) (s : BitString) : Part BitString :=
  (rfindB fun t ↦ stageGood c s.length (bitsToNat s.reverse) t).bind fun t ↦
    (rfindB fun j ↦ !outHit c t (List.replicate j false)).map fun j ↦ List.replicate j false

theorem omegaDecode_partrec (c : Code) : Partrec (omegaDecode c) := by
  have hb : Computable₂ fun (s : BitString) (t : ℕ) ↦
      stageGood c s.length (bitsToNat s.reverse) t :=
    ((stageGood_primrec c).comp (Primrec.pair (Primrec.pair
      (Primrec.list_length.comp Primrec.fst)
      (bitsToNat_primrec.comp (Primrec.list_reverse.comp Primrec.fst))) Primrec.snd)).to_comp.to₂
  have hb2 : Computable₂ fun (q : BitString × ℕ) (j : ℕ) ↦
      !outHit c q.2 (List.replicate j false) :=
    (Primrec.not.comp ((outHit_primrec c).comp (Primrec.pair (Primrec.snd.comp Primrec.fst)
      (Primrec.list_replicate.comp Primrec.snd (Primrec.const false))))).to_comp.to₂
  have hm : Computable₂ fun (_ : BitString × ℕ) (j : ℕ) ↦ List.replicate j false :=
    (Primrec.list_replicate.comp Primrec.snd (Primrec.const false)).to_comp.to₂
  exact (rfindB_partrec hb).bind ((rfindB_partrec hb2).map hm)

/-- Only finitely many strings are output by `E^t`, so some `0^j` is not. -/
theorem exists_not_outHit (c : Code) (t : ℕ) :
    ∃ j, (!outHit c t (List.replicate j false)) = true := by
  classical
  by_contra hall
  set M := (boundedPrograms t).length
  have hhit : ∀ j, ∃ p ∈ boundedPrograms t,
      runOut c t p = some (Encodable.encode (List.replicate j false)) := fun j ↦ by
    have : outHit c t (List.replicate j false) = true := by
      by_contra h
      exact hall ⟨j, by simpa using h⟩
    simpa only [outHit, List.any_eq_true, decide_eq_true_eq] using this
  choose g hg hgout using hhit
  have hinj : Set.InjOn g (Finset.range (M + 1) : Set ℕ) := fun i _ j _ hij ↦ by
    have := (hgout i).symm.trans ((congrArg (runOut c t) hij).trans (hgout j))
    simpa using Encodable.encode_injective (Option.some_injective _ this)
  have hcard := Finset.card_le_card_of_injOn (t := (boundedPrograms t).toFinset) g
    (fun i _ ↦ List.mem_toFinset.mpr (hg i)) hinj
  simp only [Finset.card_range] at hcard
  have := List.toFinset_card_le (boundedPrograms t)
  omega

/-- **Gács Theorem 3.2.4.** `K(Ω(1:n)) ≥ n − c`. -/
theorem le_KP_omegaPrefix {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, (n : ENat) ≤ KP U (omegaPrefix U n) [] + c := by
  obtain ⟨code, hc⟩ := exists_isCodeOf hU.isDecompressor
  have hpm := hU.isPrefixMachine
  obtain ⟨c, hcK⟩ := KP_partrec_cond_first_map_le U hU (fun _ s ↦ omegaDecode code s)
    ((omegaDecode_partrec code).comp Computable.fst)
  refine ⟨c, fun n ↦ ?_⟩
  set s := omegaPrefix U n
  have hlen : s.length = n := length_omegaPrefix U n
  have hval : bitsToNat s.reverse = omegaDigits U n := bitsToNat_reverse_omegaPrefix U n
  obtain ⟨t, ht⟩ := exists_mem_rfindB (b := fun t ↦ stageGood code s.length
    (bitsToNat s.reverse) t) (by rw [hlen, hval]; exact exists_stageGood hpm hc n)
  have hgood : stageGood code n (omegaDigits U n) t = true := by
    have := (mem_rfindB.mp ht).1; rwa [hlen, hval] at this
  obtain ⟨j, hj⟩ := exists_mem_rfindB (exists_not_outHit code t)
  have hnot : outHit code t (List.replicate j false) = false := by
    have := (mem_rfindB.mp hj).1; simpa using this
  have hmem : List.replicate j false ∈ omegaDecode code s :=
    Part.mem_bind_iff.mpr ⟨t, ht, (Part.mem_map_iff _).mpr ⟨j, hj, rfl⟩⟩
  -- Every program for `0^j` is at least `n` long.
  have hK : (n : ENat) ≤ KP U (List.replicate j false) [] := by
    refine le_sInf ?_
    rintro _ ⟨p, hp, rfl⟩
    by_contra hlt
    have hlt' : p.length < n := by exact_mod_cast not_le.mp hlt
    obtain ⟨hpb, hph⟩ := halts_of_short hpm hc hgood (Part.dom_iff_mem.mpr ⟨_, hp⟩) hlt'
    have : outHit code t (List.replicate j false) = true :=
      List.any_eq_true.mpr ⟨p, hpb, decide_eq_true (runOut_eq_of_mem hc hp hph)⟩
    rw [hnot] at this; exact Bool.noConfusion this
  exact hK.trans (hcK s _ [] hmem)

end Kolmogorov.Information.Halting
