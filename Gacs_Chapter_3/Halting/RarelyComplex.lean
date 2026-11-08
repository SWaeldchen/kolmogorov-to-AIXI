/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Halting.Omega
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitin
import KolmogorovMathlib.AlgorithmicProbability.Normalization
import KolmogorovMathlib.Prefix.ConditionalSymmetry

/-!
# Complexity is rarely complex: Gács Lemmas 3.3.1 and 3.3.2

* **Lemma 3.3.1** (`measure_approx_le`, `measure_approx_lt`): for a semimeasure `ν` and
  `S_m = {x : 2^m μ(x) ≤ ν(x)}`, `μ(S_m) ≤ 2^{-m}`; and if `μ ≤ ν` with
  `∑ (ν − μ) < ε` then `ν(S_1) < 2ε`.
* **Lemma 3.3.2, sharp form** (`aprioriMeasure_complexityOfComplexity_le`): with
  `f(x) = K(K(x) ∣ x)` (`complexityOfComplexity`) and `m` the a priori semimeasure of the
  optimal machine, `m{x : f(x) = n} ≤ C 2^{K(n)} 2^{-n}`.

  Gács states `≲ n^{1.2} 2^{-n}`; ours implies it, since `K(n) ≤ log n + 2 log log n + O(1)`
  `≤ 1.2 log n + O(1)`.

## Proof of Lemma 3.3.2

* `m^t(x) = ∑_{p ∈ E^t, p ↦ x} 2^{-|p|}` (`mStage`): `∑_x m^t(x) = Ω^t` and `m^t ≤ m`.
* At the first good stage `t_k` for `Ω(1:k)` (`stageGood`), `∑_x (m − m^{t_k}) = Ω − Ω^{t_k} <
  2·2^{-k}`, so `Y(k) = {x : 2 m^{t_k}(x) ≤ m(x)}` has `m(Y(k)) < 4·2^{-k}` (Lemma 3.3.1).
* Off `Y(k)`, `K(x)` is within a constant of `t_k − |bin(2^{t_k} m^{t_k}(x))|`, which is
  computable from `x` and `Ω(1:k)` (`kMachine`). Hence `K(K(x) ∣ x) ≤ K(Ω(1:k)) + O(1)` off
  `Y(k)`.
* `K(Ω(1:k)) + e ≤ n + O(1)` when `k = n − K(n) − 3e` (`KPPlain_add_le_of_length`): describe
  `n` by a shortest program, then `e` and `Ω(1:k)` literally; the length of the literal part is
  computable from `n`, `K(n)` and `e` (`lenMachine`). Gács uses `K(Ω(1:k)) ≤ k + 2 log k`, which
  loses the `log` factors.
* So for a large fixed `e`, `{f = n} ⊆ Y(n − K(n) − 3e)`.
-/

namespace Kolmogorov.Information.Halting

open Kolmogorov
open Nat.Partrec (Code)
open scoped ENNReal
open Kolmogorov.Randomness (two_pow_ne_zero' two_pow_ne_top')

/-! ### Lemma 3.3.1 -/

/-- **Gács Lemma 3.3.1, first part.** `μ{x : 2^m μ(x) ≤ ν(x)} ≤ 2^{-m}` for a semimeasure
`ν`. -/
theorem measure_approx_le {α : Type*} (μ ν : α → ℝ≥0∞) (hν : ∑' x, ν x ≤ 1) (m : ℕ) :
    ∑' x, (if 2 ^ m * μ x ≤ ν x then μ x else 0) ≤ 2⁻¹ ^ m := by
  calc ∑' x, (if 2 ^ m * μ x ≤ ν x then μ x else 0) ≤ ∑' x, 2⁻¹ ^ m * ν x := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        split_ifs with h
        · calc μ x = 2⁻¹ ^ m * (2 ^ m * μ x) := by
                rw [← mul_assoc, ← mul_pow,
                  ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, one_mul]
            _ ≤ 2⁻¹ ^ m * ν x := mul_le_mul' le_rfl h
        · exact zero_le
    _ = 2⁻¹ ^ m * ∑' x, ν x := ENNReal.tsum_mul_left
    _ ≤ 2⁻¹ ^ m * 1 := mul_le_mul' le_rfl hν
    _ = 2⁻¹ ^ m := mul_one _

/-- **Gács Lemma 3.3.1, second part.** If `μ ≤ ν` and `∑ (ν − μ) < ε` then
`ν{x : 2 μ(x) ≤ ν(x)} < 2ε`. -/
theorem measure_approx_lt {α : Type*} (μ ν : α → ℝ≥0∞) (hle : ∀ x, μ x ≤ ν x)
    (hfin : ∀ x, ν x ≠ ⊤) {ε : ℝ≥0∞} (hsum : ∑' x, (ν x - μ x) < ε) :
    ∑' x, (if 2 * μ x ≤ ν x then ν x else 0) < 2 * ε := by
  calc ∑' x, (if 2 * μ x ≤ ν x then ν x else 0) ≤ ∑' x, 2 * (ν x - μ x) := by
        refine ENNReal.tsum_le_tsum fun x ↦ ?_
        split_ifs with h
        · have hμ : μ x ≠ ⊤ := ne_top_of_le_ne_top (hfin x) (hle x)
          have h1 : μ x ≤ ν x - μ x :=
            ENNReal.le_sub_of_add_le_left hμ (by rw [← two_mul]; exact h)
          calc ν x = ν x - μ x + μ x := (tsub_add_cancel_of_le (hle x)).symm
            _ ≤ ν x - μ x + (ν x - μ x) := add_le_add le_rfl h1
            _ = 2 * (ν x - μ x) := (two_mul _).symm
        · exact zero_le
    _ = 2 * ∑' x, (ν x - μ x) := ENNReal.tsum_mul_left
    _ < 2 * ε := by
        rw [mul_comm 2, mul_comm 2]
        exact (ENNReal.mul_lt_mul_iff_left two_ne_zero ENNReal.ofNat_ne_top).mpr hsum

/-! ### Helpers -/

theorem finset_sum_tsum_comm {α β : Type*} (F : Finset α) (f : α → β → ℝ≥0∞) :
    ∑' b, ∑ a ∈ F, f a b = ∑ a ∈ F, ∑' b, f a b := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    simp only [Finset.sum_insert ha]
    rw [ENNReal.tsum_add, ih]

theorem tsum_sub_eq {α : Type*} {f g : α → ℝ≥0∞} (hg : ∑' x, g x ≠ ⊤) (hle : ∀ x, g x ≤ f x) :
    ∑' x, (f x - g x) = ∑' x, f x - ∑' x, g x := by
  refine ENNReal.eq_sub_of_add_eq hg ?_
  rw [← ENNReal.tsum_add]
  exact tsum_congr fun x ↦ tsub_add_cancel_of_le (hle x)

theorem natCode_primrec' : Primrec natCode :=
  Primrec.list_append.comp (Primrec.list_replicate.comp Primrec.id (Primrec.const true))
    (Primrec.const [false])

/-- Comparison of dyadic multiples: `A 2^{-i} < B 2^{-j} ↔ A 2^j < B 2^i`. -/
theorem cast_mul_inv_pow_lt_iff (A B i j : ℕ) :
    (A : ℝ≥0∞) * 2⁻¹ ^ i < (B : ℝ≥0∞) * 2⁻¹ ^ j ↔ A * 2 ^ j < B * 2 ^ i := by
  have h0 : (2 : ℝ≥0∞) ^ i * 2 ^ j ≠ 0 := mul_ne_zero (two_pow_ne_zero' i) (two_pow_ne_zero' j)
  have ht : (2 : ℝ≥0∞) ^ i * 2 ^ j ≠ ⊤ :=
    ENNReal.mul_ne_top (two_pow_ne_top' i) (two_pow_ne_top' j)
  have hinv : ∀ k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k * 2 ^ k = 1 := fun k ↦ by
    rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
  rw [← ENNReal.mul_lt_mul_iff_left h0 ht]
  have hl : (A : ℝ≥0∞) * 2⁻¹ ^ i * (2 ^ i * 2 ^ j) = ((A * 2 ^ j : ℕ) : ℝ≥0∞) := by
    push_cast
    calc (A : ℝ≥0∞) * 2⁻¹ ^ i * (2 ^ i * 2 ^ j) = A * 2 ^ j * (2⁻¹ ^ i * 2 ^ i) := by ring
      _ = A * 2 ^ j := by rw [hinv, mul_one]
  have hr : (B : ℝ≥0∞) * 2⁻¹ ^ j * (2 ^ i * 2 ^ j) = ((B * 2 ^ i : ℕ) : ℝ≥0∞) := by
    push_cast
    calc (B : ℝ≥0∞) * 2⁻¹ ^ j * (2 ^ i * 2 ^ j) = B * 2 ^ i * (2⁻¹ ^ j * 2 ^ j) := by ring
      _ = B * 2 ^ i := by rw [hinv, mul_one]
  rw [hl, hr, Nat.cast_lt]

theorem cast_mul_inv_pow_le_iff (A B i j : ℕ) :
    (A : ℝ≥0∞) * 2⁻¹ ^ i ≤ (B : ℝ≥0∞) * 2⁻¹ ^ j ↔ A * 2 ^ j ≤ B * 2 ^ i := by
  rw [← not_lt, ← not_lt, cast_mul_inv_pow_lt_iff]

/-- Generic counting below a bound, with a parameter. -/
theorem countBelow_primrec {α : Type*} [Primcodable α] {b : α → ℕ → Bool} (hb : Primrec₂ b)
    {g : α → ℕ} (hg : Primrec g) : Primrec fun a ↦ countBelow (b a) (g a) := by
  have hh : Primrec₂ fun (a : α) (p : ℕ × ℕ) ↦ (if b a p.1 then 1 else 0) + p.2 := by
    have h1 : Primrec fun r : α × (ℕ × ℕ) ↦ b r.1 r.2.1 :=
      hb.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
    exact (Primrec.nat_add.comp (Primrec.ite (Primrec.eq.comp h1 (Primrec.const true))
      (Primrec.const 1) (Primrec.const 0)) (Primrec.snd.comp Primrec.snd)).to₂.of_eq
      fun _ _ ↦ by simp
  exact (Primrec.list_foldr (Primrec.list_range.comp hg) (Primrec.const 0) hh).of_eq
    fun _ ↦ rfl

/-- The bit length `⌊log₂ N⌋ + 1` (`= Nat.size N`), by counting. -/
def bitLen (N : ℕ) : ℕ := countBelow (fun i ↦ decide (2 ^ i ≤ N)) (N + 1)

theorem bitLen_eq_size (N : ℕ) : bitLen N = Nat.size N := by
  rw [bitLen, countBelow_eq_card]
  have : (Finset.range (N + 1)).filter (fun i ↦ decide (2 ^ i ≤ N) = true) =
      Finset.range (Nat.size N) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, decide_eq_true_eq, Nat.lt_size]
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨by have := (Nat.lt_two_pow_self (n := i)); omega, h⟩
  rw [this, Finset.card_range]

theorem bitLen_primrec : Primrec bitLen :=
  countBelow_primrec (b := fun N i ↦ decide (2 ^ i ≤ N))
    (PrimrecPred.decide (Primrec.nat_le.comp (Kolmogorov.Randomness.natPow_primrec.comp
      (Primrec.const 2) Primrec.snd) Primrec.fst)).to₂ Primrec.succ

/-! ### The time-bounded a priori semimeasure -/

section Stage

variable (c : Code)

/-- `p` outputs `x` within fuel `t`. -/
def outB (t : ℕ) (x p : BitString) : Bool := decide (runOut c t p = some (Encodable.encode x))

/-- **`m^t(x)`**: the weight of the programs in `E^t` printing `x`. -/
noncomputable def mStage (t : ℕ) (x : BitString) : ℝ≥0∞ :=
  ∑ p ∈ (boundedPrograms t).toFinset, if outB c t x p then progWeight p else 0

/-- Its numerator `2^t m^t(x)`. -/
def mNum (t : ℕ) (x : BitString) : ℕ := foldNum (outB c t x) t

theorem mStage_eq (t : ℕ) (x : BitString) : mStage c t x = (mNum c t x : ℝ≥0∞) * 2⁻¹ ^ t :=
  sum_ite_progWeight_eq _ t

theorem mNum_primrec : Primrec fun q : ℕ × BitString ↦ mNum c q.1 q.2 := by
  have hh : Primrec₂ fun (q : ℕ × BitString) (r : BitString × ℕ) ↦
      (if outB c q.1 q.2 r.1 then 2 ^ (q.1 - r.1.length) else 0) + r.2 := by
    have h1 : Primrec fun z : (ℕ × BitString) × (BitString × ℕ) ↦ outB c z.1.1 z.1.2 z.2.1 := by
      have hr := (runOut_primrec c).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd (α := ℕ × BitString) (β := BitString × ℕ))))
      have he := Primrec.option_some.comp (Primrec.encode.comp (Primrec.snd.comp
        (Primrec.fst (α := ℕ × BitString) (β := BitString × ℕ))))
      exact (PrimrecPred.decide (Primrec.eq.comp hr he)).of_eq fun _ ↦ rfl
    have h2 : Primrec fun z : (ℕ × BitString) × (BitString × ℕ) ↦ 2 ^ (z.1.1 - z.2.1.length) :=
      Kolmogorov.Randomness.natPow_primrec.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
    exact (Primrec.nat_add.comp (Primrec.ite (Primrec.eq.comp h1 (Primrec.const true)) h2
      (Primrec.const 0)) (Primrec.snd.comp Primrec.snd)).to₂.of_eq fun _ _ ↦ by simp
  exact (Primrec.list_foldr (primrec_boundedPrograms.comp Primrec.fst) (Primrec.const 0)
    hh).of_eq fun _ ↦ rfl

variable {U : Map} {c}

theorem tsum_mStage (hc : IsCodeOf U c) (t : ℕ) : ∑' x, mStage c t x = omegaStage c t := by
  simp only [mStage]
  rw [finset_sum_tsum_comm, omegaStage]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  cases hrun : runOut c t p with
  | none =>
    have hh : haltsIn c t p = false := by simp [haltsIn, hrun]
    simp [outB, hrun, hh]
  | some v =>
    obtain ⟨y, rfl, -⟩ := runOut_sound hc hrun
    have hh : haltsIn c t p = true := by simp [haltsIn, hrun]
    rw [if_pos hh]
    have : ∀ x, outB c t x p = decide (x = y) := fun x ↦ by
      simp [outB, hrun, Encodable.encode_inj, eq_comm]
    simp_rw [this]
    simp

theorem mStage_le (hc : IsCodeOf U c) (t : ℕ) (x : BitString) :
    mStage c t x ≤ aprioriMeasure U x [] := by
  classical
  refine le_trans (Finset.sum_le_sum fun p _ ↦ ?_) (ENNReal.sum_le_tsum
    (f := fun p ↦ if produces U p [] x then progWeight p else 0) _)
  by_cases h : outB c t x p = true
  · rw [if_pos h]
    have hrun : runOut c t p = some (Encodable.encode x) := of_decide_eq_true h
    obtain ⟨y, hy, hyU⟩ := runOut_sound hc hrun
    have hxy : x = y := Encodable.encode_injective hy
    subst hxy
    rw [if_pos (show produces U p [] x from hyU)]
  · rw [if_neg h]; exact zero_le

end Stage

/-! ### Off `Y(k)`, `K(x)` is computable from `x` and `Ω(1:k)` -/

section KMachine

variable (c : Code)

/-- Output `natCode (t − |bin N| + e)` on program `natCode e`. -/
def kOut (t : ℕ) (q x : BitString) : Option BitString :=
  if q = natCode (natOfCode q) then some (natCode (t - bitLen (mNum c t x) + natOfCode q))
  else none

theorem kOut_primrec : Primrec fun r : ℕ × BitString × BitString ↦ kOut c r.1 r.2.1 r.2.2 := by
  have hq : Primrec fun r : ℕ × BitString × BitString ↦ natOfCode r.2.1 :=
    natOfCode_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hcond : PrimrecPred fun r : ℕ × BitString × BitString ↦ r.2.1 = natCode (natOfCode r.2.1) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (natCode_primrec'.comp hq)
  have hval : Primrec fun r : ℕ × BitString × BitString ↦
      natCode (r.1 - bitLen (mNum c r.1 r.2.2) + natOfCode r.2.1) :=
    natCode_primrec'.comp (Primrec.nat_add.comp (Primrec.nat_sub.comp Primrec.fst
      (bitLen_primrec.comp ((mNum_primrec c).comp (Primrec.pair Primrec.fst
        (Primrec.snd.comp Primrec.snd))))) hq)
  exact (Primrec.ite hcond (Primrec.option_some.comp hval) (Primrec.const none)).of_eq
    fun _ ↦ rfl

/-- The machine computing `K(x)` from `⟨x, Ω(1:k)⟩` and a short offset. -/
def kMachine : Map := fun pr ↦
  (rfindB fun t ↦ stageGood c (decodeSecond pr.2).length
    (bitsToNat (decodeSecond pr.2).reverse) t).bind fun t ↦
      Part.ofOption (kOut c t pr.1 (decodeFirst pr.2))

theorem kMachine_isDecompressor : isDecompressor (kMachine c) := by
  have hs : Computable fun pr : BitString × BitString ↦ decodeSecond pr.2 :=
    decodeSecond_computable.comp Computable.snd
  have hb : Computable₂ fun (pr : BitString × BitString) (t : ℕ) ↦
      stageGood c (decodeSecond pr.2).length (bitsToNat (decodeSecond pr.2).reverse) t := by
    have h1 : Computable fun z : (BitString × BitString) × ℕ ↦
        ((decodeSecond z.1.2).length, bitsToNat (decodeSecond z.1.2).reverse) :=
      Computable.pair (Computable.list_length.comp (hs.comp Computable.fst))
        ((bitsToNat_primrec.comp Primrec.list_reverse).to_comp.comp (hs.comp Computable.fst))
    have h := (stageGood_primrec c).to_comp.comp (Computable.pair h1 Computable.snd)
    exact h.of_eq fun _ ↦ rfl
  have hk : Computable₂ fun (pr : BitString × BitString) (t : ℕ) ↦
      kOut c t pr.1 (decodeFirst pr.2) := by
    have h := (kOut_primrec c).to_comp.comp (Computable.pair Computable.snd
      (Computable.pair (Computable.fst.comp Computable.fst)
        (decodeFirst_computable.comp (Computable.snd.comp Computable.fst))))
    exact h.of_eq fun _ ↦ rfl
  exact (rfindB_partrec hb).bind (Computable.ofOption hk)

theorem eq_natCode_of_mem_domain {p y : BitString} (h : p ∈ domainAt (kMachine c) y) :
    p = natCode (natOfCode p) := by
  obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp h
  obtain ⟨t, -, ht⟩ := Part.mem_bind_iff.mp hz
  simp only [Part.mem_ofOption, kOut] at ht
  split_ifs at ht with hp
  · exact hp
  · exact absurd ht (by simp)

theorem kMachine_isPrefixDecompressor : IsPrefixDecompressor (kMachine c) := by
  refine ⟨kMachine_isDecompressor c, fun y p hp q hq hpq ↦ ?_⟩
  have hp' := eq_natCode_of_mem_domain c hp
  have hq' := eq_natCode_of_mem_domain c hq
  rw [hp', hq'] at hpq ⊢
  rw [natCode_prefix_iff.mp hpq]

end KMachine

/-! ### Strings of length `n − K(n) − 3e` have complexity `≲ n − e` -/

theorem pairCode_primrec' : Primrec₂ pairCode := by
  have h := Primrec.list_append.comp (Primrec.list_append.comp
    (natCode_primrec'.comp (Primrec.list_length.comp Primrec.fst)) Primrec.fst) Primrec.snd
  exact h.to₂.of_eq fun _ _ ↦ rfl

theorem pairCode_prefix {x q x' q' : BitString} (h : pairCode x q <+: pairCode x' q') :
    x = x' ∧ q <+: q' := by
  unfold pairCode at h
  have hn : natCode x.length = natCode x'.length := by
    have h1 : natCode x.length <+: natCode x'.length ++ x' ++ q' :=
      (List.prefix_append _ _).trans ((List.prefix_append _ _).trans h)
    rcases List.prefix_or_prefix_of_prefix h1
      ((List.prefix_append _ _).trans (List.prefix_append _ _)) with hc | hc
    · rw [natCode_prefix_iff.mp hc]
    · rw [natCode_prefix_iff.mp hc]
  rw [List.append_assoc, List.append_assoc, hn] at h
  have h2 := (List.prefix_append_right_inj _).mp h
  have hlen : x.length = x'.length := by
    have := congrArg List.length hn; simpa [length_natCode] using this
  have hx : x = x' := by
    have h3 : x <+: x' ++ q' := (List.prefix_append _ _).trans h2
    exact (List.prefix_of_prefix_length_le h3 (List.prefix_append _ _) hlen.le).eq_of_length hlen
  subst hx
  exact ⟨rfl, (List.prefix_append_right_inj _).mp h2⟩

/-- In the context `⟨natCode n, natCode kn⟩`, the program `⟨u, w⟩` prints `w` provided
`|w| + 3|u| + kn = n`. -/
def lenOut (q z : BitString) : Option BitString :=
  if pairCode (decodeFirst q) (decodeSecond q) = q then
    if (decodeSecond q).length + 3 * (decodeFirst q).length + natOfCode (decodeSecond z) =
        natOfCode (decodeFirst z) then some (decodeSecond q) else none
  else none

/-- The machine of `lenOut`. -/
def lenMachine : Map := fun pr ↦ Part.ofOption (lenOut pr.1 pr.2)

theorem lenOut_primrec : Primrec fun pr : BitString × BitString ↦ lenOut pr.1 pr.2 := by
  have hq1 : Primrec fun pr : BitString × BitString ↦ decodeFirst pr.1 :=
    CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.fst
  have hq2 : Primrec fun pr : BitString × BitString ↦ decodeSecond pr.1 :=
    CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.fst
  have hc1 : PrimrecPred fun pr : BitString × BitString ↦
      pairCode (decodeFirst pr.1) (decodeSecond pr.1) = pr.1 :=
    Primrec.eq.comp (pairCode_primrec'.comp hq1 hq2) Primrec.fst
  have hc2 : PrimrecPred fun pr : BitString × BitString ↦
      (decodeSecond pr.1).length + 3 * (decodeFirst pr.1).length + natOfCode (decodeSecond pr.2) =
        natOfCode (decodeFirst pr.2) :=
    Primrec.eq.comp (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.list_length.comp hq2)
      (Primrec.nat_mul.comp (Primrec.const 3) (Primrec.list_length.comp hq1)))
      (natOfCode_primrec.comp (CodedFiniteDistribution.decodeSecond_primrec.comp Primrec.snd)))
      (natOfCode_primrec.comp (CodedFiniteDistribution.decodeFirst_primrec.comp Primrec.snd))
  exact (Primrec.ite hc1 (Primrec.ite hc2 (Primrec.option_some.comp hq2) (Primrec.const none))
    (Primrec.const none)).of_eq fun _ ↦ rfl

theorem lenMachine_isPrefixDecompressor : IsPrefixDecompressor lenMachine := by
  refine ⟨(Computable.ofOption lenOut_primrec.to_comp).of_eq fun _ ↦ rfl,
    fun z q hq q' hq' hpre ↦ ?_⟩
  have hv : ∀ {s : BitString}, (lenMachine (s, z)).Dom →
      pairCode (decodeFirst s) (decodeSecond s) = s ∧
        (decodeSecond s).length + 3 * (decodeFirst s).length + natOfCode (decodeSecond z) =
          natOfCode (decodeFirst z) := fun {s} hs ↦ by
    unfold lenMachine lenOut at hs
    split_ifs at hs with h1 h2
    · exact ⟨h1, h2⟩
    · exact absurd hs (by simp)
    · exact absurd hs (by simp)
  obtain ⟨h1, h1'⟩ := hv hq
  obtain ⟨h2, h2'⟩ := hv hq'
  rw [← h1, ← h2] at hpre
  obtain ⟨hx, hs⟩ := pairCode_prefix hpre
  have hlen : (decodeSecond q).length = (decodeSecond q').length := by rw [hx] at h1'; omega
  rw [← h1, ← h2, hx, hs.eq_of_length hlen]

/-- **`K(s) + e ≤ n + c` whenever `|s| = n − K(n) − 3e`**, uniformly in `e`, `n`, `s`. -/
theorem KPPlain_add_le_of_length {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ (e n : ℕ) (s : BitString),
      s.length + 3 * e + (KPPlain U (natCode n)).toNat = n → KPPlain U s + e ≤ n + c := by
  obtain ⟨c₁, h₁⟩ := KPPlain_right_le_KPPair U hU
  obtain ⟨c₂, h₂⟩ := KPPair_chain_upper U hU
  obtain ⟨c₃, h₃⟩ := hU.invariance lenMachine_isPrefixDecompressor
  refine ⟨c₁ + c₂ + c₃ + 1, fun e n s hlen ↦ ?_⟩
  set kn := (KPPlain U (natCode n)).toNat with hkn_def
  have hkn : HasPrefixComplexityValue U (natCode n) kn :=
    ENat.coe_toNat (KP_ne_top_of_optimal U hU _ _)
  set z := prefixComplexityContext (natCode n) kn
  have hrun : s ∈ lenMachine (pairCode (List.replicate e false) s, z) := by
    simp only [lenMachine, lenOut, z, prefixComplexityContext, decodeFirst_pairCode,
      decodeSecond_pairCode, natOfCode_natCode, List.length_replicate]
    rw [if_pos trivial, if_pos hlen]
    simp
  have hM : KP lenMachine s z ≤ ((2 * e + 1 + s.length : ℕ) : ENat) := by
    calc KP lenMachine s z ≤ ((pairCode (List.replicate e false) s).length : ENat) :=
          sInf_le ⟨_, hrun, rfl⟩
      _ = ((2 * e + 1 + s.length : ℕ) : ENat) := by
          rw [length_pairCode, List.length_replicate]; congr 1; ring
  calc KPPlain U s + e ≤ (KPPair U (natCode n) s + c₁) + e := add_le_add (h₁ _ _) le_rfl
    _ ≤ ((KPPlain U (natCode n) + KP U s z + c₂) + c₁) + e :=
        add_le_add (add_le_add (h₂ _ _ _ hkn) le_rfl) le_rfl
    _ ≤ (((kn : ENat) + (((2 * e + 1 + s.length : ℕ) : ENat) + c₃) + c₂) + c₁) + e := by
        rw [← hkn]
        exact add_le_add (add_le_add (add_le_add (add_le_add le_rfl
          ((h₃ s z).trans (add_le_add hM le_rfl))) le_rfl) le_rfl) le_rfl
    _ = ((kn + (2 * e + 1 + s.length + c₃) + c₂ + c₁ + e : ℕ) : ENat) := by push_cast; ring
    _ ≤ ((n + (c₁ + c₂ + c₃ + 1) : ℕ) : ENat) := by exact_mod_cast (by omega)
    _ = (n : ENat) + ((c₁ + c₂ + c₃ + 1 : ℕ) : ENat) := by push_cast; ring

/-! ### Lemma 3.3.2 -/

theorem inv_pow_sub_eq (n D : ℕ) (h : D ≤ n) :
    (2 : ℝ≥0∞)⁻¹ ^ (n - D) = 2 ^ D * 2⁻¹ ^ n := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + D := ⟨n - D, by omega⟩
  rw [Nat.add_sub_cancel, pow_add, ← mul_assoc, mul_comm (2 ^ D : ℝ≥0∞), mul_assoc, ← mul_pow,
    ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow, mul_one]

/-- **`f(x) = K(K(x) ∣ x)`**. -/
noncomputable def complexityOfComplexity (U : Map) (x : BitString) : ENat :=
  KP U (natCode (KP U x []).toNat) x

/-- `K(w ∣ x) ≤ K(s) + K(w ∣ ⟨x, s⟩) + c`. -/
theorem KP_le_KPPlain_add_KP_pair {U : Map} (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ w x s, KP U w x ≤ KPPlain U s + KP U w (pairCode x s) + C := by
  obtain ⟨c₁, h₁⟩ := KP_cond_first_map_le U hU (fun _ q ↦ decodeSecond q)
    (decodeSecond_computable.comp Computable.snd)
  obtain ⟨c₂, h₂⟩ := KPCondPair_chain_upper U hU
  obtain ⟨c₃, h₃⟩ := KP_le_KPPlain U hU
  have hf := pairCode_computable.comp (Computable.pair
      decodeFirst_computable (decodeFirst_computable.comp decodeSecond_computable))
  obtain ⟨c₄, h₄⟩ := KP_cond_map_le U hU (fun y ↦ pairCode (decodeFirst y)
    (decodeFirst (decodeSecond y))) (hf.of_eq fun _ ↦ rfl)
  refine ⟨c₁ + c₂ + c₃ + c₄, fun w x s ↦ ?_⟩
  set ks := (KP U s x).toNat
  have hks : HasCondPrefixComplexityValue U s x ks :=
    ENat.coe_toNat (KP_ne_top_of_optimal U hU s x)
  have e1 := h₁ (pairCode s w) x
  simp only [decodeSecond_pairCode] at e1
  have e2 := h₂ s w x ks hks
  have e4 := h₄ w (prefixCondComplexityContext x s ks)
  simp only [prefixCondComplexityContext, decodeFirst_pairCode, decodeSecond_pairCode] at e4
  unfold KPCondPair at e2
  unfold prefixCondComplexityContext at e2
  calc KP U w x ≤ KP U (pairCode s w) x + c₁ := e1
    _ ≤ KP U s x + KP U w (pairCode x (pairCode s (natCode ks))) + c₂ + c₁ := by gcongr
    _ ≤ (KPPlain U s + c₃) + (KP U w (pairCode x s) + c₄) + c₂ + c₁ := by
        gcongr
        · exact h₃ s x
    _ = KPPlain U s + KP U w (pairCode x s) + ((c₁ + c₂ + c₃ + c₄ : ℕ) : ENat) := by
        push_cast; ring

/-- **Gács Lemma 3.3.2, sharp form.** `m{x : K(K(x) ∣ x) = n} ≤ C 2^{K(n)} 2^{-n}`.
(Gács: `≲ n^{1.2} 2^{-n}`, which follows since `K(n) ≤ 1.2 log n + O(1)`.) -/
theorem aprioriMeasure_complexityOfComplexity_le {U : Map}
    (hU : IsOptimalPrefixConditional U) :
    ∃ C : ℕ, ∀ n : ℕ, ∑' x, (if complexityOfComplexity U x = n then aprioriMeasure U x []
      else 0) ≤ (C : ℝ≥0∞) * 2 ^ (KPPlain U (natCode n)).toNat * 2⁻¹ ^ n := by
  classical
  obtain ⟨c, hc⟩ := exists_isCodeOf hU.isDecompressor
  have hpm := hU.isPrefixMachine
  obtain ⟨c₀, hc₀⟩ := aprioriMeasure_le_complexityWeight_optimal hU hU.isPrefixDecompressor
  obtain ⟨cD, hcD⟩ := hU.invariance (kMachine_isPrefixDecompressor c)
  obtain ⟨cH, hcH⟩ := KP_le_KPPlain_add_KP_pair hU
  obtain ⟨cA, hcA⟩ := KPPlain_add_le_of_length hU
  set m : BitString → ℝ≥0∞ := fun x ↦ aprioriMeasure U x [] with hm
  -- The first good stage for `Ω(1:k)`.
  set tk : ℕ → ℕ := fun k ↦ Nat.find (exists_stageGood hpm hc k) with htk
  have htk_spec : ∀ k, stageGood c k (omegaDigits U k) (tk k) = true := fun k ↦
    Nat.find_spec (exists_stageGood hpm hc k)
  -- The bad set `Y(k)` is small.
  have hY : ∀ k, ∑' x, (if 2 * mStage c (tk k) x ≤ m x then m x else 0) < 4 * 2⁻¹ ^ k := by
    intro k
    have hgood := (stageGood_iff c k _ _).mp (htk_spec k)
    have hfinΩ := omega_ne_top hpm
    have hfinS : ∑' x, mStage c (tk k) x ≠ ⊤ := by
      rw [tsum_mStage hc]
      exact ne_top_of_le_ne_top hfinΩ (omegaStage_le_omega hc _)
    have hsum : ∑' x, (m x - mStage c (tk k) x) < 2 * 2⁻¹ ^ k := by
      rw [tsum_sub_eq hfinS (fun x ↦ mStage_le hc _ x), tsum_mStage hc]
      have : ∑' x, m x = omega U := tsum_aprioriMeasure_eq_domainWeight U []
      rw [this]
      refine ENNReal.sub_lt_of_lt_add (omegaStage_le_omega hc _) ?_
      calc omega U ≤ ((omegaDigits U k : ℝ≥0∞) + 1) * 2⁻¹ ^ k := omega_le_omegaDigits_succ hpm k
        _ = (omegaDigits U k : ℝ≥0∞) * 2⁻¹ ^ k + 2⁻¹ ^ k := by ring
        _ < omegaStage c (tk k) + 2⁻¹ ^ k + 2⁻¹ ^ k :=
            ENNReal.add_lt_add_right (ENNReal.pow_ne_top (by simp)) hgood
        _ = 2 * 2⁻¹ ^ k + omegaStage c (tk k) := by ring
    have := measure_approx_lt (fun x ↦ mStage c (tk k) x) m (fun x ↦ mStage_le hc _ x)
      (fun x ↦ aprioriMeasure_ne_top U x [] hpm) hsum
    calc _ < 2 * (2 * 2⁻¹ ^ k) := this
      _ = 4 * 2⁻¹ ^ k := by ring
  -- Off `Y(k)`, `f(x) ≤ K(Ω(1:k)) + C₃`.
  set C₃ := c₀ + 2 + cD + cH with hC₃
  have hoff : ∀ k x, ¬ (2 * mStage c (tk k) x ≤ m x) →
      complexityOfComplexity U x ≤ KPPlain U (omegaPrefix U k) + C₃ := by
    intro k x hx
    rw [not_le] at hx
    obtain ⟨K, hK⟩ : ∃ K : ℕ, KP U x [] = K :=
      ⟨_, (ENat.coe_toNat (KP_ne_top_of_optimal U hU x [])).symm⟩
    set s := omegaPrefix U k
    set t := tk k
    set N := mNum c t x
    -- Integer bounds on `K` from the coding theorem.
    have hlow : (2 : ℝ≥0∞)⁻¹ ^ K ≤ m x := by
      have := complexityWeight_KP_le_aprioriMeasure U x []
      rwa [hK, complexityWeight_coe] at this
    have hup : m x ≤ 2 ^ c₀ * 2⁻¹ ^ K := by
      have := hc₀ x []
      rw [hK, complexityWeight_coe] at this
      calc m x = 2 ^ c₀ * (2⁻¹ ^ c₀ * m x) := by
            rw [← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
              one_pow, one_mul]
        _ ≤ 2 ^ c₀ * 2⁻¹ ^ K := mul_le_mul' le_rfl this
    rw [mStage_eq] at hx
    have hi : 2 ^ t < 2 * N * 2 ^ K := by
      have h := lt_of_le_of_lt hlow hx
      have : (1 : ℝ≥0∞) * 2⁻¹ ^ K < ((2 * N : ℕ) : ℝ≥0∞) * 2⁻¹ ^ t := by
        push_cast; rw [one_mul, mul_assoc]; exact h
      have := (cast_mul_inv_pow_lt_iff 1 (2 * N) K t).mp (by exact_mod_cast this)
      linarith
    have hii : N * 2 ^ K ≤ 2 ^ c₀ * 2 ^ t := by
      have h : (N : ℝ≥0∞) * 2⁻¹ ^ t ≤ ((2 ^ c₀ : ℕ) : ℝ≥0∞) * 2⁻¹ ^ K := by
        push_cast
        exact (by rw [← mStage_eq]; exact mStage_le hc t x : (N : ℝ≥0∞) * 2⁻¹ ^ t ≤ m x).trans
          hup
      exact (cast_mul_inv_pow_le_iff N (2 ^ c₀) t K).mp h
    have hN : 0 < N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · rw [h0] at hi; simp at hi
      · exact h0
    set S := Nat.size N
    have hS : 0 < S := Nat.size_pos.mpr hN
    have hNlt : N < 2 ^ S := Nat.lt_size_self N
    have hNge : 2 ^ (S - 1) ≤ N := Nat.lt_size.mp (by omega)
    have hK1 : t - S ≤ K := by
      have : 2 ^ t < 2 ^ (S + K + 1) := by
        calc 2 ^ t < 2 * N * 2 ^ K := hi
          _ ≤ 2 * 2 ^ S * 2 ^ K := by gcongr
          _ = 2 ^ (S + K + 1) := by ring
      have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp this
      omega
    have hK2 : K ≤ t - S + c₀ + 1 := by
      have : 2 ^ (S - 1 + K) ≤ 2 ^ (c₀ + t) := by
        calc 2 ^ (S - 1 + K) = 2 ^ (S - 1) * 2 ^ K := pow_add _ _ _
          _ ≤ N * 2 ^ K := by gcongr
          _ ≤ 2 ^ c₀ * 2 ^ t := hii
          _ = 2 ^ (c₀ + t) := (pow_add _ _ _).symm
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
      omega
    set e := K - (t - S)
    -- The machine outputs `natCode K` on `natCode e`.
    have hrun : natCode K ∈ kMachine c (natCode e, pairCode x s) := by
      refine Part.mem_bind_iff.mpr ⟨t, ?_, ?_⟩
      · simp only [decodeSecond_pairCode, s, length_omegaPrefix, bitsToNat_reverse_omegaPrefix]
        refine mem_rfindB.mpr ⟨htk_spec k, fun j hj ↦ ?_⟩
        have := Nat.find_min (exists_stageGood hpm hc k) hj
        simpa using this
      · simp only [decodeFirst_pairCode, kOut, natOfCode_natCode, if_true, Part.mem_ofOption,
          Option.mem_def, Option.some.injEq, bitLen_eq_size]
        congr 1
        change t - Nat.size N + e = K
        omega
    have hKD : KP (kMachine c) (natCode K) (pairCode x s) ≤ c₀ + 2 := by
      calc KP (kMachine c) (natCode K) (pairCode x s) ≤ (natCode e).length :=
            sInf_le ⟨natCode e, hrun, rfl⟩
        _ ≤ c₀ + 2 := by
            rw [length_natCode]; exact_mod_cast (by omega : e + 1 ≤ c₀ + 2)
    have hKnat : (KP U x []).toNat = K := by rw [hK]; rfl
    unfold complexityOfComplexity
    rw [hKnat]
    calc KP U (natCode K) x ≤ KPPlain U s + KP U (natCode K) (pairCode x s) + cH := hcH _ _ _
      _ ≤ KPPlain U s + (KP (kMachine c) (natCode K) (pairCode x s) + cD) + cH := by
            gcongr; exact hcD _ _
      _ ≤ KPPlain U s + ((c₀ + 2 : ℕ) + cD) + cH := by gcongr; exact_mod_cast hKD
      _ = KPPlain U s + ((C₃ : ℕ) : ENat) := by rw [hC₃]; push_cast; ring
  -- Final count: `{f = n} ⊆ Y(n − K(n) − 3e)`.
  set e := cA + C₃ + 1 with he
  refine ⟨4 * 2 ^ (3 * e), fun n ↦ ?_⟩
  set kn := (KPPlain U (natCode n)).toNat with hkn
  set D := kn + 3 * e with hD
  have hfinal : (4 : ℝ≥0∞) * 2 ^ D * 2⁻¹ ^ n =
      ((4 * 2 ^ (3 * e) : ℕ) : ℝ≥0∞) * 2 ^ kn * 2⁻¹ ^ n := by
    rw [hD, pow_add]; push_cast; ring
  refine le_trans ?_ hfinal.le
  by_cases hnD : D ≤ n
  · set k := n - D with hk
    have hsub : ∀ x, (if complexityOfComplexity U x = n then m x else 0) ≤
        (if 2 * mStage c (tk k) x ≤ m x then m x else 0) := by
      intro x
      split_ifs with h1 h2
      · exact le_rfl
      · exfalso
        have hb := hoff k x h2
        rw [h1] at hb
        have hA := hcA e n (omegaPrefix U k) (by rw [length_omegaPrefix]; omega)
        obtain ⟨ks, hks⟩ : ∃ ks : ℕ, KPPlain U (omegaPrefix U k) = ks :=
          ⟨_, (ENat.coe_toNat (KP_ne_top_of_optimal U hU _ [])).symm⟩
        rw [hks] at hb hA
        have hb' : n ≤ ks + C₃ := by exact_mod_cast hb
        have hA' : ks + e ≤ n + cA := by exact_mod_cast hA
        omega
      · exact zero_le
      · exact le_rfl
    calc ∑' x, (if complexityOfComplexity U x = n then m x else 0)
        ≤ ∑' x, (if 2 * mStage c (tk k) x ≤ m x then m x else 0) := ENNReal.tsum_le_tsum hsub
      _ ≤ 4 * 2⁻¹ ^ k := (hY k).le
      _ = 4 * 2 ^ D * 2⁻¹ ^ n := by rw [hk, inv_pow_sub_eq n D hnD, mul_assoc]
  · -- Small `n`: the total mass is at most `1`.
    rw [not_le] at hnD
    calc ∑' x, (if complexityOfComplexity U x = n then m x else 0) ≤ ∑' x, m x :=
          ENNReal.tsum_le_tsum fun x ↦ by split_ifs <;> simp
      _ ≤ 1 := tsum_aprioriMeasure_le_one U [] hpm
      _ = 2 ^ n * 2⁻¹ ^ n := by
          rw [← mul_pow, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]
      _ ≤ 4 * 2 ^ D * 2⁻¹ ^ n := by
          gcongr
          calc (2 : ℝ≥0∞) ^ n ≤ 2 ^ D := pow_le_pow_right₀ one_le_two hnD.le
            _ ≤ 4 * 2 ^ D := le_mul_of_one_le_left zero_le (by norm_num)

end Kolmogorov.Information.Halting
