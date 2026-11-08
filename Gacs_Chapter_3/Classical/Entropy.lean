/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Convex.Jensen
import KolmogorovMathlib.Prefix.Kraft

/-!
# Classical entropy, the log-sum inequality, Shannon's coding bound (Gács §3.1.1)

Distributions are functions `P : α → ℝ≥0∞` on a type `α` (in practice countable), of total
mass one. Entropy is measured in bits and is `ℝ≥0∞`-valued, so distributions with infinite
entropy are allowed and no summability side conditions appear:

  `entropy P = ∑ₓ −P(x) log₂ P(x)`   (**Definition 3.1.1**).

* **Theorem 3.1.1** (Csiszár's log-sum inequality, `log_sum_inequality`): for positive reals,
  `∑ aᵢ log (aᵢ/bᵢ) ≥ a log (a/b)`, with equality iff `aᵢ/bᵢ` is constant
  (`log_sum_eq_iff`); in particular `∑ aᵢ log (aᵢ/bᵢ) ≥ 0` when `∑ aᵢ = 1 ≥ ∑ bᵢ`
  (`log_sum_nonneg`). Proof: Jensen for the strictly convex `x log x`.
* **Gibbs' inequality** (`entropy_le_crossEntropy`): `H(P) ≤ ∑ₓ P(x) (−log₂ Q(x))` whenever
  `∑ Q ≤ 1`. Here `−log₂` is `negLog2 : ℝ≥0∞ → ℝ≥0∞` (value `⊤` at `0`). The proof is
  termwise, from `ln t ≤ t − 1`:
  `−p log₂ p + p/ln 2 ≤ p (−log₂ q) + q/ln 2`; summing and cancelling the finite `1/ln 2`
  gives the claim with no finiteness assumption on the entropy.
* With `Q(x) = 2^{-ℓ(x)}`: `entropy_le_tsum_mul_length`, `H(P) ≤ ∑ P(x) ℓ(x)` whenever
  `∑ 2^{-ℓ(x)} ≤ 1`.
* **Theorem 3.1.2** (Shannon, `shannon_coding_lb`): the expected codeword length of a prefix
  code is at least `H(P)`, via the Kraft inequality of the repository
  (`finset_kraft_real_le_one`).
-/

namespace Kolmogorov.Information.Classical

open scoped ENNReal

variable {α : Type*}

/-! ### `−log₂` on `ℝ≥0∞` and entropy -/

/-- `−log₂ q`, extended to `ℝ≥0∞` with value `⊤` at `0` (and `0` above `1`). -/
noncomputable def negLog2 (q : ℝ≥0∞) : ℝ≥0∞ :=
  if q = 0 then ⊤ else ENNReal.ofReal (-Real.logb 2 q.toReal)

/-- **Gács Definition 3.1.1.** The (Shannon) entropy of `P`, in bits. -/
noncomputable def entropy (P : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, ENNReal.ofReal (Real.negMulLog (P x).toReal / Real.log 2)

theorem log_two_pos' : 0 < Real.log 2 := Real.log_pos one_lt_two

@[simp] theorem negLog2_zero : negLog2 0 = ⊤ := by simp [negLog2]

theorem negLog2_of_ne_zero {q : ℝ≥0∞} (hq : q ≠ 0) :
    negLog2 q = ENNReal.ofReal (-Real.logb 2 q.toReal) := by
  simp [negLog2, hq]

theorem ne_top_of_le_one {p : ℝ≥0∞} (hp : p ≤ 1) : p ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top hp

/-- Writing a finite `p ∈ [0, 1]` as `ofReal r`. -/
theorem exists_ofReal_of_le_one {p : ℝ≥0∞} (hp : p ≤ 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r ≤ 1 ∧ p = ENNReal.ofReal r :=
  ⟨p.toReal, ENNReal.toReal_nonneg,
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp),
    (ENNReal.ofReal_toReal (ne_top_of_le_one hp)).symm⟩

theorem negLog2_ofReal {r : ℝ} (hr : 0 < r) :
    negLog2 (ENNReal.ofReal r) = ENNReal.ofReal (-Real.logb 2 r) := by
  rw [negLog2_of_ne_zero (by simpa using hr), ENNReal.toReal_ofReal hr.le]

/-- `−log₂ (2^{-ℓ}) = ℓ`. -/
theorem negLog2_inv_two_pow (ℓ : ℕ) : negLog2 ((2 : ℝ≥0∞)⁻¹ ^ ℓ) = ℓ := by
  have h0 : (2 : ℝ≥0∞)⁻¹ ^ ℓ ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
  have ht : ((2 : ℝ≥0∞)⁻¹ ^ ℓ).toReal = (2 : ℝ)⁻¹ ^ ℓ := by
    simp [ENNReal.toReal_pow, ENNReal.toReal_inv]
  rw [negLog2_of_ne_zero h0, ht, Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one one_lt_two]
  simp

/-- The entropy term is `p · (−log₂ p)`. -/
theorem ofReal_negMulLog_eq {p : ℝ≥0∞} (hp : p ≤ 1) :
    ENNReal.ofReal (Real.negMulLog p.toReal / Real.log 2) = p * negLog2 p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  obtain ⟨r, hr0, -, rfl⟩ := exists_ofReal_of_le_one hp
  have hr : 0 < r := by
    rcases hr0.eq_or_lt with h | h
    · exact absurd (by rw [← h]; simp) hp0
    · exact h
  rw [negLog2_ofReal hr, ENNReal.toReal_ofReal hr0, ← ENNReal.ofReal_mul hr0]
  congr 1
  unfold Real.negMulLog Real.logb
  ring

/-- **Entropy as an expectation**: `H(P) = ∑ₓ P(x) (−log₂ P(x))`. -/
theorem entropy_eq_tsum_mul_negLog2 {P : α → ℝ≥0∞} (hP : ∀ x, P x ≤ 1) :
    entropy P = ∑' x, P x * negLog2 (P x) :=
  tsum_congr fun x ↦ ofReal_negMulLog_eq (hP x)

/-! ### Theorem 3.1.1: the log-sum inequality -/

section LogSum

variable {ι : Type*} (t : Finset ι) (a b : ι → ℝ)

/-- The Jensen data: weights `bᵢ/b`, points `aᵢ/bᵢ`. -/
private theorem logSum_aux (ha : ∀ i ∈ t, 0 < a i) (hb : ∀ i ∈ t, 0 < b i) (ht : t.Nonempty) :
    let B := ∑ i ∈ t, b i
    (∀ i ∈ t, 0 < b i / B) ∧ (∑ i ∈ t, b i / B = 1) ∧ (∀ i ∈ t, a i / b i ∈ Set.Ici (0 : ℝ)) ∧
      (∑ i ∈ t, (b i / B) • (a i / b i) = (∑ i ∈ t, a i) / B) ∧
      (∑ i ∈ t, (b i / B) • ((a i / b i) * Real.log (a i / b i))
        = (∑ i ∈ t, a i * Real.log (a i / b i)) / B) := by
  intro B
  have hB : 0 < B := Finset.sum_pos hb ht
  refine ⟨fun i hi ↦ div_pos (hb i hi) hB, ?_, fun i hi ↦ Set.mem_Ici.mpr
    (div_pos (ha i hi) (hb i hi)).le, ?_, ?_⟩
  · rw [← Finset.sum_div, div_self hB.ne']
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have := (hb i hi).ne'
    simp only [smul_eq_mul]
    field_simp
  · rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have := (hb i hi).ne'
    simp only [smul_eq_mul]
    field_simp

/-- **Gács Theorem 3.1.1** (Csiszár's log-sum inequality). For positive `aᵢ, bᵢ` with
`a = ∑ aᵢ`, `b = ∑ bᵢ`: `∑ aᵢ log (aᵢ/bᵢ) ≥ a log (a/b)`. -/
theorem log_sum_inequality (ha : ∀ i ∈ t, 0 < a i) (hb : ∀ i ∈ t, 0 < b i) :
    (∑ i ∈ t, a i) * Real.log ((∑ i ∈ t, a i) / ∑ i ∈ t, b i)
      ≤ ∑ i ∈ t, a i * Real.log (a i / b i) := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
  obtain ⟨hw, hw1, hmem, hsum, hsumf⟩ := logSum_aux t a b ha hb ht
  have hB : 0 < ∑ i ∈ t, b i := Finset.sum_pos hb ht
  have hJ := Real.convexOn_mul_log.map_sum_le (fun i hi ↦ (hw i hi).le) hw1 hmem
  rw [hsum, hsumf] at hJ
  have e : (∑ i ∈ t, a i) / (∑ i ∈ t, b i) * Real.log ((∑ i ∈ t, a i) / ∑ i ∈ t, b i)
      * (∑ i ∈ t, b i) = (∑ i ∈ t, a i) * Real.log ((∑ i ∈ t, a i) / ∑ i ∈ t, b i) := by
    field_simp
  rw [← e, ← le_div_iff₀ hB]
  exact hJ

/-- **Equality case of Theorem 3.1.1**: equality holds iff `aᵢ/bᵢ = a/b` for all `i`. -/
theorem log_sum_eq_iff (ha : ∀ i ∈ t, 0 < a i) (hb : ∀ i ∈ t, 0 < b i) :
    ∑ i ∈ t, a i * Real.log (a i / b i)
        = (∑ i ∈ t, a i) * Real.log ((∑ i ∈ t, a i) / ∑ i ∈ t, b i) ↔
      ∀ i ∈ t, a i / b i = (∑ i ∈ t, a i) / ∑ i ∈ t, b i := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
  obtain ⟨hw, hw1, hmem, hsum, hsumf⟩ := logSum_aux t a b ha hb ht
  have hB : 0 < ∑ i ∈ t, b i := Finset.sum_pos hb ht
  have hiff := Real.strictConvexOn_mul_log.map_sum_eq_iff hw hw1 hmem
  rw [hsum, hsumf] at hiff
  rw [← hiff]
  have e : (∑ i ∈ t, a i) / (∑ i ∈ t, b i) * Real.log ((∑ i ∈ t, a i) / ∑ i ∈ t, b i)
      * (∑ i ∈ t, b i) = (∑ i ∈ t, a i) * Real.log ((∑ i ∈ t, a i) / ∑ i ∈ t, b i) := by
    field_simp
  rw [eq_div_iff hB.ne', e, eq_comm]

/-- The special case of Theorem 3.1.1: if `∑ aᵢ = 1` and `∑ bᵢ ≤ 1`, then
`∑ aᵢ log (aᵢ/bᵢ) ≥ 0`. -/
theorem log_sum_nonneg (ha : ∀ i ∈ t, 0 < a i) (hb : ∀ i ∈ t, 0 < b i)
    (ha1 : ∑ i ∈ t, a i = 1) (hb1 : ∑ i ∈ t, b i ≤ 1) :
    0 ≤ ∑ i ∈ t, a i * Real.log (a i / b i) := by
  refine le_trans ?_ (log_sum_inequality t a b ha hb)
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp at ha1
  have hB : 0 < ∑ i ∈ t, b i := Finset.sum_pos hb ht
  rw [ha1, one_mul, one_div]
  exact Real.log_nonneg (one_le_inv₀ hB |>.mpr hb1)

end LogSum

/-! ### Gibbs' inequality -/

/-- `−r ln r + r ≤ −r ln s + s` for `r ≥ 0`, `s > 0` (from `ln t ≤ t − 1`). -/
theorem negMulLog_add_le (r s : ℝ) (hr : 0 ≤ r) (hs : 0 < s) :
    Real.negMulLog r + r ≤ -r * Real.log s + s := by
  rcases hr.eq_or_lt with rfl | hr'
  · simp [hs.le]
  have h := Real.log_le_sub_one_of_pos (div_pos hs hr')
  rw [Real.log_div hs.ne' hr'.ne'] at h
  have h2 : r * (Real.log s - Real.log r) ≤ r * (s / r - 1) := mul_le_mul_of_nonneg_left h hr
  have h3 : r * (s / r) = s := by field_simp
  unfold Real.negMulLog
  nlinarith [h2, h3]

/-- The termwise Gibbs inequality in `ℝ≥0∞`:
`−p log₂ p + p/ln 2 ≤ p (−log₂ q) + q/ln 2` for `p, q ∈ [0, 1]`. -/
theorem gibbs_term {p q : ℝ≥0∞} (hp : p ≤ 1) (hq : q ≤ 1) :
    ENNReal.ofReal (Real.negMulLog p.toReal / Real.log 2) + p * ENNReal.ofReal (1 / Real.log 2)
      ≤ p * negLog2 q + q * ENNReal.ofReal (1 / Real.log 2) := by
  have hL := log_two_pos'
  by_cases hq0 : q = 0
  · by_cases hp0 : p = 0
    · simp [hp0]
    · rw [hq0, negLog2_zero, ENNReal.mul_top hp0]
      simp
  obtain ⟨r, hr0, hr1, rfl⟩ := exists_ofReal_of_le_one hp
  obtain ⟨s, hs0, hs1, rfl⟩ := exists_ofReal_of_le_one hq
  have hs : 0 < s := by
    rcases hs0.eq_or_lt with h | h
    · exact absurd (by rw [← h]; simp) hq0
    · exact h
  rw [negLog2_ofReal hs, ENNReal.toReal_ofReal hr0, ← ENNReal.ofReal_mul hr0,
    ← ENNReal.ofReal_mul hr0, ← ENNReal.ofReal_mul hs0]
  have hlogb : 0 ≤ -Real.logb 2 s := neg_nonneg.mpr (Real.logb_nonpos one_lt_two hs0 hs1)
  rw [← ENNReal.ofReal_add (div_nonneg (Real.negMulLog_nonneg hr0 hr1) hL.le)
      (mul_nonneg hr0 (by positivity)),
    ← ENNReal.ofReal_add (mul_nonneg hr0 hlogb) (mul_nonneg hs0 (by positivity))]
  refine ENNReal.ofReal_le_ofReal ?_
  have key := negMulLog_add_le r s hr0 hs
  have e1 : Real.negMulLog r / Real.log 2 + r * (1 / Real.log 2)
      = (Real.negMulLog r + r) / Real.log 2 := by ring
  have e2 : r * -Real.logb 2 s + s * (1 / Real.log 2) = (-r * Real.log s + s) / Real.log 2 := by
    unfold Real.logb; ring
  rw [e1, e2]
  exact div_le_div_of_nonneg_right key hL.le

/-- **Gibbs' inequality.** `H(P) ≤ ∑ₓ P(x) (−log₂ Q(x))` for a distribution `P` and any `Q`
with `∑ Q ≤ 1`. -/
theorem entropy_le_crossEntropy {P Q : α → ℝ≥0∞} (hP : ∑' x, P x = 1) (hQ : ∑' x, Q x ≤ 1) :
    entropy P ≤ ∑' x, P x * negLog2 (Q x) := by
  set A := ENNReal.ofReal (1 / Real.log 2) with hAdef
  have hA : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hP1 : ∀ x, P x ≤ 1 := fun x ↦ hP ▸ ENNReal.le_tsum x
  have hQ1 : ∀ x, Q x ≤ 1 := fun x ↦ (ENNReal.le_tsum x).trans hQ
  refine ENNReal.le_of_add_le_add_right hA ?_
  calc entropy P + A
      = ∑' x, (ENNReal.ofReal (Real.negMulLog (P x).toReal / Real.log 2) + P x * A) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, hP, one_mul]; rfl
    _ ≤ ∑' x, (P x * negLog2 (Q x) + Q x * A) :=
        ENNReal.tsum_le_tsum fun x ↦ gibbs_term (hP1 x) (hQ1 x)
    _ = (∑' x, P x * negLog2 (Q x)) + (∑' x, Q x) * A := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ (∑' x, P x * negLog2 (Q x)) + 1 * A := add_le_add le_rfl (mul_le_mul' hQ le_rfl)
    _ = (∑' x, P x * negLog2 (Q x)) + A := by rw [one_mul]

/-- **Gibbs with lengths.** If `∑ 2^{-ℓ(x)} ≤ 1` then `H(P) ≤ ∑ₓ P(x) ℓ(x)`. -/
theorem entropy_le_tsum_mul_length (P : α → ℝ≥0∞) (hP : ∑' x, P x = 1) (ℓ : α → ℕ)
    (hK : ∑' x, (2 : ℝ≥0∞)⁻¹ ^ ℓ x ≤ 1) : entropy P ≤ ∑' x, P x * ℓ x := by
  have h := entropy_le_crossEntropy (Q := fun x ↦ (2 : ℝ≥0∞)⁻¹ ^ ℓ x) hP hK
  simpa only [negLog2_inv_two_pow] using h

/-! ### Theorem 3.1.2: Shannon's lower bound for prefix codes -/

/-- `(1/2)^n` in `ℝ≥0∞`. -/
theorem inv_two_pow_eq_ofReal (n : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ n = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos two_pos]
  simp

/-- **Kraft's inequality for a countable prefix code.** -/
theorem kraft_tsum_le_one {z : α → BitString} (hz : ∀ x x', z x <+: z x' → x = x') :
    ∑' x, (2 : ℝ≥0∞)⁻¹ ^ (z x).length ≤ 1 := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s ↦ ?_
  have hinj : ∀ x ∈ s, ∀ x' ∈ s, z x = z x' → x = x' := fun x _ x' _ h ↦
    hz x x' (h ▸ List.prefix_rfl)
  rw [← Finset.sum_image (f := fun w : BitString ↦ (2 : ℝ≥0∞)⁻¹ ^ w.length) hinj]
  have hpf : IsPrefixFree ((s.image z : Finset BitString) : Set BitString) := by
    intro p hp q hq hpq
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hp)
    obtain ⟨x', _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hq)
    rw [hz x x' hpq]
  have h := finset_kraft_real_le_one _ hpf
  rw [Finset.sum_congr rfl (fun w _ ↦ inv_two_pow_eq_ofReal w.length),
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)]
  exact ENNReal.ofReal_le_one.mpr h

/-- **Gács Theorem 3.1.2** (Shannon). If `x ↦ z_x` is a prefix code (no codeword is a prefix
of another codeword), its expected codeword length is at least the entropy:
`∑ₓ P(x) |z_x| ≥ H(P)`. -/
theorem shannon_coding_lb (P : α → ℝ≥0∞) (hP : ∑' x, P x = 1) {z : α → BitString}
    (hz : ∀ x x', z x <+: z x' → x = x') : entropy P ≤ ∑' x, P x * (z x).length :=
  entropy_le_tsum_mul_length P hP (fun x ↦ (z x).length) (kraft_tsum_le_one hz)

end Kolmogorov.Information.Classical
