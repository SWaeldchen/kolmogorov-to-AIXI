/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Classical.Entropy
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-!
# Conditional entropy and mutual information (Gács §3.1.1, "Identities, inequalities")

A pair of discrete random variables `(X, Y)` is given by its joint law
`p : α × β → ℝ≥0∞` (total mass one); `marg1 p`, `marg2 p` are the laws of `X` and `Y`.
Everything is `ℝ≥0∞`-valued, so the identities below hold with **no finiteness assumption**;
differences are taken only where Gács takes them, under finite entropies.

* **Definition 3.1.2** (`condEntropy`): `H(Y∣X) = ∑ₓ P[X=x] H(P[Y=·∣X=x])`; it equals
  `∑ p(x,y) (−log₂ p(y∣x))` (`condEntropy_eq`).
* **Additivity** (`entropy_eq_add_condEntropy`): `H(X,Y) = H(X) + H(Y∣X)`.
* **Conditioning reduces entropy** (`condEntropy_le_coarsen`, `condEntropy_le_entropy`):
  `H(Y∣X) ≤ H(Y∣g(X)) ≤ H(Y)`; proved fibrewise from Gibbs' inequality.
* **Definition 3.1.3** (`mutualInfo`): `I(X:Y) = H(Y) − H(Y∣X)`.
* The **KL form** (`mutualInfoKL`, eq. (info-via-exp-val)): with Mathlib's
  `klFun t = t log t + 1 − t`, `∑ p₁(x)p₂(y) klFun (p(x,y)/(p₁(x)p₂(y))) / ln 2`. The identity
  `H(X,Y) + I_KL = H(X) + H(Y)` (`entropy_add_mutualInfoKL`) holds termwise in `ℝ≥0∞`; hence
  `I = I_KL` (`mutualInfo_eq_mutualInfoKL`), the symmetry `I(X:Y) = I(Y:X)`
  (`mutualInfo_swap`) and `I = H(X) + H(Y) − H(X,Y)` (`mutualInfo_eq_entropy_add_sub`) when
  `H(X), H(Y) < ∞`.
* **Proposition 3.1.4** (`mutualInfo_eq_zero_iff`): `I(X:Y) ≥ 0` (it is a sum of
  non-negative terms; equivalently `H(Y∣X) ≤ H(Y)`), and `I(X:Y) = 0` iff `X, Y` are
  independent.
* Three variables `(X₁, X₂, X₃)` with law `r : α × β × γ → ℝ≥0∞`: the **chain rule**
  `H((X₂,X₃)∣X₁) = H(X₂∣X₁) + H(X₃∣X₁,X₂)` (`condEntropy_chain`), the **data-processing
  identity** `I(X₁ : (X₂,X₃)) = I(X₁ : X₂) + I(X₁ : X₃ ∣ X₂)` (`mutualInfo_chain`), and the
  **triangle inequality** `H(X₃∣X₁) ≤ H(X₂∣X₁) + H(X₃∣X₂)` (`condEntropy_triangle`; Gács'
  `H(X∣Y) ≤ H(Z∣Y) + H(X∣Z)` with `X₁ = Y`, `X₂ = Z`, `X₃ = X`).
-/

namespace Kolmogorov.Information.Classical

open scoped ENNReal

variable {α β γ : Type*}

/-! ### Marginals -/

/-- The law of `X` from the joint law `p` of `(X, Y)`. -/
noncomputable def marg1 (p : α × β → ℝ≥0∞) (x : α) : ℝ≥0∞ := ∑' y, p (x, y)

/-- The law of `Y` from the joint law `p` of `(X, Y)`. -/
noncomputable def marg2 (p : α × β → ℝ≥0∞) (y : β) : ℝ≥0∞ := ∑' x, p (x, y)

theorem tsum_marg1 (p : α × β → ℝ≥0∞) : ∑' x, marg1 p x = ∑' z, p z :=
  ENNReal.tsum_prod'.symm

theorem tsum_marg2 (p : α × β → ℝ≥0∞) : ∑' y, marg2 p y = ∑' z, p z := by
  unfold marg2; rw [ENNReal.tsum_comm, ENNReal.tsum_prod']

theorem le_marg1 (p : α × β → ℝ≥0∞) (z : α × β) : p z ≤ marg1 p z.1 :=
  ENNReal.le_tsum (f := fun y ↦ p (z.1, y)) z.2

theorem le_marg2 (p : α × β → ℝ≥0∞) (z : α × β) : p z ≤ marg2 p z.2 :=
  ENNReal.le_tsum (f := fun x ↦ p (x, z.2)) z.1

theorem marg1_le_one {p : α × β → ℝ≥0∞} (hp : ∑' z, p z ≤ 1) (x : α) : marg1 p x ≤ 1 :=
  (ENNReal.le_tsum x).trans ((tsum_marg1 p).trans_le hp)

theorem marg2_le_one {p : α × β → ℝ≥0∞} (hp : ∑' z, p z ≤ 1) (y : β) : marg2 p y ≤ 1 :=
  (ENNReal.le_tsum y).trans ((tsum_marg2 p).trans_le hp)

theorem le_one_of_tsum_le_one {P : α → ℝ≥0∞} (hP : ∑' x, P x ≤ 1) (x : α) : P x ≤ 1 :=
  (ENNReal.le_tsum x).trans hP

/-! ### `−log₂` of a ratio -/

/-- `−log₂ (a/b) = log₂ b − log₂ a` for `0 < a ≤ b ≤ 1`. -/
theorem negLog2_div {a b : ℝ≥0∞} (ha : a ≠ 0) (hab : a ≤ b) (hb : b ≤ 1) :
    negLog2 (a / b) = ENNReal.ofReal (Real.logb 2 b.toReal - Real.logb 2 a.toReal) := by
  have hbt : b ≠ ⊤ := ne_top_of_le_one hb
  have hat : a ≠ ⊤ := ne_top_of_le_one (hab.trans hb)
  have hb0 : b ≠ 0 := ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr ha) hab)
  have hdiv : a / b ≠ 0 := by simp [ha, hbt]
  rw [negLog2_of_ne_zero hdiv, ENNReal.toReal_div,
    Real.logb_div (ENNReal.toReal_pos ha hat).ne' (ENNReal.toReal_pos hb0 hbt).ne']
  ring_nf

/-- Splitting `−log₂ (q/s)` at an intermediate `m`:
`q (−log₂ (q/s)) = q (−log₂ (m/s)) + q (−log₂ (q/m))` for `q ≤ m ≤ s ≤ 1`. -/
theorem mul_negLog2_div_split {q m s : ℝ≥0∞} (hqm : q ≤ m) (hms : m ≤ s) (hs : s ≤ 1) :
    q * negLog2 (q / s) = q * negLog2 (m / s) + q * negLog2 (q / m) := by
  by_cases hq : q = 0
  · simp [hq]
  have hm : m ≠ 0 := ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.mpr hq) hqm)
  have hmt : m ≠ ⊤ := ne_top_of_le_one (hms.trans hs)
  have hst : s ≠ ⊤ := ne_top_of_le_one hs
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq (ne_top_of_le_one (hqm.trans (hms.trans hs)))
  have hm' : 0 < m.toReal := ENNReal.toReal_pos hm hmt
  have h1 : Real.logb 2 m.toReal ≤ Real.logb 2 s.toReal :=
    Real.logb_le_logb_of_le one_lt_two hm' (ENNReal.toReal_mono hst hms)
  have h2 : Real.logb 2 q.toReal ≤ Real.logb 2 m.toReal :=
    Real.logb_le_logb_of_le one_lt_two hq' (ENNReal.toReal_mono hmt hqm)
  rw [negLog2_div hq (hqm.trans hms) hs, negLog2_div hm hms hs, negLog2_div hq hqm (hms.trans hs),
    ← mul_add, ← ENNReal.ofReal_add (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  congr 2
  ring

/-! ### Conditional entropy and additivity -/

/-- **Gács Definition 3.1.2.** The conditional entropy `H(Y∣X)` of the joint law `p` of
`(X, Y)`: `∑ₓ P[X = x] · H(P[Y = · ∣ X = x])`. -/
noncomputable def condEntropy (p : α × β → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' x, marg1 p x * entropy (fun y ↦ p (x, y) / marg1 p x)

/-- `H(Y∣X) = ∑ p(x,y) (−log₂ p(y∣x))`. -/
theorem condEntropy_eq (p : α × β → ℝ≥0∞) (hp : ∑' z, p z ≤ 1) :
    condEntropy p = ∑' z, p z * negLog2 (p z / marg1 p z.1) := by
  rw [ENNReal.tsum_prod']
  unfold condEntropy
  refine tsum_congr fun x ↦ ?_
  by_cases hx : marg1 p x = 0
  · have h0 : ∀ y, p (x, y) = 0 := fun y ↦ le_antisymm (hx ▸ le_marg1 p (x, y)) zero_le
    simp [hx, h0]
  · have hxt : marg1 p x ≠ ⊤ := ne_top_of_le_one (marg1_le_one hp x)
    have hc : ∀ y, p (x, y) / marg1 p x ≤ 1 := fun y ↦
      ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_marg1 p (x, y))
    rw [entropy_eq_tsum_mul_negLog2 hc, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun y ↦ ?_
    rw [← mul_assoc, ENNReal.mul_div_cancel hx hxt]

/-- `∑ p(x,y) (−log₂ p₁(x)) = H(X)`. -/
theorem tsum_mul_negLog2_marg1 (p : α × β → ℝ≥0∞) (hp : ∑' z, p z ≤ 1) :
    ∑' z, p z * negLog2 (marg1 p z.1) = entropy (marg1 p) := by
  rw [entropy_eq_tsum_mul_negLog2 (marg1_le_one hp), ENNReal.tsum_prod']
  refine tsum_congr fun x ↦ ?_
  dsimp only
  rw [ENNReal.tsum_mul_right]
  rfl

/-- `∑ p(x,y) (−log₂ p₂(y)) = H(Y)`. -/
theorem tsum_mul_negLog2_marg2 (p : α × β → ℝ≥0∞) (hp : ∑' z, p z ≤ 1) :
    ∑' z, p z * negLog2 (marg2 p z.2) = entropy (marg2 p) := by
  rw [entropy_eq_tsum_mul_negLog2 (marg2_le_one hp), ENNReal.tsum_prod', ENNReal.tsum_comm]
  refine tsum_congr fun y ↦ ?_
  dsimp only
  rw [ENNReal.tsum_mul_right]
  rfl

/-- **Additivity** (Gács eq. (entraddit)): `H(X,Y) = H(X) + H(Y∣X)`, in `ℝ≥0∞` with no
finiteness assumption. -/
theorem entropy_eq_add_condEntropy (p : α × β → ℝ≥0∞) (hp : ∑' z, p z ≤ 1) :
    entropy p = entropy (marg1 p) + condEntropy p := by
  rw [entropy_eq_tsum_mul_negLog2 (le_one_of_tsum_le_one hp), condEntropy_eq p hp,
    ← tsum_mul_negLog2_marg1 p hp, ← ENNReal.tsum_add]
  refine tsum_congr fun z ↦ ?_
  have h := mul_negLog2_div_split (le_marg1 p z) (marg1_le_one hp z.1) le_rfl
  simpa only [div_one] using h

/-! ### Conditioning reduces entropy -/

open _root_.Classical in
/-- The joint law of `(g(X), Y)` obtained from the joint law `p` of `(X, Y)`. -/
noncomputable def coarsen (g : α → γ) (p : α × β → ℝ≥0∞) : γ × β → ℝ≥0∞ :=
  fun w ↦ ∑' a, if w.1 = g a then p (a, w.2) else 0

/-- Regrouping a sum along the fibres of `g`. -/
theorem tsum_comp_coarsen (g : α → γ) (p : α × β → ℝ≥0∞) (F : γ → β → ℝ≥0∞) :
    ∑' z : α × β, p z * F (g z.1) z.2 = ∑' w : γ × β, coarsen g p w * F w.1 w.2 := by
  classical
  symm
  calc ∑' w : γ × β, coarsen g p w * F w.1 w.2
      = ∑' w : γ × β, ∑' a, (if w.1 = g a then p (a, w.2) * F w.1 w.2 else 0) := by
        refine tsum_congr fun w ↦ ?_
        unfold coarsen
        rw [← ENNReal.tsum_mul_right]
        refine tsum_congr fun a ↦ ?_
        split_ifs <;> simp
    _ = ∑' a, ∑' w : γ × β, (if w.1 = g a then p (a, w.2) * F w.1 w.2 else 0) :=
        ENNReal.tsum_comm
    _ = ∑' a, ∑' b, p (a, b) * F (g a) b := by
        refine tsum_congr fun a ↦ ?_
        rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
        refine tsum_congr fun b ↦ ?_
        rw [tsum_eq_single (g a)]
        · simp
        · intro c hc; simp [hc]
    _ = ∑' z : α × β, p z * F (g z.1) z.2 :=
        (ENNReal.tsum_prod' (f := fun z : α × β ↦ p z * F (g z.1) z.2)).symm

theorem tsum_coarsen (g : α → γ) (p : α × β → ℝ≥0∞) :
    ∑' w, coarsen g p w = ∑' z, p z := by
  have h := tsum_comp_coarsen g p (fun _ _ ↦ 1)
  simpa using h.symm

/-- **Conditioning on more reduces entropy**: `H(Y∣X) ≤ H(Y∣g(X))`. -/
theorem condEntropy_le_coarsen (g : α → γ) (p : α × β → ℝ≥0∞) (hp : ∑' z, p z = 1) :
    condEntropy p ≤ condEntropy (coarsen g p) := by
  set p' := coarsen g p with hp'
  have hsum' : ∑' w, p' w = 1 := (tsum_coarsen g p).trans hp
  have hstep : ∀ x, marg1 p x * entropy (fun y ↦ p (x, y) / marg1 p x)
      ≤ ∑' y, p (x, y) * negLog2 (p' (g x, y) / marg1 p' (g x)) := by
    intro x
    by_cases hx : marg1 p x = 0
    · rw [hx, zero_mul]; exact zero_le
    have hxt : marg1 p x ≠ ⊤ := ne_top_of_le_one (marg1_le_one hp.le x)
    have hc1 : ∑' y, p (x, y) / marg1 p x = 1 := by
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
      exact ENNReal.mul_inv_cancel hx hxt
    have hQ : ∑' y, p' (g x, y) / marg1 p' (g x) ≤ 1 := by
      simp_rw [div_eq_mul_inv]
      rw [ENNReal.tsum_mul_right]
      change marg1 p' (g x) * (marg1 p' (g x))⁻¹ ≤ 1
      rw [← div_eq_mul_inv]
      exact ENNReal.div_self_le_one
    calc marg1 p x * entropy (fun y ↦ p (x, y) / marg1 p x)
        ≤ marg1 p x * ∑' y, p (x, y) / marg1 p x * negLog2 (p' (g x, y) / marg1 p' (g x)) :=
          mul_le_mul' le_rfl (entropy_le_crossEntropy hc1 hQ)
      _ = ∑' y, p (x, y) * negLog2 (p' (g x, y) / marg1 p' (g x)) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun y ↦ ?_
          rw [← mul_assoc, ENNReal.mul_div_cancel hx hxt]
  calc condEntropy p
      ≤ ∑' x, ∑' y, p (x, y) * negLog2 (p' (g x, y) / marg1 p' (g x)) :=
        ENNReal.tsum_le_tsum hstep
    _ = ∑' z : α × β, p z * negLog2 (p' (g z.1, z.2) / marg1 p' (g z.1)) :=
        (ENNReal.tsum_prod' (f := fun z : α × β ↦
          p z * negLog2 (p' (g z.1, z.2) / marg1 p' (g z.1)))).symm
    _ = ∑' w, p' w * negLog2 (p' w / marg1 p' w.1) :=
        tsum_comp_coarsen g p (fun c b ↦ negLog2 (p' (c, b) / marg1 p' c))
    _ = condEntropy p' := (condEntropy_eq p' hsum'.le).symm

/-- `H(Y∣X) ≤ H(Y)`. -/
theorem condEntropy_le_entropy (p : α × β → ℝ≥0∞) (hp : ∑' z, p z = 1) :
    condEntropy p ≤ entropy (marg2 p) := by
  refine (condEntropy_le_coarsen (fun _ ↦ ()) p hp).trans (le_of_eq ?_)
  have hc : ∀ y, coarsen (fun _ : α ↦ ()) p ((), y) = marg2 p y := fun y ↦ by
    unfold coarsen marg2; simp
  have hm : marg1 (coarsen (fun _ : α ↦ ()) p) () = 1 := by
    unfold marg1; simp_rw [hc]; rw [tsum_marg2]; exact hp
  unfold condEntropy
  rw [tsum_eq_single ()]
  · rw [hm, one_mul]
    congr 1
    funext y
    rw [hc, div_one]
  · intro u hu; exact absurd (Subsingleton.elim u ()) hu

/-! ### Mutual information -/

/-- **Gács Definition 3.1.3.** The information in `X` about `Y`: `I(X:Y) = H(Y) − H(Y∣X)`. -/
noncomputable def mutualInfo (p : α × β → ℝ≥0∞) : ℝ≥0∞ :=
  entropy (marg2 p) - condEntropy p

/-- The KL summand `q · klFun (r/q) / ln 2 = (r log₂ (r/q) + (q − r)/ln 2)`. -/
noncomputable def klTerm (r q : ℝ) : ℝ := q * InformationTheory.klFun (r / q) / Real.log 2

/-- The KL form of mutual information (Gács eq. (info-via-exp-val)), as a sum of non-negative
terms: `∑ p₁(x)p₂(y) · klFun (p(x,y) / (p₁(x)p₂(y))) / ln 2`. -/
noncomputable def mutualInfoKL (p : α × β → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' z, ENNReal.ofReal (klTerm (p z).toReal (marg1 p z.1 * marg2 p z.2).toReal)

theorem klTerm_nonneg {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) : 0 ≤ klTerm r q :=
  div_nonneg (mul_nonneg hq (InformationTheory.klFun_nonneg (div_nonneg hr hq)))
    log_two_pos'.le

/-- The real identity behind the KL form. -/
theorem kl_identity {r σ τ : ℝ} (hr : 0 < r) (hσ : 0 < σ) (hτ : 0 < τ) :
    Real.negMulLog r + σ * τ * InformationTheory.klFun (r / (σ * τ)) + r
      = r * -Real.log σ + r * -Real.log τ + σ * τ := by
  unfold Real.negMulLog InformationTheory.klFun
  rw [Real.log_div hr.ne' (mul_pos hσ hτ).ne', Real.log_mul hσ.ne' hτ.ne']
  field_simp
  ring

/-- The termwise form of `H(X,Y) + I = H(X) + H(Y)`. -/
theorem kl_term_eq {r s t : ℝ≥0∞} (hrs : r ≤ s) (hrt : r ≤ t) (hs : s ≤ 1) (ht : t ≤ 1) :
    ENNReal.ofReal (Real.negMulLog r.toReal / Real.log 2)
        + ENNReal.ofReal (klTerm r.toReal (s * t).toReal) + r * ENNReal.ofReal (1 / Real.log 2)
      = r * negLog2 s + r * negLog2 t + s * t * ENNReal.ofReal (1 / Real.log 2) := by
  have hL := log_two_pos'
  obtain ⟨σ, hσ0, -, rfl⟩ := exists_ofReal_of_le_one hs
  obtain ⟨τ, hτ0, -, rfl⟩ := exists_ofReal_of_le_one ht
  have hst : (ENNReal.ofReal σ * ENNReal.ofReal τ).toReal = σ * τ := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hσ0, ENNReal.toReal_ofReal hτ0]
  have hstA : ENNReal.ofReal σ * ENNReal.ofReal τ * ENNReal.ofReal (1 / Real.log 2)
      = ENNReal.ofReal (σ * τ / Real.log 2) := by
    rw [← ENNReal.ofReal_mul hσ0, ← ENNReal.ofReal_mul (mul_nonneg hσ0 hτ0)]
    congr 1; ring
  rw [hst, hstA]
  by_cases hr0 : r = 0
  · subst hr0
    simp [klTerm, InformationTheory.klFun_zero]
  obtain ⟨ρ, hρ0, -, rfl⟩ := exists_ofReal_of_le_one (hrs.trans hs)
  have hρ : 0 < ρ := by
    rcases hρ0.eq_or_lt with h | h
    · exact absurd (by rw [← h]; simp) hr0
    · exact h
  have hσ : 0 < σ := by
    have := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hρ) hrs
    exact ENNReal.ofReal_pos.mp this
  have hτ : 0 < τ := by
    have := lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hρ) hrt
    exact ENNReal.ofReal_pos.mp this
  rw [negLog2_ofReal hσ, negLog2_ofReal hτ, ENNReal.toReal_ofReal hρ0,
    ← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_mul hρ0, ← ENNReal.ofReal_mul hρ0]
  have hlσ : 0 ≤ -Real.logb 2 σ := neg_nonneg.mpr (Real.logb_nonpos one_lt_two hσ0
    (ENNReal.ofReal_le_one.mp hs))
  have hlτ : 0 ≤ -Real.logb 2 τ := neg_nonneg.mpr (Real.logb_nonpos one_lt_two hτ0
    (ENNReal.ofReal_le_one.mp ht))
  rw [← ENNReal.ofReal_add (div_nonneg (Real.negMulLog_nonneg hρ0
      (ENNReal.ofReal_le_one.mp (hrs.trans hs))) hL.le)
      (klTerm_nonneg hρ0 (mul_nonneg hσ0 hτ0)),
    ← ENNReal.ofReal_add (add_nonneg (div_nonneg (Real.negMulLog_nonneg hρ0
      (ENNReal.ofReal_le_one.mp (hrs.trans hs))) hL.le)
      (klTerm_nonneg hρ0 (mul_nonneg hσ0 hτ0))) (mul_nonneg hρ0 (by positivity)),
    ← ENNReal.ofReal_add (mul_nonneg hρ0 hlσ) (mul_nonneg hρ0 hlτ),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hρ0 hlσ) (mul_nonneg hρ0 hlτ))
      (by positivity)]
  congr 1
  have key := kl_identity hρ hσ hτ
  unfold klTerm Real.logb
  field_simp
  linear_combination key

/-- `H(X,Y) + I_KL(X:Y) = H(X) + H(Y)`, in `ℝ≥0∞` with no finiteness assumption. -/
theorem entropy_add_mutualInfoKL (p : α × β → ℝ≥0∞) (hp : ∑' z, p z = 1) :
    entropy p + mutualInfoKL p = entropy (marg1 p) + entropy (marg2 p) := by
  set A := ENNReal.ofReal (1 / Real.log 2) with hAdef
  have hA : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hm : ∑' z : α × β, marg1 p z.1 * marg2 p z.2 = 1 := by
    rw [ENNReal.tsum_prod']
    simp_rw [ENNReal.tsum_mul_left, tsum_marg2, hp, mul_one]
    rw [tsum_marg1, hp]
  refine (ENNReal.add_left_inj hA).mp ?_
  calc entropy p + mutualInfoKL p + A
      = ∑' z, (ENNReal.ofReal (Real.negMulLog (p z).toReal / Real.log 2)
          + ENNReal.ofReal (klTerm (p z).toReal (marg1 p z.1 * marg2 p z.2).toReal)
          + p z * A) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hp, one_mul]; rfl
    _ = ∑' z, (p z * negLog2 (marg1 p z.1) + p z * negLog2 (marg2 p z.2)
          + marg1 p z.1 * marg2 p z.2 * A) :=
        tsum_congr fun z ↦ kl_term_eq (le_marg1 p z) (le_marg2 p z) (marg1_le_one hp.le z.1)
          (marg2_le_one hp.le z.2)
    _ = entropy (marg1 p) + entropy (marg2 p) + A := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, tsum_mul_negLog2_marg1 p hp.le,
          tsum_mul_negLog2_marg2 p hp.le, ENNReal.tsum_mul_right, hm, one_mul]

/-- `H(Y∣X) + I_KL(X:Y) = H(Y)` when `H(X) < ∞`. -/
theorem condEntropy_add_mutualInfoKL (p : α × β → ℝ≥0∞) (hp : ∑' z, p z = 1)
    (h1 : entropy (marg1 p) ≠ ⊤) : condEntropy p + mutualInfoKL p = entropy (marg2 p) := by
  have h := entropy_add_mutualInfoKL p hp
  rw [entropy_eq_add_condEntropy p hp.le, add_assoc] at h
  exact (ENNReal.add_right_inj h1).mp h

/-- `I(X:Y) + H(Y∣X) = H(Y)` (no finiteness assumption). -/
theorem mutualInfo_add_condEntropy (p : α × β → ℝ≥0∞) (hp : ∑' z, p z = 1) :
    mutualInfo p + condEntropy p = entropy (marg2 p) :=
  tsub_add_cancel_of_le (condEntropy_le_entropy p hp)

/-- **Def 3.1.3 equals the KL form** (Gács eq. (info-via-exp-val)) when `H(X), H(Y) < ∞`. -/
theorem mutualInfo_eq_mutualInfoKL (p : α × β → ℝ≥0∞) (hp : ∑' z, p z = 1)
    (h1 : entropy (marg1 p) ≠ ⊤) (h2 : entropy (marg2 p) ≠ ⊤) :
    mutualInfo p = mutualInfoKL p := by
  have hc : condEntropy p ≠ ⊤ := ne_top_of_le_ne_top h2 (condEntropy_le_entropy p hp)
  unfold mutualInfo
  rw [← condEntropy_add_mutualInfoKL p hp h1, ENNReal.add_sub_cancel_left hc]

/-- `H(X,Y) < ∞` when `H(X), H(Y) < ∞`. -/
theorem entropy_ne_top (p : α × β → ℝ≥0∞) (hp : ∑' z, p z = 1)
    (h1 : entropy (marg1 p) ≠ ⊤) (h2 : entropy (marg2 p) ≠ ⊤) : entropy p ≠ ⊤ := by
  rw [entropy_eq_add_condEntropy p hp.le]
  exact ENNReal.add_ne_top.mpr ⟨h1, ne_top_of_le_ne_top h2 (condEntropy_le_entropy p hp)⟩

/-- `I(X:Y) = H(X) + H(Y) − H(X,Y)` when `H(X), H(Y) < ∞`. -/
theorem mutualInfo_eq_entropy_add_sub (p : α × β → ℝ≥0∞) (hp : ∑' z, p z = 1)
    (h1 : entropy (marg1 p) ≠ ⊤) (h2 : entropy (marg2 p) ≠ ⊤) :
    mutualInfo p = entropy (marg1 p) + entropy (marg2 p) - entropy p := by
  rw [mutualInfo_eq_mutualInfoKL p hp h1 h2, ← entropy_add_mutualInfoKL p hp,
    ENNReal.add_sub_cancel_left (entropy_ne_top p hp h1 h2)]

/-- The joint law of `(Y, X)`. -/
def swapJoint (p : α × β → ℝ≥0∞) : β × α → ℝ≥0∞ := fun w ↦ p w.swap

theorem tsum_swapJoint (p : α × β → ℝ≥0∞) : ∑' w, swapJoint p w = ∑' z, p z :=
  (Equiv.prodComm β α).tsum_eq p

theorem mutualInfoKL_swap (p : α × β → ℝ≥0∞) : mutualInfoKL (swapJoint p) = mutualInfoKL p := by
  unfold mutualInfoKL
  rw [← (Equiv.prodComm α β).tsum_eq]
  refine tsum_congr fun z ↦ ?_
  simp only [Equiv.prodComm_apply, swapJoint, Prod.swap_swap, Prod.fst_swap, Prod.snd_swap]
  congr 3
  unfold marg1 marg2 swapJoint
  simp only [Prod.swap_prod_mk]
  ring

/-- **Symmetry** `I(X:Y) = I(Y:X)` when `H(X), H(Y) < ∞`. -/
theorem mutualInfo_swap (p : α × β → ℝ≥0∞) (hp : ∑' z, p z = 1)
    (h1 : entropy (marg1 p) ≠ ⊤) (h2 : entropy (marg2 p) ≠ ⊤) :
    mutualInfo (swapJoint p) = mutualInfo p := by
  have hs : ∑' w, swapJoint p w = 1 := (tsum_swapJoint p).trans hp
  rw [mutualInfo_eq_mutualInfoKL p hp h1 h2,
    mutualInfo_eq_mutualInfoKL (swapJoint p) hs h2 h1, mutualInfoKL_swap]

/-- One KL summand vanishes iff `p(x,y) = p₁(x) p₂(y)`. -/
theorem ofReal_klTerm_eq_zero_iff {r s t : ℝ≥0∞} (hrs : r ≤ s) (hrt : r ≤ t) (hs : s ≤ 1)
    (ht : t ≤ 1) : ENNReal.ofReal (klTerm r.toReal (s * t).toReal) = 0 ↔ r = s * t := by
  obtain ⟨σ, hσ0, -, rfl⟩ := exists_ofReal_of_le_one hs
  obtain ⟨τ, hτ0, -, rfl⟩ := exists_ofReal_of_le_one ht
  obtain ⟨ρ, hρ0, -, rfl⟩ := exists_ofReal_of_le_one (hrs.trans hs)
  rw [← ENNReal.ofReal_mul hσ0, ENNReal.toReal_ofReal hρ0,
    ENNReal.toReal_ofReal (mul_nonneg hσ0 hτ0), ENNReal.ofReal_eq_zero]
  have hnn := klTerm_nonneg hρ0 (mul_nonneg hσ0 hτ0)
  rcases (mul_nonneg hσ0 hτ0).eq_or_lt with hq | hq
  · -- `p₁ p₂ = 0` forces `p = 0`
    have hρ : ρ = 0 := by
      rcases mul_eq_zero.mp hq.symm with h | h
      · subst h; exact le_antisymm (by simpa using hrs) hρ0
      · subst h; exact le_antisymm (by simpa using hrt) hρ0
    subst hρ
    simp [← hq, klTerm]
  · constructor
    · intro h
      have h0 : klTerm ρ (σ * τ) = 0 := le_antisymm h hnn
      unfold klTerm at h0
      have hk : InformationTheory.klFun (ρ / (σ * τ)) = 0 := by
        rcases mul_eq_zero.mp (div_eq_zero_iff.mp h0 |>.resolve_right log_two_pos'.ne') with
          h' | h'
        · exact absurd h' hq.ne'
        · exact h'
      rw [InformationTheory.klFun_eq_zero_iff (div_nonneg hρ0 hq.le), div_eq_one_iff_eq hq.ne']
        at hk
      rw [hk]
    · intro h
      have hρ : ρ = σ * τ := by
        have := congrArg ENNReal.toReal h
        rwa [ENNReal.toReal_ofReal hρ0, ENNReal.toReal_ofReal (mul_nonneg hσ0 hτ0)] at this
      rw [hρ]
      unfold klTerm
      rw [div_self hq.ne', InformationTheory.klFun_one]
      simp

/-- **Gács Proposition 3.1.4.** When `H(X), H(Y) < ∞`, `I(X:Y) = 0` iff `X` and `Y` are
independent. (Non-negativity is automatic: `I` is the sum of the non-negative KL terms,
`mutualInfo_eq_mutualInfoKL`; equivalently `H(Y∣X) ≤ H(Y)`, `condEntropy_le_entropy`.) -/
theorem mutualInfo_eq_zero_iff (p : α × β → ℝ≥0∞) (hp : ∑' z, p z = 1)
    (h1 : entropy (marg1 p) ≠ ⊤) (h2 : entropy (marg2 p) ≠ ⊤) :
    mutualInfo p = 0 ↔ ∀ z, p z = marg1 p z.1 * marg2 p z.2 := by
  rw [mutualInfo_eq_mutualInfoKL p hp h1 h2, mutualInfoKL, ENNReal.tsum_eq_zero]
  exact forall_congr' fun z ↦ ofReal_klTerm_eq_zero_iff (le_marg1 p z) (le_marg2 p z)
    (marg1_le_one hp.le z.1) (marg2_le_one hp.le z.2)

/-! ### Three variables: chain rule, data processing, triangle inequality -/

section Three

variable (r : α × β × γ → ℝ≥0∞)

/-- The law of `(X₁, X₂)` from the law `r` of `(X₁, X₂, X₃)`. -/
noncomputable def marg12 : α × β → ℝ≥0∞ := fun w ↦ ∑' c, r (w.1, w.2, c)

/-- The law of `(X₁, X₃)`. -/
noncomputable def marg13 : α × γ → ℝ≥0∞ := fun w ↦ ∑' b, r (w.1, b, w.2)

/-- The law of `(X₂, X₃)`. -/
noncomputable def marg23 : β × γ → ℝ≥0∞ := marg2 r

/-- The law of `((X₁, X₂), X₃)`: conditioning on the pair `(X₁, X₂)`. -/
def assoc : (α × β) × γ → ℝ≥0∞ := fun w ↦ r (w.1.1, w.1.2, w.2)

/-- The law of `(X₁, X₃, X₂)`. -/
def swap23 : α × γ × β → ℝ≥0∞ := fun w ↦ r (w.1, w.2.2, w.2.1)

/-- The conditional information `I(X₁ : X₃ ∣ X₂) = H(X₃∣X₂) − H(X₃∣X₁,X₂)`. -/
noncomputable def condMutualInfo : ℝ≥0∞ := condEntropy (marg23 r) - condEntropy (assoc r)

theorem tsum_assoc : ∑' w, assoc r w = ∑' w, r w :=
  (Equiv.prodAssoc α β γ).tsum_eq r

theorem tsum_swap23 : ∑' w, swap23 r w = ∑' w, r w :=
  (Equiv.prodCongr (Equiv.refl α) (Equiv.prodComm γ β)).tsum_eq r

theorem tsum_marg12 : ∑' w, marg12 r w = ∑' w, r w := by
  unfold marg12
  rw [ENNReal.tsum_prod', ENNReal.tsum_prod']
  refine tsum_congr fun a ↦ ?_
  exact (ENNReal.tsum_prod' (f := fun bc : β × γ ↦ r (a, bc))).symm

theorem marg1_marg12 : marg1 (marg12 r) = marg1 r := by
  funext a
  unfold marg1 marg12
  exact (ENNReal.tsum_prod' (f := fun bc : β × γ ↦ r (a, bc))).symm

theorem marg2_marg12 : marg2 (marg12 r) = marg1 (marg23 r) := by
  funext b
  unfold marg1 marg2 marg12 marg23 marg2
  exact ENNReal.tsum_comm

theorem marg12_le_marg1 (w : α × β) : marg12 r w ≤ marg1 r w.1 := by
  rw [← marg1_marg12]; exact le_marg1 _ w

/-- **Chain rule** `H((X₂,X₃)∣X₁) = H(X₂∣X₁) + H(X₃∣X₁,X₂)` (no finiteness assumption). -/
theorem condEntropy_chain (hr : ∑' w, r w ≤ 1) :
    condEntropy r = condEntropy (marg12 r) + condEntropy (assoc r) := by
  rw [condEntropy_eq r hr, condEntropy_eq (marg12 r) ((tsum_marg12 r).trans_le hr),
    condEntropy_eq (assoc r) ((tsum_assoc r).trans_le hr), marg1_marg12]
  have hsplit : ∀ w : α × β × γ, r w * negLog2 (r w / marg1 r w.1)
      = r w * negLog2 (marg12 r (w.1, w.2.1) / marg1 r w.1)
        + r w * negLog2 (r w / marg12 r (w.1, w.2.1)) := fun w ↦
    mul_negLog2_div_split (ENNReal.le_tsum (f := fun c ↦ r (w.1, w.2.1, c)) w.2.2)
      (marg12_le_marg1 r (w.1, w.2.1)) (marg1_le_one hr w.1)
  rw [tsum_congr hsplit, ENNReal.tsum_add]
  congr 1
  · rw [ENNReal.tsum_prod', ENNReal.tsum_prod']
    refine tsum_congr fun a ↦ ?_
    rw [ENNReal.tsum_prod']
    refine tsum_congr fun b ↦ ?_
    dsimp only
    rw [ENNReal.tsum_mul_right]
    rfl
  · rw [← (Equiv.prodAssoc α β γ).tsum_eq]
    rfl

theorem marg1_swap23 : marg1 (swap23 r) = marg1 r := by
  funext a
  unfold marg1 swap23
  exact (Equiv.prodComm γ β).tsum_eq (fun bc ↦ r (a, bc))

/-- Swapping `X₂, X₃` does not change `H((X₂,X₃)∣X₁)`. -/
theorem condEntropy_swap23 (hr : ∑' w, r w ≤ 1) : condEntropy (swap23 r) = condEntropy r := by
  rw [condEntropy_eq (swap23 r) ((tsum_swap23 r).trans_le hr), condEntropy_eq r hr,
    marg1_swap23, ← (Equiv.prodCongr (Equiv.refl α) (Equiv.prodComm β γ)).tsum_eq]
  rfl

theorem coarsen_snd_assoc : coarsen Prod.snd (assoc r) = marg23 r := by
  classical
  funext w
  unfold coarsen assoc marg23 marg2
  rw [ENNReal.tsum_prod']
  refine tsum_congr fun a ↦ ?_
  rw [tsum_eq_single w.1]
  · simp
  · intro b hb; simp [Ne.symm hb]

/-- `H(X₃∣X₁,X₂) ≤ H(X₃∣X₂)`. -/
theorem condEntropy_assoc_le (hr : ∑' w, r w = 1) :
    condEntropy (assoc r) ≤ condEntropy (marg23 r) := by
  rw [← coarsen_snd_assoc]
  exact condEntropy_le_coarsen Prod.snd (assoc r) ((tsum_assoc r).trans hr)

/-- `(a + b) − (c + d) = (a − c) + (b − d)` for `c ≤ a < ∞`, `d ≤ b < ∞`. -/
theorem add_tsub_add_eq {a b c d : ℝ≥0∞} (hca : c ≤ a) (hdb : d ≤ b) (ha : a ≠ ⊤)
    (hb : b ≠ ⊤) : a + b - (c + d) = (a - c) + (b - d) := by
  refine ENNReal.sub_eq_of_eq_add (ENNReal.add_ne_top.mpr
    ⟨ne_top_of_le_ne_top ha hca, ne_top_of_le_ne_top hb hdb⟩) ?_
  calc a + b = (a - c + c) + (b - d + d) := by
        rw [tsub_add_cancel_of_le hca, tsub_add_cancel_of_le hdb]
    _ = (a - c) + (b - d) + (c + d) := by ring

/-- **Classical data-processing identity** `I(X₁ : (X₂,X₃)) = I(X₁ : X₂) + I(X₁ : X₃ ∣ X₂)`
(Gács eq. (data-proc-ident) with `Z = X₁`, `X = X₂`, `Y = X₃`), when `H(X₂), H(X₃) < ∞`. -/
theorem mutualInfo_chain (hr : ∑' w, r w = 1) (h2 : entropy (marg1 (marg23 r)) ≠ ⊤)
    (h3 : entropy (marg2 (marg23 r)) ≠ ⊤) :
    mutualInfo r = mutualInfo (marg12 r) + condMutualInfo r := by
  have h23 : ∑' w, marg23 r w = 1 := (tsum_marg2 r).trans hr
  have h12 : ∑' w, marg12 r w = 1 := (tsum_marg12 r).trans hr
  have hC32 : condEntropy (marg23 r) ≤ entropy (marg2 (marg23 r)) :=
    condEntropy_le_entropy _ h23
  have hC21 : condEntropy (marg12 r) ≤ entropy (marg1 (marg23 r)) := by
    rw [← marg2_marg12]; exact condEntropy_le_entropy _ h12
  unfold mutualInfo condMutualInfo
  rw [show marg2 r = marg23 r from rfl, entropy_eq_add_condEntropy (marg23 r) h23.le,
    condEntropy_chain r hr.le, marg2_marg12]
  exact add_tsub_add_eq hC21 (condEntropy_assoc_le r hr) h2
    (ne_top_of_le_ne_top h3 hC32)

/-- **Classical triangle inequality** `H(X₃∣X₁) ≤ H(X₂∣X₁) + H(X₃∣X₂)` (Gács:
`H(X∣Y) ≤ H(Z∣Y) + H(X∣Z)`, with `X₁ = Y`, `X₂ = Z`, `X₃ = X`). -/
theorem condEntropy_triangle (hr : ∑' w, r w = 1) :
    condEntropy (marg13 r) ≤ condEntropy (marg12 r) + condEntropy (marg23 r) := by
  have hs : ∑' w, swap23 r w ≤ 1 := ((tsum_swap23 r).trans hr).le
  calc condEntropy (marg13 r) = condEntropy (marg12 (swap23 r)) := rfl
    _ ≤ condEntropy (marg12 (swap23 r)) + condEntropy (assoc (swap23 r)) := le_self_add
    _ = condEntropy (swap23 r) := (condEntropy_chain (swap23 r) hs).symm
    _ = condEntropy r := condEntropy_swap23 r hr.le
    _ = condEntropy (marg12 r) + condEntropy (assoc r) := condEntropy_chain r hr.le
    _ ≤ condEntropy (marg12 r) + condEntropy (marg23 r) :=
        add_le_add le_rfl (condEntropy_assoc_le r hr)

end Three

end Kolmogorov.Information.Classical
