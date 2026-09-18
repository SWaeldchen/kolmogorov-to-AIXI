/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.ContTrimComputable

/-!
# Gács Theorem 2.3.5: the universal continuous semimeasure `M`

There is a lower semicomputable continuous semimeasure `M` such that every lower
semicomputable continuous semimeasure `ν` satisfies `2^{-c} ν ≤ M` for some `c`.

`M(x) = ∑_i 2^{-(i+1)} ν_i(x)`, where `ν_i` is the trimmed limit of the `i`-th enumerated
approximation (`enumSemimeasure`). Each `ν_i` is a continuous semimeasure
(`isContSemimeasure_iSup_trimSt`); when the `i`-th approximation converges to a genuine
continuous semimeasure `ν`, trimming leaves it unchanged (`iSup_trimSt_eq`), so `ν = ν_i`
and `M ≥ 2^{-(i+1)} ν`. Lower semicomputability of the mixture is the repository's
`isLSC_unaryMixture_dyadicWeight_of_uniform`, fed the primitive recursive family
`trimSt (enumApprox i)`.
-/

namespace Kolmogorov

open scoped ENNReal

/-- The doubling law for the monotonised enumeration. -/
theorem enumApprox_double (i s : ℕ) (y : BitString) :
    2 * enumApprox i s y ≤ enumApprox i (s + 1) y := by
  unfold enumApprox
  exact le_max_left _ _

/-- The `i`-th enumerated continuous semimeasure. -/
noncomputable def enumSemimeasure (i : ℕ) (x : BitString) : ℝ≥0∞ :=
  ⨆ s, dyadicValue (trimSt (enumApprox i) s x) s

theorem enumSemimeasure_isContSemimeasure (i : ℕ) : IsContSemimeasure (enumSemimeasure i) :=
  isContSemimeasure_iSup_trimSt (fun s y ↦ enumApprox_double i s y)

/-- **The universal continuous semimeasure** `M`. -/
noncomputable def univContSemimeasure (x : BitString) : ℝ≥0∞ :=
  ∑' i, dyadicWeight i * enumSemimeasure i x

/-- Universality for continuous semimeasures, packaged. -/
def IsUniversalContSemimeasure (M : BitString → ℝ≥0∞) : Prop :=
  IsContSemimeasure M ∧ IsLSC₁ M ∧
    ∀ ν, IsContSemimeasure ν → IsLSC₁ ν → ∃ c : ℕ, ∀ x, 2⁻¹ ^ c * ν x ≤ M x

theorem univContSemimeasure_isContSemimeasure : IsContSemimeasure univContSemimeasure := by
  refine ⟨?_, fun x ↦ ?_⟩
  · calc ∑' i, dyadicWeight i * enumSemimeasure i [] ≤ ∑' i, dyadicWeight i * 1 :=
          ENNReal.tsum_le_tsum fun i ↦ mul_le_mul' le_rfl (enumSemimeasure_isContSemimeasure i).1
      _ = 1 := by simp [tsum_dyadicWeight]
  · unfold univContSemimeasure
    rw [← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i ↦ ?_
    rw [← mul_add]
    exact mul_le_mul' le_rfl ((enumSemimeasure_isContSemimeasure i).2 x)

theorem univContSemimeasure_isLSC₁ : IsLSC₁ univContSemimeasure := by
  have h := isLSC_unaryMixture_dyadicWeight_of_uniform
    (fun i out _ ↦ enumSemimeasure i out)
    (fun i s out _ ↦ trimSt (enumApprox i) s out)
    (fun i s out _ ↦ trimSt_dyadic_mono (fun s y ↦ enumApprox_double i s y) s out)
    (fun i out _ ↦ rfl)
    ((trimSt_enumApprox_primrec.comp (Primrec.pair
      (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))).to_comp)
  exact IsLSC.toUnary h

/-- **Domination.** Every lower semicomputable continuous semimeasure is one of the
trimmed components, up to the weight. -/
theorem contSemimeasure_le_univ {ν : BitString → ℝ≥0∞} (hν : IsContSemimeasure ν)
    (hlsc : IsLSC₁ ν) : ∃ c : ℕ, ∀ x, 2⁻¹ ^ c * ν x ≤ univContSemimeasure x := by
  obtain ⟨a, hmono, hsup, hcomp⟩ := hlsc
  obtain ⟨i, hi⟩ := exists_approxEnum (fun s x _ ↦ a s x)
    (hcomp.comp (Computable.pair Computable.fst (Computable.fst.comp Computable.snd)))
  -- The monotonised enumerated approximation converges to `ν`.
  have hsupψ : ∀ x, ⨆ s, dyadicValue (enumApprox i s x) s = ν x := by
    intro x
    unfold enumApprox
    rw [iSup_makeMono_eq_iSup, hi x [], hsup x]
  have hle : ∀ s x, dyadicValue (enumApprox i s x) s ≤ ν x := fun s x ↦ by
    rw [← hsupψ x]; exact le_iSup (fun s ↦ dyadicValue (enumApprox i s x) s) s
  have heq : ∀ x, enumSemimeasure i x = ν x := fun x ↦
    iSup_trimSt_eq hν (fun s y ↦ enumApprox_double i s y) hle hsupψ x
  refine ⟨i + 1, fun x ↦ ?_⟩
  rw [← heq x]
  exact ENNReal.le_tsum (f := fun i ↦ dyadicWeight i * enumSemimeasure i x) i

/-- **Gács Theorem 2.3.5.** `univContSemimeasure` is a universal lower semicomputable
continuous semimeasure. -/
theorem univContSemimeasure_isUniversal : IsUniversalContSemimeasure univContSemimeasure :=
  ⟨univContSemimeasure_isContSemimeasure, univContSemimeasure_isLSC₁,
    fun _ hν hlsc ↦ contSemimeasure_le_univ hν hlsc⟩

/-- **Gács Theorem 2.3.5**, existential form. -/
theorem exists_universalContSemimeasure : ∃ M, IsUniversalContSemimeasure M :=
  ⟨_, univContSemimeasure_isUniversal⟩

end Kolmogorov
