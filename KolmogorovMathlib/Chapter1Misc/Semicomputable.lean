/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.AlgorithmicProbability.UniversalSemimeasure
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.Foundation.UnboundedSearch
import KolmogorovMathlib.Chapter1Misc.Levin
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Fin

/-!
# Gács Propositions 1.5.5 and 1.6.8: semicomputable functions

## Lower semicomputability, unary

The repository's notion of lower semicomputability, `IsLSC`, is for *conditional*
functions `BitString → BitString → ℝ≥0∞`, with dyadic approximations
`approx s x ctx / 2^s` nondecreasing in the stage `s` and computable. `IsLSC₁` is the
same notion for one-argument functions, and `IsLSC.toUnary` connects the two, so that
every `IsLowerSemicomputableSemimeasure` is `IsLSC₁`.

`IsComputableENNReal` is Gács' Definition 1.5.1 with error `2^{-k}` in place of `1/n`:
a computable sequence of dyadic rationals within `2^{-k}` of the value.

## Proposition 1.5.5, what is and is not formalised

Gács lists four closure facts. Two of them, (a) "`⌈·⌉ : ℝ → ℝ` is lower semicomputable"
and (d) "a monotone lower semicomputable `f : ℝ → ℝ` composed with a lower
semicomputable `g` is lower semicomputable", concern **functions of a real argument**
(his Definitions 1.5.3–1.5.4, via enumerable sets of rational intervals). The
repository has no computability theory for real-input functions and building one is
outside the scope of this chapter, so those two are **not formalised** here.

The discrete-domain content is: (b) computable functions compose
(`IsComputableENNReal.comp_computable`), (c) lower semicomputable functions
pre-compose with computable maps (`IsLSC₁.comp_computable`), and, in the same spirit,
lower semicomputability is closed under sums and maxima (`IsLSC₁.add`, `IsLSC₁.max`),
the facts actually used downstream.

## Proposition 1.6.8

A constructive semimeasure that is a measure is computable. If the approximations
`aₛ` increase to `m` and `∑ₓ m(x) = 1`, then once a finite partial sum of `aₛ` exceeds
`1 − 2^{-k}` the remaining mass, in particular `m(x) − aₛ(x)` for any `x`, is below
`2^{-k}`. Such a stage and finite set exist because the partial sums of `m` approach
`1` and each partial sum of `aₛ` approaches that of `m`; they can be *found* by
searching, since the test is a comparison of integers. The result is a computable
two-sided approximation.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Definitions -/

/-- **Lower semicomputability**, one-argument form: dyadic approximations `approx s x / 2^s`,
nondecreasing in `s`, with supremum `f x`, computable in `(s, x)`. -/
def IsLSC₁ (f : BitString → ℝ≥0∞) : Prop :=
  ∃ approx : ℕ → BitString → ℕ,
    (∀ s x, dyadicValue (approx s x) s ≤ dyadicValue (approx (s + 1) x) (s + 1)) ∧
    (∀ x, ⨆ s, dyadicValue (approx s x) s = f x) ∧
    Computable (fun p : ℕ × BitString ↦ approx p.1 p.2)

/-- The repository's conditional notion, specialised to a constant condition, gives the
one-argument notion. -/
theorem IsLSC.toUnary {m : BitString → ℝ≥0∞} (h : IsLSC (fun x _ ↦ m x)) : IsLSC₁ m := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := h
  refine ⟨fun s x ↦ approx s x [], fun s x ↦ hmono s x [], fun x ↦ hsup x [], ?_⟩
  exact hcomp.comp (Computable.pair Computable.fst
    (Computable.pair Computable.snd (Computable.const [])))

/-- A constructive semimeasure is lower semicomputable in the one-argument sense. -/
theorem IsLowerSemicomputableSemimeasure.isLSC₁ {m : BitString → ℝ≥0∞}
    (h : IsLowerSemicomputableSemimeasure m) : IsLSC₁ m :=
  IsLSC.toUnary h.2

/-- **Computability** of an `ℝ≥0∞`-valued function (Gács Definition 1.5.1): a computable
dyadic rational `(numerator, exponent)` within `2^{-k}` of the value, for each `k`. -/
def IsComputableENNReal (f : BitString → ℝ≥0∞) : Prop :=
  ∃ approx : ℕ → BitString → ℕ × ℕ,
    Computable (fun p : ℕ × BitString ↦ approx p.1 p.2) ∧
    ∀ k x, dyadicValue (approx k x).1 (approx k x).2 ≤ f x + 2⁻¹ ^ k ∧
      f x ≤ dyadicValue (approx k x).1 (approx k x).2 + 2⁻¹ ^ k

/-! ### Proposition 1.5.5, discrete parts -/

/-- **(c)** Pre-composition with a computable map preserves lower semicomputability. -/
theorem IsLSC₁.comp_computable {f : BitString → ℝ≥0∞} (hf : IsLSC₁ f)
    {g : BitString → BitString} (hg : Computable g) : IsLSC₁ (fun x ↦ f (g x)) := by
  obtain ⟨a, hmono, hsup, hcomp⟩ := hf
  exact ⟨fun s x ↦ a s (g x), fun s x ↦ hmono s (g x), fun x ↦ hsup (g x),
    hcomp.comp (Computable.pair Computable.fst (hg.comp Computable.snd))⟩

/-- **(b)** Pre-composition with a computable map preserves computability. -/
theorem IsComputableENNReal.comp_computable {f : BitString → ℝ≥0∞} (hf : IsComputableENNReal f)
    {g : BitString → BitString} (hg : Computable g) : IsComputableENNReal (fun x ↦ f (g x)) := by
  obtain ⟨a, hcomp, hb⟩ := hf
  exact ⟨fun k x ↦ a k (g x),
    hcomp.comp (Computable.pair Computable.fst (hg.comp Computable.snd)), fun k x ↦ hb k (g x)⟩

/-- Dyadic values add. -/
theorem dyadicValue_add (a b s : ℕ) :
    dyadicValue (a + b) s = dyadicValue a s + dyadicValue b s := by
  unfold dyadicValue
  rw [Nat.cast_add, ENNReal.add_div]

/-- Dyadic values respect `max`. -/
theorem dyadicValue_max (a b s : ℕ) :
    dyadicValue (max a b) s = max (dyadicValue a s) (dyadicValue b s) := by
  unfold dyadicValue
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (ENNReal.div_le_div_right (by exact_mod_cast h) _)]
  · rw [max_eq_left h, max_eq_left (ENNReal.div_le_div_right (by exact_mod_cast h) _)]

/-- Lower semicomputability is closed under addition. -/
theorem IsLSC₁.add {f g : BitString → ℝ≥0∞} (hf : IsLSC₁ f) (hg : IsLSC₁ g) :
    IsLSC₁ (fun x ↦ f x + g x) := by
  obtain ⟨a, ha1, ha2, ha3⟩ := hf
  obtain ⟨b, hb1, hb2, hb3⟩ := hg
  refine ⟨fun s x ↦ a s x + b s x, fun s x ↦ ?_, fun x ↦ ?_, ?_⟩
  · rw [dyadicValue_add, dyadicValue_add]
    exact add_le_add (ha1 s x) (hb1 s x)
  · simp only [dyadicValue_add]
    rw [← ha2 x, ← hb2 x]
    exact (ENNReal.iSup_add_iSup_of_monotone (monotone_nat_of_le_succ (fun s ↦ ha1 s x))
      (monotone_nat_of_le_succ (fun s ↦ hb1 s x))).symm
  · exact Primrec.nat_add.to_comp.comp ha3 hb3

/-- Lower semicomputability is closed under `max`. -/
theorem IsLSC₁.max {f g : BitString → ℝ≥0∞} (hf : IsLSC₁ f) (hg : IsLSC₁ g) :
    IsLSC₁ (fun x ↦ Max.max (f x) (g x)) := by
  obtain ⟨a, ha1, ha2, ha3⟩ := hf
  obtain ⟨b, hb1, hb2, hb3⟩ := hg
  refine ⟨fun s x ↦ Max.max (a s x) (b s x), fun s x ↦ ?_, fun x ↦ ?_, ?_⟩
  · rw [dyadicValue_max, dyadicValue_max]
    exact max_le_max (ha1 s x) (hb1 s x)
  · simp only [dyadicValue_max]
    rw [← ha2 x, ← hb2 x]
    exact iSup_sup_eq
  · exact Primrec.nat_max.to_comp.comp ha3 hb3

/-! ### Proposition 1.6.8: preliminaries -/

/-- The order on `ℕ`, as a `Bool`, is primitive recursive (with the standard
`Decidable` instance). -/
theorem natLe_primrec : Primrec (fun p : ℕ × ℕ ↦ decide (p.1 ≤ p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.nat_le : PrimrecRel ((· ≤ ·) : ℕ → ℕ → Prop))
  exact Primrec.of_eq h (fun p ↦ by congr)

/-- Exponentiation on `ℕ` is primitive recursive. -/
theorem natPow_primrec : Primrec₂ (fun a b : ℕ ↦ a ^ b) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

/-- Summing a function over the positions of a duplicate-free list is summing it over
the list's elements. -/
theorem sum_range_getD_eq {M : Type*} [AddCommMonoid M] (l : List BitString) (hl : l.Nodup)
    (g : BitString → M) :
    ∑ i ∈ Finset.range l.length, g (l.getD i []) = ∑ x ∈ l.toFinset, g x := by
  rw [List.sum_toFinset _ hl, ← List.ofFn_getElem_eq_map, Fin.sum_ofFn,
    ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ ↦ by rw [List.getD_eq_getElem])

section Measure

variable (A : ℕ → BitString → ℕ)

/-- The **numerator sum** of the stage-`s` approximations over all strings of length at
most `N`, indexed by position so that it is visibly computable. -/
def sumNum (s N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (boundedPrograms N).length, A s ((boundedPrograms N).getD i [])

/-- The numerator sum is computable in `(s, N)`. -/
theorem sumNum_computable (hA : Computable (fun p : ℕ × BitString ↦ A p.1 p.2)) :
    Computable (fun p : ℕ × ℕ ↦ sumNum A p.1 p.2) := by
  have hg : Computable₂ (fun (p : ℕ × ℕ) (i : ℕ) ↦ A p.1 ((boundedPrograms p.2).getD i [])) := by
    have : Computable (fun q : (ℕ × ℕ) × ℕ ↦ A q.1.1 ((boundedPrograms q.1.2).getD q.2 [])) :=
      hA.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (((Primrec.list_getD ([] : BitString)).comp
          (primrec_boundedPrograms.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to_comp))
    exact this
  exact computable_range_sum _ hg (fun p ↦ (boundedPrograms p.2).length)
    ((Primrec.list_length.comp (primrec_boundedPrograms.comp Primrec.snd)).to_comp)

/-- The dyadic value of the numerator sum is the sum of the dyadic approximations. -/
theorem dyadic_sumNum (s N : ℕ) :
    (sumNum A s N : ℝ≥0∞) / 2 ^ s
      = ∑ x ∈ (boundedPrograms N).toFinset, dyadicValue (A s x) s := by
  unfold sumNum dyadicValue
  rw [sum_range_getD_eq _ (boundedPrograms_nodup N), Nat.cast_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- **The stage test.** For `n = pair s N`: does the stage-`s` mass on strings of length
at most `N` reach `1 − 2^{-k}`? Written as a comparison of integers,
`2^s · 2^k ≤ S · 2^k + 2^s`, which is `1 ≤ S / 2^s + 2^{-k}`. -/
def goodStage (k n : ℕ) : Bool :=
  decide (2 ^ n.unpair.1 * 2 ^ k ≤ sumNum A n.unpair.1 n.unpair.2 * 2 ^ k + 2 ^ n.unpair.1)

/-- The stage test is computable. -/
theorem goodStage_computable (hA : Computable (fun p : ℕ × BitString ↦ A p.1 p.2)) :
    Computable (fun p : ℕ × ℕ ↦ goodStage A p.1 p.2) := by
  have hs : Computable (fun p : ℕ × ℕ ↦ p.2.unpair.1) :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hN : Computable (fun p : ℕ × ℕ ↦ p.2.unpair.2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hpow2s : Computable (fun p : ℕ × ℕ ↦ 2 ^ p.2.unpair.1) :=
    natPow_primrec.to_comp.comp (Computable.const 2) hs
  have hpow2k : Computable (fun p : ℕ × ℕ ↦ 2 ^ p.1) :=
    natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst
  have hsum : Computable (fun p : ℕ × ℕ ↦ sumNum A p.2.unpair.1 p.2.unpair.2) :=
    (sumNum_computable A hA).comp (Computable.pair hs hN)
  have hlhs : Computable (fun p : ℕ × ℕ ↦ 2 ^ p.2.unpair.1 * 2 ^ p.1) :=
    Primrec.nat_mul.to_comp.comp hpow2s hpow2k
  have hrhs : Computable (fun p : ℕ × ℕ ↦
      sumNum A p.2.unpair.1 p.2.unpair.2 * 2 ^ p.1 + 2 ^ p.2.unpair.1) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp hsum hpow2k) hpow2s
  exact (natLe_primrec.to_comp.comp (Computable.pair hlhs hrhs)).of_eq (fun p ↦ rfl)

/-- Powers of two in `ℝ≥0∞` are finite and nonzero. -/
theorem two_pow_ne_zero_ne_top (s : ℕ) :
    ((2 : ℝ≥0∞) ^ s ≠ 0) ∧ ((2 : ℝ≥0∞) ^ s ≠ ⊤) := by
  have e : (2 : ℝ≥0∞) ^ s = ((2 ^ s : ℕ) : ℝ≥0∞) := by push_cast; rfl
  rw [e]
  exact ⟨Nat.cast_ne_zero.mpr (by positivity), ENNReal.natCast_ne_top _⟩

/-- **The stage test, read in `ℝ≥0∞`.** -/
theorem goodStage_iff (k n : ℕ) :
    goodStage A k n = true ↔
      1 ≤ ∑ x ∈ (boundedPrograms n.unpair.2).toFinset,
            dyadicValue (A n.unpair.1 x) n.unpair.1 + 2⁻¹ ^ k := by
  unfold goodStage
  rw [decide_eq_true_eq, ← dyadic_sumNum]
  obtain ⟨h2s, h2s'⟩ := two_pow_ne_zero_ne_top n.unpair.1
  obtain ⟨h2k, h2k'⟩ := two_pow_ne_zero_ne_top k
  have hc0 : (2 : ℝ≥0∞) ^ n.unpair.1 * 2 ^ k ≠ 0 := mul_ne_zero h2s h2k
  have hcT : (2 : ℝ≥0∞) ^ n.unpair.1 * 2 ^ k ≠ ⊤ := ENNReal.mul_ne_top h2s' h2k'
  rw [← ENNReal.mul_le_mul_iff_right hc0 hcT, mul_one]
  have hR : ((sumNum A n.unpair.1 n.unpair.2 : ℝ≥0∞) / 2 ^ n.unpair.1 + 2⁻¹ ^ k)
      * (2 ^ n.unpair.1 * 2 ^ k)
      = ((sumNum A n.unpair.1 n.unpair.2 * 2 ^ k + 2 ^ n.unpair.1 : ℕ) : ℝ≥0∞) := by
    rw [add_mul, ← ENNReal.inv_pow, div_eq_mul_inv]
    have e1 : (sumNum A n.unpair.1 n.unpair.2 : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n.unpair.1)⁻¹
        * (2 ^ n.unpair.1 * 2 ^ k) = (sumNum A n.unpair.1 n.unpair.2 : ℝ≥0∞) * 2 ^ k := by
      rw [mul_assoc, ← mul_assoc ((2 : ℝ≥0∞) ^ n.unpair.1)⁻¹,
        ENNReal.inv_mul_cancel h2s h2s', one_mul]
    have e2 : ((2 : ℝ≥0∞) ^ k)⁻¹ * (2 ^ n.unpair.1 * 2 ^ k) = 2 ^ n.unpair.1 := by
      rw [mul_comm ((2 : ℝ≥0∞) ^ n.unpair.1), ← mul_assoc, ENNReal.inv_mul_cancel h2k h2k',
        one_mul]
    rw [e1, e2]; push_cast; rfl
  have hR2 : (2 : ℝ≥0∞) ^ n.unpair.1 * 2 ^ k
      * ((sumNum A n.unpair.1 n.unpair.2 : ℝ≥0∞) / 2 ^ n.unpair.1 + 2⁻¹ ^ k)
      = ((sumNum A n.unpair.1 n.unpair.2 * 2 ^ k + 2 ^ n.unpair.1 : ℕ) : ℝ≥0∞) := by
    rw [mul_comm]; exact hR
  have hL : (2 : ℝ≥0∞) ^ n.unpair.1 * 2 ^ k = ((2 ^ n.unpair.1 * 2 ^ k : ℕ) : ℝ≥0∞) := by
    push_cast; rfl
  rw [hR2, hL, Nat.cast_le]

variable {A}

/-- **A good stage exists**, for any precision, when the approximations increase to a
function of total mass one. -/
theorem exists_goodStage {m : BitString → ℝ≥0∞}
    (hmono : ∀ s x, dyadicValue (A s x) s ≤ dyadicValue (A (s + 1) x) (s + 1))
    (hsup : ∀ x, ⨆ s, dyadicValue (A s x) s = m x) (hsum : ∑' x, m x = 1) (k : ℕ) :
    ∃ n, goodStage A k n = true := by
  have hpos : (2⁻¹ : ℝ≥0∞) ^ k ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.mpr (by simp))
  have hlt : (1 : ℝ≥0∞) - 2⁻¹ ^ k < ∑' x, m x := by
    rw [hsum]; exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos
  rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at hlt
  obtain ⟨F, hF⟩ := hlt
  -- Every finite set of strings lies among the strings of some bounded length.
  set N := F.sup List.length with hN
  have hFsub : F ⊆ (boundedPrograms N).toFinset := by
    intro x hx
    rw [List.mem_toFinset, mem_boundedPrograms_iff]
    exact Finset.le_sup (f := List.length) hx
  have h1 : (1 : ℝ≥0∞) - 2⁻¹ ^ k < ∑ x ∈ (boundedPrograms N).toFinset, m x :=
    hF.trans_le (Finset.sum_le_sum_of_subset hFsub)
  -- Exchange the finite sum with the supremum over stages.
  have h2 : ∑ x ∈ (boundedPrograms N).toFinset, m x
      = ⨆ s, ∑ x ∈ (boundedPrograms N).toFinset, dyadicValue (A s x) s := by
    rw [← ENNReal.finsetSum_iSup_of_monotone
      (fun x ↦ monotone_nat_of_le_succ (fun s ↦ hmono s x))]
    exact Finset.sum_congr rfl (fun x _ ↦ (hsup x).symm)
  rw [h2, lt_iSup_iff] at h1
  obtain ⟨s, hs⟩ := h1
  refine ⟨Nat.pair s N, ?_⟩
  rw [goodStage_iff, Nat.unpair_pair]
  exact tsub_le_iff_right.mp hs.le

/-- **What a good stage buys.** If the stage-`s` mass on strings of length at most `N`
is within `2^{-k}` of one, then at every `x` the approximation is within `2^{-k}` of
`m x`. -/
theorem bounds_of_goodStage {m : BitString → ℝ≥0∞}
    (hsup : ∀ x, ⨆ s, dyadicValue (A s x) s = m x) (hsum : ∑' x, m x = 1) {s N k : ℕ}
    (hgood : 1 ≤ ∑ x ∈ (boundedPrograms N).toFinset, dyadicValue (A s x) s + 2⁻¹ ^ k)
    (x : BitString) :
    dyadicValue (A s x) s ≤ m x + 2⁻¹ ^ k ∧ m x ≤ dyadicValue (A s x) s + 2⁻¹ ^ k := by
  have hle : ∀ z, dyadicValue (A s z) s ≤ m z := fun z ↦ by
    rw [← hsup z]; exact le_iSup (fun s ↦ dyadicValue (A s z) s) s
  refine ⟨(hle x).trans le_self_add, ?_⟩
  set B := (boundedPrograms N).toFinset with hB
  set T := ∑ z ∈ B.erase x, dyadicValue (A s z) s with hT
  have hsplit : ∑ z ∈ B, dyadicValue (A s z) s ≤ dyadicValue (A s x) s + T := by
    calc ∑ z ∈ B, dyadicValue (A s z) s
        ≤ ∑ z ∈ insert x (B.erase x), dyadicValue (A s z) s := by
          apply Finset.sum_le_sum_of_subset
          intro z hz
          by_cases hzx : z = x
          · simp [hzx]
          · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzx, hz⟩)
      _ = dyadicValue (A s x) s + T := Finset.sum_insert (Finset.notMem_erase x B)
  have hmT : m x + T ≤ 1 := by
    calc m x + T ≤ m x + ∑ z ∈ B.erase x, m z := by
          gcongr
          exact Finset.sum_le_sum (fun z _ ↦ hle z)
      _ = ∑ z ∈ insert x (B.erase x), m z := (Finset.sum_insert (Finset.notMem_erase x B)).symm
      _ ≤ ∑' z, m z := ENNReal.sum_le_tsum _
      _ = 1 := hsum
  have hTne : T ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans hmT)
  have hchain : m x + T ≤ (dyadicValue (A s x) s + 2⁻¹ ^ k) + T := by
    calc m x + T ≤ 1 := hmT
      _ ≤ ∑ z ∈ B, dyadicValue (A s z) s + 2⁻¹ ^ k := hgood
      _ ≤ (dyadicValue (A s x) s + T) + 2⁻¹ ^ k := by gcongr
      _ = (dyadicValue (A s x) s + 2⁻¹ ^ k) + T := by ring
  exact (ENNReal.add_le_add_iff_right hTne).mp hchain

end Measure

/-! ### Proposition 1.6.8 -/

/-- **Gács Proposition 1.6.8.** A lower semicomputable function of total mass one is
computable: search for a stage whose finite partial sum is within `2^{-k}` of one and
report that stage's approximation. -/
theorem isComputable_of_isLSC₁_of_tsum_eq_one (m : BitString → ℝ≥0∞) (hm : IsLSC₁ m)
    (hsum : ∑' x, m x = 1) : IsComputableENNReal m := by
  obtain ⟨A, hmono, hsup, hA⟩ := hm
  have hex : ∀ k, ∃ n, goodStage A k n = true := exists_goodStage hmono hsup hsum
  have hfind : Computable (fun k ↦ Nat.find (hex k)) :=
    Computable.natFind (P := fun k n ↦ goodStage A k n = true)
      ((goodStage_computable A hA).of_eq (fun p ↦ by cases goodStage A p.1 p.2 <;> simp)) hex
  refine ⟨fun k x ↦ (A (Nat.find (hex k)).unpair.1 x, (Nat.find (hex k)).unpair.1), ?_,
    fun k x ↦ ?_⟩
  · have hs : Computable (fun p : ℕ × BitString ↦ (Nat.find (hex p.1)).unpair.1) :=
      (Primrec.fst.comp Primrec.unpair).to_comp.comp (hfind.comp Computable.fst)
    exact Computable.pair (hA.comp (Computable.pair hs Computable.snd)) hs
  · have hg := (goodStage_iff A k (Nat.find (hex k))).mp (Nat.find_spec (hex k))
    exact bounds_of_goodStage hsup hsum hg x

/-- **Proposition 1.6.8 for the repository's constructive semimeasures.** -/
theorem IsLowerSemicomputableSemimeasure.isComputable_of_tsum_eq_one {m : BitString → ℝ≥0∞}
    (hm : IsLowerSemicomputableSemimeasure m) (hsum : ∑' x, m x = 1) :
    IsComputableENNReal m :=
  isComputable_of_isLSC₁_of_tsum_eq_one m hm.isLSC₁ hsum

end Kolmogorov
