/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.UniversalTest
import Mathlib.Algebra.BigOperators.Fin

/-!
# Conservation of randomness under computable maps (Gács Prop 2.2.5, Thm 2.2.2)
# and Proposition 1.6.8

* **Proposition 1.6.8**: a lower semicomputable function with total mass exactly `1` is
  computable (`IsLSC₁.isComputable_of_tsum_eq_one`). Approximating from below until the
  total lower mass exceeds `1 − 2^{-k}` bounds the error at every point at once: the
  normalisation supplies the missing modulus of convergence.
* **Proposition 2.2.5**: the pushforward `f_*P` of a computable measure along a
  computable map is a computable measure (`pushforward`). Its mass is lower
  semicomputable as a growing finite sum of lower approximations, and it has total
  mass `1`, so Proposition 1.6.8 applies.
* **Theorem 2.2.2**: `d_{f_*P}(f(x)) ≤⁺ d_P(x)`. In Gács' proof the left side, as a
  function of `x`, is itself an integrable test for `P` (its expectation telescopes to
  `∑ 2^{-K} ≤ 1`), so universality of `t_P` gives the bound. No pointwise comparison of
  numerators is needed, and none holds.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### Finite sums over the strings of bounded length -/

/-- Indexed sum over `boundedPrograms N` at stage `s` of a dyadic approximation. -/
def boundedSum (g : ℕ → BitString → ℕ) (s N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (boundedPrograms N).length, g s ((boundedPrograms N).getD i [])

theorem boundedSum_computable {g : ℕ → BitString → ℕ}
    (hg : Computable (fun p : ℕ × BitString ↦ g p.1 p.2)) :
    Computable (fun p : ℕ × ℕ ↦ boundedSum g p.1 p.2) := by
  have h2 : Computable₂ (fun (p : ℕ × ℕ) (i : ℕ) ↦ g p.1 ((boundedPrograms p.2).getD i [])) := by
    have : Computable (fun q : (ℕ × ℕ) × ℕ ↦ g q.1.1 ((boundedPrograms q.1.2).getD q.2 [])) :=
      (hg.comp (Computable.pair (Computable.fst.comp Computable.fst)
        (((Primrec.list_getD ([] : BitString)).comp
          (primrec_boundedPrograms.comp (Primrec.snd.comp Primrec.fst))
          Primrec.snd).to_comp))).of_eq (fun _ ↦ rfl)
    exact this
  exact (computable_range_sum _ h2 (fun p ↦ (boundedPrograms p.2).length)
    ((Primrec.list_length.comp (primrec_boundedPrograms.comp Primrec.snd)).to_comp)).of_eq
    (fun _ ↦ rfl)

/-- An indexed sum over a duplicate-free list is the sum over its finset. -/
theorem sum_range_getD_eq {M : Type*} [AddCommMonoid M] (l : List BitString) (hl : l.Nodup)
    (h : BitString → M) :
    ∑ i ∈ Finset.range l.length, h (l.getD i []) = ∑ x ∈ l.toFinset, h x := by
  rw [List.sum_toFinset _ hl, ← List.ofFn_getElem_eq_map, List.sum_ofFn,
    ← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl (fun i _ ↦ by rw [List.getD_eq_getElem])

theorem dyadic_boundedSum (g : ℕ → BitString → ℕ) (s N : ℕ) :
    (boundedSum g s N : ℝ≥0∞) / 2 ^ s
      = ∑ x ∈ (boundedPrograms N).toFinset, dyadicValue (g s x) s := by
  unfold boundedSum dyadicValue
  rw [sum_range_getD_eq _ (boundedPrograms_nodup N), Nat.cast_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- Every finite set of strings lies in some `boundedPrograms N`. -/
theorem subset_boundedPrograms (F : Finset BitString) :
    F ⊆ (boundedPrograms (F.sup List.length)).toFinset := by
  intro x hx
  rw [List.mem_toFinset, mem_boundedPrograms_iff]
  exact Finset.le_sup (f := List.length) hx

/-! ### Proposition 1.6.8 -/

section Normalized

variable (a : ℕ → BitString → ℕ)

/-- The search predicate: at stage `s`, the strings of length `≤ N` already carry lower
mass at least `1 − 2^{-k}`, i.e. `2^s 2^k ≤ S 2^k + 2^s` with `S` the numerator sum. -/
def goodStage (k n : ℕ) : Bool :=
  decide (2 ^ n.unpair.1 * 2 ^ k
    ≤ boundedSum a n.unpair.1 n.unpair.2 * 2 ^ k + 2 ^ n.unpair.1)

theorem natLe_primrec : Primrec (fun p : ℕ × ℕ ↦ decide (p.1 ≤ p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.nat_le : PrimrecRel ((· ≤ ·) : ℕ → ℕ → Prop))
  exact Primrec.of_eq h (fun p ↦ by congr)

theorem goodStage_computable (ha : Computable (fun p : ℕ × BitString ↦ a p.1 p.2)) :
    Computable (fun p : ℕ × ℕ ↦ goodStage a p.1 p.2) := by
  have hs : Computable (fun p : ℕ × ℕ ↦ p.2.unpair.1) :=
    (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hN : Computable (fun p : ℕ × ℕ ↦ p.2.unpair.2) :=
    (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)).to_comp
  have hpow2s : Computable (fun p : ℕ × ℕ ↦ 2 ^ p.2.unpair.1) :=
    natPow_primrec.to_comp.comp (Computable.const 2) hs
  have hpow2k : Computable (fun p : ℕ × ℕ ↦ 2 ^ p.1) :=
    natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst
  have hsum : Computable (fun p : ℕ × ℕ ↦ boundedSum a p.2.unpair.1 p.2.unpair.2) :=
    (boundedSum_computable ha).comp (Computable.pair hs hN)
  have hlhs : Computable (fun p : ℕ × ℕ ↦ 2 ^ p.2.unpair.1 * 2 ^ p.1) :=
    Primrec.nat_mul.to_comp.comp hpow2s hpow2k
  have hrhs : Computable (fun p : ℕ × ℕ ↦
      boundedSum a p.2.unpair.1 p.2.unpair.2 * 2 ^ p.1 + 2 ^ p.2.unpair.1) :=
    Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp hsum hpow2k) hpow2s
  exact (natLe_primrec.to_comp.comp (Computable.pair hlhs hrhs)).of_eq (fun _ ↦ rfl)

/-- The search predicate, read in `ℝ≥0∞`. -/
theorem goodStage_iff (k n : ℕ) :
    goodStage a k n = true ↔
      1 ≤ ∑ x ∈ (boundedPrograms n.unpair.2).toFinset, dyadicValue (a n.unpair.1 x) n.unpair.1
        + 2⁻¹ ^ k := by
  unfold goodStage
  rw [decide_eq_true_eq, ← dyadic_boundedSum]
  set s := n.unpair.1
  set N := n.unpair.2
  set S := boundedSum a s N
  have hL : (1 : ℝ≥0∞) * (2 ^ s * 2 ^ k) = ((2 ^ s * 2 ^ k : ℕ) : ℝ≥0∞) := by push_cast; ring
  have hR : ((S : ℝ≥0∞) / 2 ^ s + 2⁻¹ ^ k) * (2 ^ s * 2 ^ k)
      = ((S * 2 ^ k + 2 ^ s : ℕ) : ℝ≥0∞) := by
    rw [add_mul, ← ENNReal.inv_pow, div_eq_mul_inv]
    have e1 : (S : ℝ≥0∞) * (2 ^ s)⁻¹ * (2 ^ s * 2 ^ k) = S * 2 ^ k := by
      rw [mul_assoc, ← mul_assoc ((2 : ℝ≥0∞) ^ s)⁻¹,
        ENNReal.inv_mul_cancel (two_pow_ne_zero' s) (two_pow_ne_top' s), one_mul]
    have e2 : ((2 : ℝ≥0∞) ^ k)⁻¹ * (2 ^ s * 2 ^ k) = 2 ^ s := by
      rw [mul_comm ((2 : ℝ≥0∞) ^ s), ← mul_assoc,
        ENNReal.inv_mul_cancel (two_pow_ne_zero' k) (two_pow_ne_top' k), one_mul]
    rw [e1, e2]; push_cast; rfl
  have hmul : (2 : ℝ≥0∞) ^ s * 2 ^ k = 2 ^ (s + k) * 2⁻¹ ^ 0 := by rw [pow_zero, mul_one, pow_add]
  constructor
  · intro h
    have h' : (1 : ℝ≥0∞) * (2 ^ s * 2 ^ k) ≤ ((S : ℝ≥0∞) / 2 ^ s + 2⁻¹ ^ k) * (2 ^ s * 2 ^ k) := by
      rw [hL, hR]; exact_mod_cast h
    rw [hmul] at h'
    exact le_of_mul_two_pow_mul_inv_two_pow_le h'
  · intro h
    have h' := mul_le_mul' h (le_refl ((2 : ℝ≥0∞) ^ s * 2 ^ k))
    rw [hL, hR, Nat.cast_le] at h'
    exact h'

/-- **A good stage exists**, when the total mass is `1`. -/
theorem exists_goodStage {m : BitString → ℝ≥0∞}
    (hmono : ∀ s x, dyadicValue (a s x) s ≤ dyadicValue (a (s + 1) x) (s + 1))
    (hsup : ∀ x, ⨆ s, dyadicValue (a s x) s = m x) (hsum : ∑' x, m x = 1) (k : ℕ) :
    ∃ n, goodStage a k n = true := by
  have hpos : (2 : ℝ≥0∞)⁻¹ ^ k ≠ 0 := pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
  have hlt : (1 : ℝ≥0∞) - 2⁻¹ ^ k < ∑' x, m x := by
    rw [hsum]; exact ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero hpos
  rw [ENNReal.tsum_eq_iSup_sum, lt_iSup_iff] at hlt
  obtain ⟨F, hF⟩ := hlt
  set N := F.sup List.length with hN
  have h1 : (1 : ℝ≥0∞) - 2⁻¹ ^ k < ∑ x ∈ (boundedPrograms N).toFinset, m x :=
    hF.trans_le (Finset.sum_le_sum_of_subset (subset_boundedPrograms F))
  have h2 : ∑ x ∈ (boundedPrograms N).toFinset, m x
      = ⨆ s, ∑ x ∈ (boundedPrograms N).toFinset, dyadicValue (a s x) s := by
    rw [← ENNReal.finsetSum_iSup_of_monotone (fun x ↦ monotone_nat_of_le_succ (fun s ↦ hmono s x))]
    exact Finset.sum_congr rfl (fun x _ ↦ (hsup x).symm)
  rw [h2, lt_iSup_iff] at h1
  obtain ⟨s, hs⟩ := h1
  refine ⟨Nat.pair s N, ?_⟩
  rw [goodStage_iff, Nat.unpair_pair]
  exact tsub_le_iff_right.mp hs.le

/-- **The error bound at a good stage.** -/
theorem le_dyadic_add_of_good {m : BitString → ℝ≥0∞}
    (hsup : ∀ x, ⨆ s, dyadicValue (a s x) s = m x) (hsum : ∑' x, m x = 1) {s N k : ℕ}
    (hgood : 1 ≤ ∑ x ∈ (boundedPrograms N).toFinset, dyadicValue (a s x) s + 2⁻¹ ^ k)
    (x : BitString) : m x ≤ dyadicValue (a s x) s + 2⁻¹ ^ k := by
  have hle : ∀ z, dyadicValue (a s z) s ≤ m z := fun z ↦ by
    rw [← hsup z]; exact le_iSup (fun s ↦ dyadicValue (a s z) s) s
  set B := (boundedPrograms N).toFinset
  set T := ∑ z ∈ B.erase x, dyadicValue (a s z) s
  have hsub : B ⊆ insert x (B.erase x) := by
    intro z hz
    by_cases hzx : z = x
    · simp [hzx]
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hzx, hz⟩)
  have hsplit : ∑ z ∈ B, dyadicValue (a s z) s ≤ dyadicValue (a s x) s + T := by
    calc ∑ z ∈ B, dyadicValue (a s z) s ≤ ∑ z ∈ insert x (B.erase x), dyadicValue (a s z) s :=
          Finset.sum_le_sum_of_subset hsub
      _ = dyadicValue (a s x) s + T := Finset.sum_insert (Finset.notMem_erase x B)
  have hmT : m x + T ≤ 1 := by
    calc m x + T ≤ m x + ∑ z ∈ B.erase x, m z := by
          gcongr; exact Finset.sum_le_sum (fun z _ ↦ hle z)
      _ = ∑ z ∈ insert x (B.erase x), m z := (Finset.sum_insert (Finset.notMem_erase x B)).symm
      _ ≤ ∑' z, m z := ENNReal.sum_le_tsum _
      _ = 1 := hsum
  have hTne : T ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (le_add_self.trans hmT)
  have h : m x + T ≤ (dyadicValue (a s x) s + 2⁻¹ ^ k) + T := by
    calc m x + T ≤ 1 := hmT
      _ ≤ ∑ z ∈ B, dyadicValue (a s z) s + 2⁻¹ ^ k := hgood
      _ ≤ (dyadicValue (a s x) s + T) + 2⁻¹ ^ k := by gcongr
      _ = (dyadicValue (a s x) s + 2⁻¹ ^ k) + T := by ring
  exact (ENNReal.add_le_add_iff_right hTne).mp h

end Normalized

/-- **Gács Proposition 1.6.8.** A lower semicomputable function with total mass `1` is
computable. -/
theorem IsLSC₁.isComputable_of_tsum_eq_one {m : BitString → ℝ≥0∞} (hm : IsLSC₁ m)
    (hsum : ∑' x, m x = 1) : IsComputableENNReal m := by
  obtain ⟨a, hmono, hsup, ha⟩ := hm
  have hex : ∀ k, ∃ n, goodStage a k n = true := exists_goodStage a hmono hsup hsum
  have hfind : Computable (fun k ↦ Nat.find (hex k)) :=
    Computable.natFind (P := fun k n ↦ goodStage a k n = true)
      ((goodStage_computable a ha).of_eq (fun p ↦ by cases goodStage a p.1 p.2 <;> simp)) hex
  -- The stage found at precision `k`.
  set st : ℕ → ℕ := fun k ↦ (Nat.find (hex k)).unpair.1 with hst
  have hstc : Computable st := (Primrec.fst.comp Primrec.unpair).to_comp.comp hfind
  have hgood : ∀ k, 1 ≤ ∑ x ∈ (boundedPrograms (Nat.find (hex k)).unpair.2).toFinset,
      dyadicValue (a (st k) x) (st k) + 2⁻¹ ^ k := fun k ↦
    (goodStage_iff a k (Nat.find (hex k))).mp (Nat.find_spec (hex k))
  -- Lower approximation `a_{st k} x / 2^{st k}`; upper approximation that plus `2^{-k}`.
  refine ⟨fun k x ↦ (a (st k) x, 2 ^ st k),
    fun k x ↦ (a (st k) x * 2 ^ k + 2 ^ st k, 2 ^ st k * 2 ^ k),
    fun k x ↦ ⟨by positivity, by positivity⟩,
    ?_, ?_, fun k x ↦ ?_⟩
  · exact Computable.pair (ha.comp (Computable.pair (hstc.comp Computable.fst) Computable.snd))
      (natPow_primrec.to_comp.comp (Computable.const 2) (hstc.comp Computable.fst))
  · exact Computable.pair
      (Primrec.nat_add.to_comp.comp
        (Primrec.nat_mul.to_comp.comp
          (ha.comp (Computable.pair (hstc.comp Computable.fst) Computable.snd))
          (natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst))
        (natPow_primrec.to_comp.comp (Computable.const 2) (hstc.comp Computable.fst)))
      (Primrec.nat_mul.to_comp.comp
        (natPow_primrec.to_comp.comp (Computable.const 2) (hstc.comp Computable.fst))
        (natPow_primrec.to_comp.comp (Computable.const 2) Computable.fst))
  · have hlo : ratVal (a (st k) x, 2 ^ st k) = dyadicValue (a (st k) x) (st k) := by
      unfold ratVal dyadicValue; push_cast; rfl
    have hhi : ratVal (a (st k) x * 2 ^ k + 2 ^ st k, 2 ^ st k * 2 ^ k)
        = dyadicValue (a (st k) x) (st k) + 2⁻¹ ^ k := by
      unfold ratVal dyadicValue
      push_cast
      rw [← ENNReal.div_add_div_same,
        ENNReal.mul_div_mul_right _ _ (two_pow_ne_zero' k) (two_pow_ne_top' k)]
      congr 1
      rw [ENNReal.div_eq_inv_mul,
        ENNReal.mul_inv (Or.inl (two_pow_ne_zero' _)) (Or.inl (two_pow_ne_top' _)),
        mul_comm ((2 : ℝ≥0∞) ^ st k)⁻¹, mul_assoc,
        ENNReal.inv_mul_cancel (two_pow_ne_zero' _) (two_pow_ne_top' _), mul_one, ENNReal.inv_pow]
    rw [hlo, hhi]
    refine ⟨?_, le_dyadic_add_of_good a hsup hsum (hgood k) x, le_rfl⟩
    rw [← hsup x]; exact le_iSup (fun s ↦ dyadicValue (a s x) s) (st k)

/-! ### Pushforward of a computable measure -/

/-- Composing an lsc function with a computable map. -/
theorem IsLSC₁.comp_computable {f : BitString → ℝ≥0∞} (hf : IsLSC₁ f) {g : BitString → BitString}
    (hg : Computable g) : IsLSC₁ (fun x ↦ f (g x)) := by
  obtain ⟨a, h1, h2, h3⟩ := hf
  exact ⟨fun s x ↦ a s (g x), fun s x ↦ h1 s (g x), fun x ↦ h2 (g x),
    h3.comp (Computable.pair Computable.fst (hg.comp Computable.snd))⟩

/-- The mass of the pushforward: `f_*P(x) = ∑_{f y = x} P(y)`. -/
noncomputable def pushMass (f : BitString → BitString) (P : ComputableMeasure) (x : BitString) :
    ℝ≥0∞ :=
  ∑' y, if f y = x then P.mass y else 0

theorem tsum_pushMass (f : BitString → BitString) (P : ComputableMeasure) :
    ∑' x, pushMass f P x = 1 := by
  unfold pushMass
  rw [ENNReal.tsum_comm]
  calc ∑' y, ∑' x, (if f y = x then P.mass y else 0) = ∑' y, P.mass y := by
        refine tsum_congr (fun y ↦ ?_)
        rw [tsum_eq_single (f y) (fun x hx ↦ if_neg (Ne.symm hx)), if_pos rfl]
    _ = 1 := P.tsum_eq

/-- `P(x) ≤ f_*P(f x)`. -/
theorem mass_le_pushMass (f : BitString → BitString) (P : ComputableMeasure) (x : BitString) :
    P.mass x ≤ pushMass f P (f x) := by
  unfold pushMass
  have := ENNReal.le_tsum (f := fun y ↦ if f y = f x then P.mass y else 0) x
  simpa using this

/-- The stage-`s` lower approximation of the pushforward mass. -/
def pushApprox (a : ℕ → BitString → ℕ) (f : BitString → BitString) (s : ℕ) (x : BitString) : ℕ :=
  ∑ i ∈ Finset.range (boundedPrograms s).length,
    if f ((boundedPrograms s).getD i []) = x then a s ((boundedPrograms s).getD i []) else 0

theorem pushApprox_computable {a : ℕ → BitString → ℕ}
    (ha : Computable (fun p : ℕ × BitString ↦ a p.1 p.2)) {f : BitString → BitString}
    (hf : Computable f) : Computable (fun p : ℕ × BitString ↦ pushApprox a f p.1 p.2) := by
  have hget : Computable (fun q : (ℕ × BitString) × ℕ ↦ (boundedPrograms q.1.1).getD q.2 []) :=
    ((Primrec.list_getD ([] : BitString)).comp
      (primrec_boundedPrograms.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to_comp
  have htest : Computable (fun q : (ℕ × BitString) × ℕ ↦
      decide (f ((boundedPrograms q.1.1).getD q.2 []) = q.1.2)) :=
    (bitStringEq_primrec.to_comp.comp (Computable.pair (hf.comp hget)
      (Computable.snd.comp Computable.fst))).of_eq (fun _ ↦ rfl)
  have hval : Computable (fun q : (ℕ × BitString) × ℕ ↦
      a q.1.1 ((boundedPrograms q.1.1).getD q.2 [])) :=
    ha.comp (Computable.pair (Computable.fst.comp Computable.fst) hget)
  have h2 : Computable₂ (fun (p : ℕ × BitString) (i : ℕ) ↦
      if f ((boundedPrograms p.1).getD i []) = p.2 then a p.1 ((boundedPrograms p.1).getD i [])
      else 0) := by
    have : Computable (fun q : (ℕ × BitString) × ℕ ↦
        if f ((boundedPrograms q.1.1).getD q.2 []) = q.1.2
          then a q.1.1 ((boundedPrograms q.1.1).getD q.2 []) else 0) :=
      (Computable.cond htest hval (Computable.const 0)).of_eq (fun q ↦ Bool.cond_decide _ _ _)
    exact this
  exact (computable_range_sum _ h2 (fun p ↦ (boundedPrograms p.1).length)
    ((Primrec.list_length.comp (primrec_boundedPrograms.comp Primrec.fst)).to_comp)).of_eq
    (fun _ ↦ rfl)

theorem dyadic_pushApprox (a : ℕ → BitString → ℕ) (f : BitString → BitString) (s : ℕ)
    (x : BitString) :
    dyadicValue (pushApprox a f s x) s
      = ∑ y ∈ (boundedPrograms s).toFinset, if f y = x then dyadicValue (a s y) s else 0 := by
  unfold dyadicValue pushApprox
  rw [sum_range_getD_eq _ (boundedPrograms_nodup s)
    (fun y ↦ if f y = x then a s y else 0), Nat.cast_sum]
  simp only [div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ ↦ ?_)
  split_ifs <;> simp

/-- **The pushforward mass is lower semicomputable.** -/
theorem pushMass_isLSC₁ (f : BitString → BitString) (hf : Computable f) (P : ComputableMeasure) :
    IsLSC₁ (pushMass f P) := by
  obtain ⟨a, hmono, hsup, ha⟩ := P.computable.isLSC₁
  have hle : ∀ s y, dyadicValue (a s y) s ≤ P.mass y := fun s y ↦ by
    rw [← hsup y]; exact le_iSup (fun s ↦ dyadicValue (a s y) s) s
  -- The summand, as a function of the stage, is monotone for each `y`.
  refine ⟨pushApprox a f, fun s x ↦ ?_, fun x ↦ ?_, pushApprox_computable ha hf⟩
  · rw [dyadic_pushApprox, dyadic_pushApprox]
    calc ∑ y ∈ (boundedPrograms s).toFinset, (if f y = x then dyadicValue (a s y) s else 0)
        ≤ ∑ y ∈ (boundedPrograms s).toFinset,
            (if f y = x then dyadicValue (a (s + 1) y) (s + 1) else 0) :=
          Finset.sum_le_sum (fun y _ ↦ by split_ifs <;> simp [hmono s y])
      _ ≤ _ := Finset.sum_le_sum_of_subset (fun y hy ↦ by
          rw [List.mem_toFinset, mem_boundedPrograms_iff] at hy ⊢; omega)
  · simp only [dyadic_pushApprox]
    unfold pushMass
    apply le_antisymm
    · refine iSup_le fun s ↦ ?_
      calc ∑ y ∈ (boundedPrograms s).toFinset, (if f y = x then dyadicValue (a s y) s else 0)
          ≤ ∑ y ∈ (boundedPrograms s).toFinset, (if f y = x then P.mass y else 0) :=
            Finset.sum_le_sum (fun y _ ↦ by split_ifs <;> simp [hle s y])
        _ ≤ ∑' y, (if f y = x then P.mass y else 0) := ENNReal.sum_le_tsum _
    · rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun F ↦ ?_
      set N := F.sup List.length with hN
      have hFsub := subset_boundedPrograms F
      -- For each `y` the summand is the sup of a monotone sequence.
      have hmonoY : ∀ y, Monotone (fun s ↦ if f y = x then dyadicValue (a s y) s else 0) := by
        intro y
        refine monotone_nat_of_le_succ (fun s ↦ ?_)
        split_ifs <;> simp [hmono s y]
      have hsupY : ∀ y, (⨆ s, if f y = x then dyadicValue (a s y) s else 0)
          = if f y = x then P.mass y else 0 := by
        intro y
        split_ifs
        · exact hsup y
        · exact iSup_const
      calc ∑ y ∈ F, (if f y = x then P.mass y else 0)
          ≤ ∑ y ∈ (boundedPrograms N).toFinset, (if f y = x then P.mass y else 0) :=
            Finset.sum_le_sum_of_subset hFsub
        _ = ⨆ s, ∑ y ∈ (boundedPrograms N).toFinset,
              (if f y = x then dyadicValue (a s y) s else 0) := by
            rw [← ENNReal.finsetSum_iSup_of_monotone hmonoY]
            exact Finset.sum_congr rfl (fun y _ ↦ (hsupY y).symm)
        _ ≤ ⨆ s, ∑ y ∈ (boundedPrograms s).toFinset,
              (if f y = x then dyadicValue (a s y) s else 0) := by
            refine iSup_le fun s ↦ le_iSup_of_le (max s N) ?_
            calc ∑ y ∈ (boundedPrograms N).toFinset, (if f y = x then dyadicValue (a s y) s else 0)
                ≤ ∑ y ∈ (boundedPrograms N).toFinset,
                    (if f y = x then dyadicValue (a (max s N) y) (max s N) else 0) :=
                  Finset.sum_le_sum (fun y _ ↦ hmonoY y (le_max_left s N))
              _ ≤ _ := Finset.sum_le_sum_of_subset (fun y hy ↦ by
                  rw [List.mem_toFinset, mem_boundedPrograms_iff] at hy ⊢
                  exact hy.trans (le_max_right s N))

/-- **Gács Proposition 2.2.5.** The pushforward of a computable measure along a computable
map is a computable measure. -/
noncomputable def pushforward (f : BitString → BitString) (hf : Computable f)
    (P : ComputableMeasure) : ComputableMeasure where
  mass := pushMass f P
  tsum_eq := tsum_pushMass f P
  computable := (pushMass_isLSC₁ f hf P).isComputable_of_tsum_eq_one (tsum_pushMass f P)

/-! ### Theorem 2.2.2 -/

/-- The composite `x ↦ t_{f_*P}(f x)` is an integrable test for `P`: its expectation
telescopes to `∑_y 2^{-K(y)} ≤ 1`. -/
theorem canonical_pushforward_comp_isIntegrableTest (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) (P : ComputableMeasure) :
    IsIntegrableTest P (fun x ↦ canonicalIntegrableTest U (pushforward f hf P) (f x)) := by
  refine ⟨(canonicalIntegrableTest_isIntegrableTest U hU (pushforward f hf P)).1.comp_computable hf,
    ?_⟩
  -- Regroup the expectation by the value of `f`.
  have hregroup : ∑' x, P.mass x * canonicalIntegrableTest U (pushforward f hf P) (f x)
      = ∑' y, pushMass f P y * canonicalIntegrableTest U (pushforward f hf P) y := by
    unfold pushMass
    simp_rw [← ENNReal.tsum_mul_right]
    rw [ENNReal.tsum_comm]
    refine tsum_congr (fun x ↦ ?_)
    rw [tsum_eq_single (f x) (fun y hy ↦ by rw [if_neg (Ne.symm hy), zero_mul]), if_pos rfl]
  rw [hregroup]
  calc ∑' y, pushMass f P y * canonicalIntegrableTest U (pushforward f hf P) y
      ≤ ∑' y, prefixComplexityWeight U y :=
        ENNReal.tsum_le_tsum (fun y ↦ ENNReal.mul_div_le)
    _ ≤ 1 := KP_kraft_sum_le_one U hU.isPrefixDecompressor []

/-- **Gács Theorem 2.2.2.** `d_{f_*P}(f(x)) ≤⁺ d_P(x)`: applying a computable map cannot
increase the deficiency of randomness by more than a constant. -/
theorem canonical_pushforward_le (U : Map) (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString) (hf : Computable f) (P : ComputableMeasure) :
    ∃ c : ℕ, ∀ x, canonicalIntegrableTest U (pushforward f hf P) (f x)
      ≤ 2 ^ c * canonicalIntegrableTest U P x :=
  integrableTest_le_canonical U hU P (canonical_pushforward_comp_isIntegrableTest U hU f hf P)

end Kolmogorov
