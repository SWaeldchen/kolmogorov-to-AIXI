/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinCore
import KolmogorovMathlib.AlgorithmicProbability.Coding
import KolmogorovMathlib.Foundation.RecursivelyEnumerable
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.ModelsToSets2
import KolmogorovMathlib.Chapter1Misc.Levin
import Mathlib.Computability.PartrecCode

/-!
# Lower semicomputable functions on strings

Gács' tests of randomness (Chapter 2) are lower semicomputable functions
`d : S → (−∞, ∞]`. In this project a test is carried multiplicatively as `t = 2^d`, a
function `BitString → ℝ≥0∞`, and lower semicomputability is the repository's dyadic
notion: a computable `ℕ`-valued approximation `approx s x`, read at scale `2^{-s}`,
nondecreasing in the stage `s` and with supremum `t x`. This file introduces the
**unary** version `IsLSC₁` of the repository's conditional `IsLSC` and proves the three
closure facts Chapter 2 needs.

* `isLSC₁_complexityWeight_of_isRE`: if the relation `f x ≤ N` is recursively
  enumerable then `x ↦ 2^{-f x}` is lower semicomputable. Applied to `f = C(· | ·)`
  this is Gács' remark "since `C` is upper semicomputable, `d₀` is lower
  semicomputable" (proof of Theorem 2.1.1). The approximation at stage `s` is
  `2^{-N}` for the least bound `N ≤ s` whose witness halts within fuel `s`.
* `IsLSC₁.mul_natCast_left`: multiplying by a computable natural-valued function
  preserves lower semicomputability (used for the factor `2^{|x|}`).
* `IsLSC₁.dyadic_lt_isRE`: for lower semicomputable `t`, the relation
  "`a / 2^b < t x`" is recursively enumerable. This is the direction of comparison an
  lsc function supports; "`≤`" is not r.e. in general.

Also here: generic fuel-bounded halting for an r.e. witness on any `Primcodable` type,
and three small `IsRE` combinators.
-/

namespace Kolmogorov

open scoped ENNReal
open Nat.Partrec (Code)

/-! ### Unary lower semicomputability -/

/-- **Lower semicomputable function on strings**, dyadic form: a computable `ℕ`-valued
approximation, nondecreasing in the stage when read at scale `2^{-s}`, with supremum
`f x`. -/
def IsLSC₁ (f : BitString → ℝ≥0∞) : Prop :=
  ∃ approx : ℕ → BitString → ℕ,
    (∀ s x, dyadicValue (approx s x) s ≤ dyadicValue (approx (s + 1) x) (s + 1)) ∧
    (∀ x, ⨆ s, dyadicValue (approx s x) s = f x) ∧
    Computable (fun p : ℕ × BitString ↦ approx p.1 p.2)

/-- A conditional lsc function that ignores its condition is unary lsc. -/
theorem IsLSC.toUnary {m : BitString → ℝ≥0∞} (h : IsLSC (fun x _ ↦ m x)) : IsLSC₁ m := by
  obtain ⟨approx, hmono, hsup, hcomp⟩ := h
  exact ⟨fun s x ↦ approx s x [], fun s x ↦ hmono s x [], fun x ↦ hsup x [],
    hcomp.comp (Computable.pair Computable.fst
      (Computable.pair Computable.snd (Computable.const [])))⟩

/-- Extensional rewriting. -/
theorem IsLSC₁.congr {f g : BitString → ℝ≥0∞} (hf : IsLSC₁ f) (e : ∀ x, f x = g x) :
    IsLSC₁ g := by
  obtain ⟨a, h1, h2, h3⟩ := hf
  exact ⟨a, h1, fun x ↦ (h2 x).trans (e x), h3⟩

/-! ### Dyadic arithmetic -/

theorem two_pow_ne_zero' (n : ℕ) : (2 : ℝ≥0∞) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero

theorem two_pow_ne_top' (n : ℕ) : (2 : ℝ≥0∞) ^ n ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top

theorem dyadicValue_zero (s : ℕ) : dyadicValue 0 s = 0 := by simp [dyadicValue]

theorem dyadicValue_mul_left (n a s : ℕ) :
    dyadicValue (n * a) s = (n : ℝ≥0∞) * dyadicValue a s := by
  unfold dyadicValue; push_cast; rw [mul_div_assoc]

/-- `2^{s-N} / 2^s = 2^{-N}` for `N ≤ s`. -/
theorem dyadicValue_two_pow_sub {s N : ℕ} (h : N ≤ s) :
    dyadicValue (2 ^ (s - N)) s = (2 : ℝ≥0∞)⁻¹ ^ N := by
  unfold dyadicValue
  push_cast
  have hs : (2 : ℝ≥0∞) ^ s = 2 ^ (s - N) * 2 ^ N := by rw [← pow_add]; congr 1; omega
  rw [hs, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl (two_pow_ne_zero' _)) (Or.inl (two_pow_ne_top' _)),
    mul_comm ((2 : ℝ≥0∞) ^ (s - N))⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel (two_pow_ne_zero' _) (two_pow_ne_top' _), mul_one, ENNReal.inv_pow]

/-- Comparing two dyadic rationals is a comparison of naturals. -/
theorem dyadicValue_lt_dyadicValue_iff (a b n s : ℕ) :
    dyadicValue a b < dyadicValue n s ↔ a * 2 ^ s < n * 2 ^ b := by
  unfold dyadicValue
  rw [ENNReal.div_lt_iff (Or.inl (two_pow_ne_zero' b)) (Or.inl (two_pow_ne_top' b)),
    div_eq_mul_inv, mul_right_comm, ← div_eq_mul_inv,
    ENNReal.lt_div_iff_mul_lt (Or.inl (two_pow_ne_zero' s)) (Or.inl (two_pow_ne_top' s))]
  exact_mod_cast Iff.rfl

/-- Exponentiation on `ℕ` is primitive recursive. -/
theorem natPow_primrec : Primrec₂ (fun a b : ℕ ↦ a ^ b) := Primrec₂.unpaired'.mp Nat.Primrec.pow

/-! ### Fuel-bounded halting of an r.e. witness, generically -/

section Fuel

variable {α : Type*} [Primcodable α]

/-- Does the code halt on `q` within fuel `k`? -/
def fuelHalts (c : Code) (k : ℕ) (q : α) : Bool := (Code.evaln k c (Encodable.encode q)).isSome

theorem fuelHalts_primrec (c : Code) : Primrec (fun a : ℕ × α ↦ fuelHalts c a.1 a.2) :=
  Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c))
      (Primrec.encode.comp Primrec.snd)))

theorem fuelHalts_mono (c : Code) {k k' : ℕ} (h : k ≤ k') {q : α}
    (hq : fuelHalts c k q = true) : fuelHalts c k' q = true := by
  unfold fuelHalts at hq ⊢
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hq
  have := Nat.Partrec.Code.evaln_mono h (Option.mem_def.mpr hv)
  rw [Option.mem_def.mp this]
  rfl

variable {f : α →. Unit} {c : Code}

theorem fuelHalts_sound
    (hc : c.eval = fun n ↦ (Part.ofOption (Encodable.decode (α := α) n)).bind
      (fun a ↦ Part.map Encodable.encode (f a)))
    {k : ℕ} {q : α} (h : fuelHalts c k q = true) : (f q).Dom := by
  unfold fuelHalts at h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  have hev : v ∈ c.eval (Encodable.encode q) :=
    Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)
  rw [hc, Part.mem_bind_iff] at hev
  obtain ⟨a, ha, hva⟩ := hev
  rw [Part.mem_ofOption, Encodable.encodek] at ha
  have ha' := Option.some_inj.mp (Option.mem_def.mp ha)
  subst ha'
  obtain ⟨b, hb, _⟩ := (Part.mem_map_iff _).mp hva
  exact Part.dom_iff_mem.mpr ⟨b, hb⟩

theorem fuelHalts_complete
    (hc : c.eval = fun n ↦ (Part.ofOption (Encodable.decode (α := α) n)).bind
      (fun a ↦ Part.map Encodable.encode (f a)))
    {q : α} (h : (f q).Dom) : ∃ k, fuelHalts c k q = true := by
  obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp h
  have hmem : Encodable.encode u ∈ c.eval (Encodable.encode q) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨q, by simp [Encodable.encodek], Part.mem_map Encodable.encode hu⟩
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
  refine ⟨k, ?_⟩
  unfold fuelHalts
  rw [Option.mem_def.mp hk]
  rfl

end Fuel

/-! ### Combinators for recursively enumerable relations -/

section RE

variable {α β : Type*} [Primcodable α] [Primcodable β]

theorem IsRE.congr {R R' : α → Prop} (h : IsRE R) (e : ∀ a, R a ↔ R' a) : IsRE R' := by
  obtain ⟨f, hf, hdom⟩ := h
  exact ⟨f, hf, fun a ↦ (hdom a).trans (e a)⟩

theorem IsRE.comp {R : β → Prop} (h : IsRE R) {g : α → β} (hg : Computable g) :
    IsRE (fun a ↦ R (g a)) := by
  obtain ⟨f, hf, hdom⟩ := h
  exact ⟨fun a ↦ f (g a), hf.comp hg, fun a ↦ hdom (g a)⟩

/-- An r.e. relation intersected with a decidable, computable one is r.e. -/
theorem IsRE.inter_decidable {R : α → Prop} (h : IsRE R) (P : α → Prop) [DecidablePred P]
    (hP : Computable (fun a ↦ decide (P a))) : IsRE (fun a ↦ P a ∧ R a) := by
  obtain ⟨f, hf, hdom⟩ := h
  refine ⟨fun a ↦ (Part.ofOption (if P a then some () else none)).bind (fun _ ↦ f a), ?_, ?_⟩
  · refine Partrec.bind (Computable.ofOption ?_) (hf.comp Computable.fst).to₂
    exact (Computable.cond hP (Computable.const (some ())) (Computable.const none)).of_eq
      (fun a ↦ by by_cases hPa : P a <;> simp [hPa])
  · intro a
    rw [Part.bind_dom]
    by_cases hPa : P a
    · simp [hPa, hdom a]
    · simp [hPa]

/-- A projection of a decidable computable relation is r.e. -/
theorem isRE_exists_of_computable {P : α → ℕ → Prop} [∀ a n, Decidable (P a n)]
    (hP : Computable (fun p : α × ℕ ↦ decide (P p.1 p.2))) : IsRE (fun a ↦ ∃ n, P a n) := by
  have hp : Partrec₂ (fun (a : α) (n : ℕ) ↦ (Part.some (decide (P a n)) : Part Bool)) := hP
  refine ⟨fun a ↦ (Nat.rfind (fun n ↦ (Part.some (decide (P a n)) : Part Bool))).map (fun _ ↦ ()),
    (Partrec.rfind hp).map (Computable.const ()).to₂, fun a ↦ ?_⟩
  change (Nat.rfind _).Dom ↔ _
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨n, hn, _⟩
    exact ⟨n, decide_eq_true_iff.mp (Part.mem_some_iff.mp hn).symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, Part.mem_some_iff.mpr (decide_eq_true hn).symm, fun _ ↦ trivial⟩

end RE

/-! ### `2^{-f}` is lsc when `{f ≤ N}` is r.e. -/

section OfRE

/-- Position of the least bound `N ≤ s` whose witness halts within fuel `s`
(`s + 1` if none). -/
def usIdx (c : Code) (s : ℕ) (x : BitString) : ℕ :=
  (List.range (s + 1)).findIdx (fun N ↦ fuelHalts c s (x, N))

/-- The stage-`s` numerator: `2^{s - N}` for that least bound, `0` if none. -/
def usApprox (c : Code) (s : ℕ) (x : BitString) : ℕ :=
  if usIdx c s x ≤ s then 2 ^ (s - usIdx c s x) else 0

theorem usIdx_primrec (c : Code) : Primrec (fun p : ℕ × BitString ↦ usIdx c p.1 p.2) :=
  Primrec.list_findIdx (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
    (((fuelHalts_primrec c).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
      (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd))).to₂)

theorem usApprox_primrec (c : Code) : Primrec (fun p : ℕ × BitString ↦ usApprox c p.1 p.2) :=
  Primrec.ite (Primrec.nat_le.comp (usIdx_primrec c) Primrec.fst)
    (natPow_primrec.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.fst (usIdx_primrec c)))
    (Primrec.const 0)

theorem fuelHalts_usIdx (c : Code) (s : ℕ) (x : BitString) (h : usIdx c s x ≤ s) :
    fuelHalts c s (x, usIdx c s x) = true := by
  have hlt : (List.range (s + 1)).findIdx (fun N ↦ fuelHalts c s (x, N))
      < (List.range (s + 1)).length := by
    rw [List.length_range]; unfold usIdx at h; omega
  have := List.findIdx_getElem (w := hlt)
  simpa [usIdx] using this

theorem fuelHalts_eq_false_of_lt_usIdx (c : Code) (s : ℕ) (x : BitString) {N : ℕ}
    (hN : N ≤ s) (h : N < usIdx c s x) : fuelHalts c s (x, N) = false := by
  have hlen : N < (List.range (s + 1)).length := by rw [List.length_range]; omega
  have := List.not_of_lt_findIdx (p := fun N ↦ fuelHalts c s (x, N)) (xs := List.range (s + 1)) h
  simpa using this

theorem usIdx_le_of_fuelHalts (c : Code) (s : ℕ) (x : BitString) {N : ℕ} (hN : N ≤ s)
    (h : fuelHalts c s (x, N) = true) : usIdx c s x ≤ N := by
  by_contra hlt
  have := fuelHalts_eq_false_of_lt_usIdx c s x hN (not_le.mp hlt)
  simp [h] at this

theorem usIdx_antitone (c : Code) {s : ℕ} (x : BitString) (h : usIdx c s x ≤ s) :
    usIdx c (s + 1) x ≤ usIdx c s x :=
  usIdx_le_of_fuelHalts c (s + 1) x (by omega)
    (fuelHalts_mono c (Nat.le_succ s) (fuelHalts_usIdx c s x h))

theorem dyadicValue_usApprox (c : Code) (s : ℕ) (x : BitString) :
    dyadicValue (usApprox c s x) s
      = if usIdx c s x ≤ s then (2 : ℝ≥0∞)⁻¹ ^ usIdx c s x else 0 := by
  unfold usApprox
  by_cases h : usIdx c s x ≤ s
  · rw [if_pos h, if_pos h]; exact dyadicValue_two_pow_sub h
  · rw [if_neg h, if_neg h]; exact dyadicValue_zero s

theorem usApprox_mono (c : Code) (s : ℕ) (x : BitString) :
    dyadicValue (usApprox c s x) s ≤ dyadicValue (usApprox c (s + 1) x) (s + 1) := by
  rw [dyadicValue_usApprox, dyadicValue_usApprox]
  by_cases h1 : usIdx c s x ≤ s
  · have h2 : usIdx c (s + 1) x ≤ s + 1 := (usIdx_antitone c x h1).trans (h1.trans (Nat.le_succ s))
    rw [if_pos h1, if_pos h2]
    exact pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two) (usIdx_antitone c x h1)
  · rw [if_neg h1]; exact zero_le

theorem iSup_usApprox {F : BitString → ENat} {f : BitString × ℕ →. Unit} {c : Code}
    (hc : c.eval = fun n ↦ (Part.ofOption (Encodable.decode (α := BitString × ℕ) n)).bind
      (fun a ↦ Part.map Encodable.encode (f a)))
    (hdom : ∀ q, (f q).Dom ↔ F q.1 ≤ (q.2 : ENat)) (x : BitString) :
    ⨆ s, dyadicValue (usApprox c s x) s = complexityWeight (F x) := by
  have hsound : ∀ (s N : ℕ), fuelHalts c s (x, N) = true → F x ≤ (N : ENat) :=
    fun s N h ↦ (hdom (x, N)).mp (fuelHalts_sound hc h)
  rcases eq_or_ne (F x) ⊤ with htop | hne
  · -- Nothing ever halts: every approximation is `0`.
    rw [htop, complexityWeight_top]
    refine le_antisymm (iSup_le fun s ↦ ?_) (zero_le)
    rw [dyadicValue_usApprox]
    have hno : ¬ usIdx c s x ≤ s := fun h ↦ by
      have := hsound s _ (fuelHalts_usIdx c s x h)
      rw [htop] at this
      exact absurd this (WithTop.not_top_le_coe _)
    rw [if_neg hno]
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, F x = (k : ENat) := ⟨(F x).toNat, (ENat.coe_toNat hne).symm⟩
    rw [hk, complexityWeight_coe]
    refine le_antisymm (iSup_le fun s ↦ ?_) ?_
    · rw [dyadicValue_usApprox]
      by_cases h : usIdx c s x ≤ s
      · rw [if_pos h]
        have hk' : k ≤ usIdx c s x := by
          have := hsound s _ (fuelHalts_usIdx c s x h)
          rw [hk] at this
          exact_mod_cast this
        exact pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.mpr one_le_two) hk'
      · rw [if_neg h]; exact zero_le
    · -- The witness for `(x, k)` halts at some fuel; from then on the index is `k`.
      obtain ⟨k₀, hk₀⟩ := fuelHalts_complete hc ((hdom (x, k)).mpr (by rw [hk]))
      refine le_iSup_of_le (max k₀ k) ?_
      rw [dyadicValue_usApprox]
      have hhalt : fuelHalts c (max k₀ k) (x, k) = true := fuelHalts_mono c (le_max_left _ _) hk₀
      have hle : usIdx c (max k₀ k) x ≤ k := usIdx_le_of_fuelHalts c _ x (le_max_right _ _) hhalt
      have hge : k ≤ usIdx c (max k₀ k) x := by
        have := hsound _ _ (fuelHalts_usIdx c _ x (hle.trans (le_max_right _ _)))
        rw [hk] at this
        exact_mod_cast this
      rw [if_pos (hle.trans (le_max_right _ _)), le_antisymm hle hge]

/-- **`2^{-f}` is lower semicomputable when `f` is upper semicomputable**, i.e. when
the relation `f x ≤ N` is recursively enumerable. -/
theorem isLSC₁_complexityWeight_of_isRE (F : BitString → ENat)
    (hF : IsRE (fun q : BitString × ℕ ↦ F q.1 ≤ (q.2 : ENat))) :
    IsLSC₁ (fun x ↦ complexityWeight (F x)) := by
  obtain ⟨f, hf, hdom⟩ := hF
  obtain ⟨c, hc⟩ := Code.exists_code.mp hf
  exact ⟨usApprox c, fun s x ↦ usApprox_mono c s x, fun x ↦ iSup_usApprox hc hdom x,
    (usApprox_primrec c).to_comp⟩

end OfRE

/-! ### Two closure properties -/

/-- Multiplying an lsc function by a computable natural-valued function preserves lsc. -/
theorem IsLSC₁.mul_natCast_left {f : BitString → ℝ≥0∞} (hf : IsLSC₁ f) {g : BitString → ℕ}
    (hg : Computable g) : IsLSC₁ (fun x ↦ (g x : ℝ≥0∞) * f x) := by
  obtain ⟨a, h1, h2, h3⟩ := hf
  refine ⟨fun s x ↦ g x * a s x, fun s x ↦ ?_, fun x ↦ ?_, ?_⟩
  · rw [dyadicValue_mul_left, dyadicValue_mul_left]
    gcongr
    exact h1 s x
  · simp only [dyadicValue_mul_left]
    rw [← ENNReal.mul_iSup, h2 x]
  · exact Primrec.nat_mul.to_comp.comp (hg.comp Computable.snd) h3

/-- **Dyadic lower bounds of an lsc function are r.e.**: the relation `a / 2^b < t x` is
recursively enumerable in `(x, a, b)`. -/
theorem IsLSC₁.dyadic_lt_isRE {t : BitString → ℝ≥0∞} (ht : IsLSC₁ t) :
    IsRE (fun q : BitString × (ℕ × ℕ) ↦ dyadicValue q.2.1 q.2.2 < t q.1) := by
  obtain ⟨a, _, h2, h3⟩ := ht
  have hiff : ∀ q : BitString × (ℕ × ℕ),
      (dyadicValue q.2.1 q.2.2 < t q.1) ↔ ∃ s, q.2.1 * 2 ^ s < a s q.1 * 2 ^ q.2.2 := by
    intro q
    rw [← h2 q.1, lt_iSup_iff]
    simp only [dyadicValue_lt_dyadicValue_iff]
  have hL : Computable (fun p : (BitString × (ℕ × ℕ)) × ℕ ↦ p.1.2.1 * 2 ^ p.2) :=
    Primrec.nat_mul.to_comp.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (natPow_primrec.to_comp.comp (Computable.const 2) Computable.snd)
  have hR : Computable (fun p : (BitString × (ℕ × ℕ)) × ℕ ↦ a p.2 p.1.1 * 2 ^ p.1.2.2) :=
    Primrec.nat_mul.to_comp.comp
      (h3.comp (Computable.pair Computable.snd (Computable.fst.comp Computable.fst)))
      (natPow_primrec.to_comp.comp (Computable.const 2)
        (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  have hP : Computable (fun p : (BitString × (ℕ × ℕ)) × ℕ ↦
      decide (p.1.2.1 * 2 ^ p.2 < a p.2 p.1.1 * 2 ^ p.1.2.2)) :=
    (natLt_primrec.to_comp.comp (Computable.pair hL hR)).of_eq (fun p ↦ rfl)
  exact (isRE_exists_of_computable
    (P := fun (q : BitString × (ℕ × ℕ)) (s : ℕ) ↦ q.2.1 * 2 ^ s < a s q.1 * 2 ^ q.2.2) hP).congr
    (fun q ↦ (hiff q).symm)

end Kolmogorov
