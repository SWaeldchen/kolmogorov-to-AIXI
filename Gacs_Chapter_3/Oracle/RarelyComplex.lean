/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Oracle.RarelyComplexPrep
import Gacs_Chapter_3.Oracle.Coding
import Gacs_Chapter_3.Oracle.MachineUniversal

/-!
# Gács Theorem 3.3.1: complexity is rarely complex

Let `f(x) = K(K(x) ∣ x)` and let `χ` be the halting sequence of the (exactly universal) machine
`U`. Then, for an optimal oracle machine `V`,

  `I(χ : x) = K(x) − K(x ∣ χ) ≥ f(x) − 2 K(f(x)) − c`   (`rarely_complex`),

i.e. `K(x ∣ χ) + f(x) ≤ K(x) + 2 K(f(x)) + c`. Gács states `f(x) − 2.4 log f(x) − c`; ours
implies it, since `K(n) ≤ log n + 2 log log n + O(1) ≤ 1.2 log n + O(1)`.

## Proof

Gács: `ν(x) = m(x) 2^{f(x)} f(x)^{-2.4}` is a semimeasure (by Lemma 3.3.2) computable from `Ω`,
so `m(x ∣ Ω) ≳ ν(x)`. We use `ν(x) = m(x) 2^{f(x)} 2^{-2K(f(x))}` instead: by the sharp
Lemma 3.3.2, `ν{f = n} ≲ 2^{-K(n)}`, which is summable by Kraft. We work with `χ` directly, so
no Turing reduction is needed:

* exact universality turns conditional computations into unconditional ones
  (`exists_tag_cond`), so a finite prefix of `χ` decides halting of all programs needed to
  compute `K(x)`, `f(x)` and `K(f(x))`; `kVal`, `fVal` read them off (`kVal_eq`, `fVal_eq`),
  monotonically in the prefix (`readyB_mono`);
* the requests `(x, K(x) + c₀ + 2 K(f(x)) − f(x))`, issued in the order `strEnum` once the
  prefix suffices, form a monotone initial segment of requests (`reqRC`), with Kraft mass at most
  one along `χ` by Lemma 3.3.2;
* the relativized Kraft–Chaitin theorem (`exists_oracleMachine_of_requests`) and optimality of
  `V` finish.
-/

namespace Kolmogorov.Information.Oracle

open scoped ENNReal
open Kolmogorov.Information (Kc Ku KP_eq_Kc Kc_le_Ku Kc_map Ku_xk_xStar xStar_spec)
open Kolmogorov.Information.Halting (IsCodeOf chi bitLen bitLen_eq_size bitLen_primrec
  complexityOfComplexity aprioriMeasure_complexityOfComplexity_le exists_isCodeOf countBelow
  countBelow_primrec pairCode_primrec')
open Kolmogorov.Randomness (Seq seqTake length_seqTake seqTake_prefix
  two_pow_ne_zero' two_pow_ne_top')
open Nat.Partrec (Code)

/-! ### Primitive recursiveness of the readers -/

section PrimrecReaders

variable {α : Type*} [Primcodable α] (c : Code) {σ : α → BitString}
  {w : α → BitString → BitString} {v : α → ℕ}

theorem hitAt_primrec (hσ : Primrec σ) (hw : Primrec₂ w) (hv : Primrec v) {L : α → ℕ}
    (hL : Primrec L) : Primrec (fun a ↦ hitAt c (σ a) (w a) (v a) (L a)) := by
  have hk : Primrec (fun r : α × BitString ↦ knownOut c (σ r.1) (w r.1 r.2)) :=
    (knownOut_primrec c).comp (Primrec.pair (hσ.comp Primrec.fst) hw)
  have hs : Primrec (fun r : α × BitString ↦ (some (some (v r.1)) : Option (Option ℕ))) :=
    Primrec.option_some.comp (Primrec.option_some.comp (hv.comp Primrec.fst))
  have hp : Primrec₂ (fun (a : α) (q : BitString) ↦
      decide (knownOut c (σ a) (w a q) = some (some (v a)))) :=
    (PrimrecPred.decide (Primrec.eq.comp hk hs)).to₂
  exact list_any_primrec (primrec_boundedPrograms.comp hL) hp

theorem allKnown_primrec (hσ : Primrec σ) (hw : Primrec₂ w) {B : α → ℕ} (hB : Primrec B) :
    Primrec (fun a ↦ allKnown c (σ a) (w a) (B a)) := by
  have hk : Primrec (fun r : α × BitString ↦ knownOut c (σ r.1) (w r.1 r.2)) :=
    (knownOut_primrec c).comp (Primrec.pair (hσ.comp Primrec.fst) hw)
  have hp : Primrec₂ (fun (a : α) (q : BitString) ↦ !(knownOut c (σ a) (w a q)).isSome) :=
    (Primrec.not.comp (Primrec.option_isSome.comp hk)).to₂
  exact Primrec.not.comp (list_any_primrec (primrec_boundedPrograms.comp hB) hp)

theorem minHit_primrec (hσ : Primrec σ) (hw : Primrec₂ w) (hv : Primrec v) {B : α → ℕ}
    (hB : Primrec B) : Primrec (fun a ↦ minHit c (σ a) (w a) (v a) (B a)) := by
  have hh := hitAt_primrec c (α := α × ℕ) (σ := fun r ↦ σ r.1) (w := fun r ↦ w r.1)
    (v := fun r ↦ v r.1) (hσ.comp Primrec.fst)
    (hw.comp (Primrec.fst.comp Primrec.fst) Primrec.snd) (hv.comp Primrec.fst) Primrec.snd
  have hb : Primrec₂ (fun (a : α) (L : ℕ) ↦ !hitAt c (σ a) (w a) (v a) L) :=
    (Primrec.not.comp hh).to₂
  exact countBelow_primrec hb (Primrec.succ.comp hB)

end PrimrecReaders

/-! ### The request stream -/

/-- The constants of the construction. -/
structure RCParams where
  /-- A code of `U`. -/
  code : Code
  /-- The tag of the conditional machine. -/
  tag : BitString
  /-- Constant in `K(x) ≤ |x| + 2 log |x| + c`. -/
  cK : ℕ
  /-- Constant in `f(x) ≤ K(x) + 1 + 2 log(K(x) + 1) + c`. -/
  cf : ℕ
  /-- The normalising constant of the request lengths. -/
  c₀ : ℕ

variable (P : RCParams)

/-- Upper bound for `K(x)`. -/
def boundK (x : BitString) : ℕ := x.length + 2 * bitLen x.length + P.cK

/-- Upper bound for `f(x)` given `k = K(x)`. -/
def boundF (k : ℕ) : ℕ := k + 1 + 2 * bitLen (k + 1) + P.cf

/-- Programs for `U(q, x)`, as unconditional programs. -/
def wrapC (x q : BitString) : BitString := P.tag ++ pairCode x q

/-- `K(x)` as read off `σ`. -/
@[irreducible] def kVal (σ x : BitString) : ℕ :=
  minHit P.code σ id (Encodable.encode x) (boundK P x)

/-- `f(x) = K(K(x) ∣ x)` as read off `σ`. -/
@[irreducible] def fVal (σ x : BitString) : ℕ :=
  minHit P.code σ (wrapC P x) (Encodable.encode (natCode (kVal P σ x))) (boundF P (kVal P σ x))

/-- `σ` suffices to read off `K(x)`, `f(x)` and `K(f(x))`. -/
@[irreducible] def readyB (σ x : BitString) : Bool :=
  allKnown P.code σ id (boundK P x) && allKnown P.code σ (wrapC P x) (boundF P (kVal P σ x)) &&
    allKnown P.code σ id (boundK P (natCode (fVal P σ x)))

/-- The requested length `K(x) + c₀ + 2 K(f(x)) − f(x)`. -/
@[irreducible] def lenReq (σ x : BitString) : ℕ :=
  kVal P σ x + P.c₀ + 2 * kVal P σ (natCode (fVal P σ x)) - fVal P σ x

/-- The `n`-th request, issued once `σ` suffices for the first `n + 1` strings. -/
def reqRC (σ : BitString) (n : ℕ) : Option (BitString × ℕ) :=
  if (List.range (n + 1)).any (fun i ↦ !readyB P σ (strEnum i)) then none
  else some (strEnum n, lenReq P σ (strEnum n))

theorem reqRC_eq_some_iff {σ : BitString} {n : ℕ} {r : BitString × ℕ} :
    reqRC P σ n = some r ↔
      (∀ i ≤ n, readyB P σ (strEnum i) = true) ∧ r = (strEnum n, lenReq P σ (strEnum n)) := by
  unfold reqRC
  by_cases h : (List.range (n + 1)).any (fun i ↦ !readyB P σ (strEnum i)) = true
  · rw [if_pos h]
    obtain ⟨i, hi, hni⟩ := List.any_eq_true.mp h
    simp only [reduceCtorEq, false_iff, not_and]
    intro hall
    have := hall i (Nat.lt_succ_iff.mp (List.mem_range.mp hi))
    simp [this] at hni
  · rw [if_neg h]
    have hall : ∀ i ≤ n, readyB P σ (strEnum i) = true := fun i hi ↦ by
      by_contra hne
      exact h (List.any_eq_true.mpr
        ⟨i, List.mem_range.mpr (Nat.lt_succ_of_le hi), by simpa using hne⟩)
    simp only [Option.some.injEq]
    exact ⟨fun h' ↦ ⟨hall, h'.symm⟩, fun h' ↦ h'.2.symm⟩

/-! ### Monotonicity in the oracle prefix -/

theorem knownOut_eq_of_isSome {c : Code} {σ τ p : BitString} (h : σ <+: τ)
    (hs : (knownOut c σ p).isSome) : knownOut c τ p = knownOut c σ p := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  rw [hr, knownOut_mono h hr]

theorem allKnown_mono {c : Code} {σ τ : BitString} {w : BitString → BitString} {B : ℕ}
    (h : σ <+: τ) (ha : allKnown c σ w B = true) :
    allKnown c τ w B = true ∧ ∀ v, minHit c τ w v B = minHit c σ w v B := by
  have hk := allKnown_iff.mp ha
  refine ⟨allKnown_iff.mpr fun q hq ↦ ?_, fun v ↦ ?_⟩
  · rw [knownOut_eq_of_isSome h (hk q hq)]; exact hk q hq
  · exact minHit_congr fun q hq ↦ (knownOut_eq_of_isSome h (hk q hq))

theorem readyB_mono {σ τ x : BitString} (h : σ <+: τ) (hr : readyB P σ x = true) :
    readyB P τ x = true ∧ kVal P τ x = kVal P σ x ∧ fVal P τ x = fVal P σ x ∧
      kVal P τ (natCode (fVal P σ x)) = kVal P σ (natCode (fVal P σ x)) := by
  rw [readyB, Bool.and_eq_true, Bool.and_eq_true] at hr
  obtain ⟨⟨r1, r2⟩, r3⟩ := hr
  obtain ⟨h1, h2⟩ := allKnown_mono h r1
  have hk : kVal P τ x = kVal P σ x := by rw [kVal, kVal]; exact h2 _
  obtain ⟨h3, h4⟩ := allKnown_mono h r2
  have hf : fVal P τ x = fVal P σ x := by unfold fVal; rw [hk]; exact h4 _
  obtain ⟨h5, h6⟩ := allKnown_mono h r3
  have hkf : kVal P τ (natCode (fVal P σ x)) = kVal P σ (natCode (fVal P σ x)) := by
    rw [kVal, kVal]; exact h6 _
  refine ⟨?_, hk, hf, hkf⟩
  rw [readyB, Bool.and_eq_true, Bool.and_eq_true, hk, hf]; exact ⟨⟨h1, h3⟩, h5⟩

theorem reqRC_mono {σ τ : BitString} {n : ℕ} {r : BitString × ℕ} (h : σ <+: τ)
    (hr : reqRC P σ n = some r) : reqRC P τ n = some r := by
  rw [reqRC_eq_some_iff] at hr ⊢
  obtain ⟨hall, rfl⟩ := hr
  refine ⟨fun i hi ↦ (readyB_mono P h (hall i hi)).1, ?_⟩
  obtain ⟨-, hk, hf, hkf⟩ := readyB_mono P h (hall n le_rfl)
  rw [lenReq, lenReq, hk, hf, hkf]

theorem reqRC_init {σ : BitString} {n m : ℕ} (hmn : m ≤ n) (hs : (reqRC P σ n).isSome) :
    (reqRC P σ m).isSome := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨hall, -⟩ := (reqRC_eq_some_iff P).mp hr
  exact Option.isSome_iff_exists.mpr ⟨_, (reqRC_eq_some_iff P).mpr
    ⟨fun i hi ↦ hall i (le_trans hi hmn), rfl⟩⟩

/-! ### Computability -/

theorem boundK_primrec : Primrec (fun x : BitString ↦ boundK P x) := by
  have hl : Primrec (fun x : BitString ↦ x.length) := Primrec.list_length
  have h := Primrec.nat_add.comp (Primrec.nat_add.comp hl
    (Primrec.nat_mul.comp (Primrec.const 2) (bitLen_primrec.comp hl))) (Primrec.const P.cK)
  exact h.of_eq fun _ ↦ rfl

theorem boundF_primrec : Primrec (fun k : ℕ ↦ boundF P k) := by
  have h := Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.succ
    (Primrec.nat_mul.comp (Primrec.const 2) (bitLen_primrec.comp Primrec.succ)))
    (Primrec.const P.cf)
  exact h.of_eq fun _ ↦ rfl

theorem wrapC_primrec :
    Primrec₂ (fun (r : BitString × BitString) (q : BitString) ↦ wrapC P r.2 q) := by
  have h2 : Primrec (fun a : (BitString × BitString) × BitString ↦ a.1.2) :=
    Primrec.snd.comp Primrec.fst
  have h3 : Primrec (fun a : (BitString × BitString) × BitString ↦ a.2) := Primrec.snd
  have h := Primrec.list_append.comp (Primrec.const P.tag) (pairCode_primrec'.comp h2 h3)
  exact h.to₂.of_eq fun _ _ ↦ rfl

theorem kVal_primrec : Primrec (fun r : BitString × BitString ↦ kVal P r.1 r.2) := by
  have hw : Primrec₂ (fun (_ : BitString × BitString) (q : BitString) ↦ q) := Primrec.snd.to₂
  have hv : Primrec (fun r : BitString × BitString ↦ Encodable.encode r.2) :=
    Primrec.encode.comp Primrec.snd
  have hB : Primrec (fun r : BitString × BitString ↦ boundK P r.2) :=
    (boundK_primrec P).comp Primrec.snd
  have h := minHit_primrec P.code (σ := fun r : BitString × BitString ↦ r.1)
    (w := fun _ q ↦ q) (v := fun r ↦ Encodable.encode r.2) Primrec.fst hw hv hB
  exact h.of_eq fun _ ↦ by rw [kVal]; rfl

theorem fVal_primrec : Primrec (fun r : BitString × BitString ↦ fVal P r.1 r.2) := by
  have hk := kVal_primrec P
  have hv : Primrec (fun r : BitString × BitString ↦ Encodable.encode (natCode (kVal P r.1 r.2))) :=
    Primrec.encode.comp (Halting.natCode_primrec'.comp hk)
  have hB : Primrec (fun r : BitString × BitString ↦ boundF P (kVal P r.1 r.2)) :=
    (boundF_primrec P).comp hk
  have h := minHit_primrec P.code (σ := fun r : BitString × BitString ↦ r.1)
    (w := fun r q ↦ wrapC P r.2 q) (v := fun r ↦ Encodable.encode (natCode (kVal P r.1 r.2)))
    Primrec.fst (wrapC_primrec P) hv hB
  exact h.of_eq fun _ ↦ by rw [fVal]

theorem readyB_primrec : Primrec (fun r : BitString × BitString ↦ readyB P r.1 r.2) := by
  have hw : Primrec₂ (fun (_ : BitString × BitString) (q : BitString) ↦ q) := Primrec.snd.to₂
  have hB : Primrec (fun r : BitString × BitString ↦ boundK P r.2) :=
    (boundK_primrec P).comp Primrec.snd
  have hBF : Primrec (fun r : BitString × BitString ↦ boundF P (kVal P r.1 r.2)) :=
    (boundF_primrec P).comp (kVal_primrec P)
  have hBK : Primrec (fun r : BitString × BitString ↦ boundK P (natCode (fVal P r.1 r.2))) :=
    (boundK_primrec P).comp (Halting.natCode_primrec'.comp (fVal_primrec P))
  have h1 := allKnown_primrec P.code (σ := fun r : BitString × BitString ↦ r.1)
    (w := fun _ q ↦ q) Primrec.fst hw hB
  have h2 := allKnown_primrec P.code (σ := fun r : BitString × BitString ↦ r.1)
    (w := fun r q ↦ wrapC P r.2 q) Primrec.fst (wrapC_primrec P) hBF
  have h3 := allKnown_primrec P.code (σ := fun r : BitString × BitString ↦ r.1)
    (w := fun _ q ↦ q) Primrec.fst hw hBK
  have h4 := Primrec.and.comp (Primrec.and.comp h1 h2) h3
  exact h4.of_eq fun _ ↦ by rw [readyB]; rfl

theorem anyNotReady_primrec : Primrec (fun p : BitString × ℕ ↦
    (List.range (p.2 + 1)).any (fun i ↦ !readyB P p.1 (strEnum i))) := by
  have hf : Primrec (fun p : BitString × ℕ ↦ List.range (p.2 + 1)) :=
    Primrec.list_range.comp (Primrec.succ.comp Primrec.snd)
  have hq : Primrec (fun a : (BitString × ℕ) × ℕ ↦ (a.1.1, strEnum a.2)) :=
    Primrec.pair (Primrec.fst.comp Primrec.fst) (strEnum_primrec.comp Primrec.snd)
  have hr : Primrec (fun a : (BitString × ℕ) × ℕ ↦ readyB P a.1.1 (strEnum a.2)) :=
    (readyB_primrec P).comp hq
  have hp : Primrec (fun a : (BitString × ℕ) × ℕ ↦ !readyB P a.1.1 (strEnum a.2)) :=
    Primrec.not.comp hr
  exact list_any_primrec hf hp.to₂

theorem lenReq_primrec : Primrec (fun r : BitString × BitString ↦ lenReq P r.1 r.2) := by
  have hk := kVal_primrec P
  have hf := fVal_primrec P
  have h1 : Primrec (fun r : BitString × BitString ↦ kVal P r.1 r.2 + P.c₀) :=
    Primrec.nat_add.comp hk (Primrec.const P.c₀)
  have h2 : Primrec (fun r : BitString × BitString ↦ 2 * kVal P r.1 (natCode (fVal P r.1 r.2))) :=
    Primrec.nat_mul.comp (Primrec.const 2) (hk.comp (Primrec.pair Primrec.fst
      (Halting.natCode_primrec'.comp hf)))
  have h3 := Primrec.nat_sub.comp (Primrec.nat_add.comp h1 h2) hf
  exact h3.of_eq fun _ ↦ by rw [lenReq]

theorem reqRC_primrec : Primrec (fun p : BitString × ℕ ↦ reqRC P p.1 p.2) := by
  have hx : Primrec (fun p : BitString × ℕ ↦ strEnum p.2) := strEnum_primrec.comp Primrec.snd
  have hl : Primrec (fun p : BitString × ℕ ↦ lenReq P p.1 (strEnum p.2)) :=
    (lenReq_primrec P).comp (Primrec.pair Primrec.fst hx)
  have hval : Primrec (fun p : BitString × ℕ ↦
      (some (strEnum p.2, lenReq P p.1 (strEnum p.2)) : Option (BitString × ℕ))) :=
    Primrec.option_some.comp (Primrec.pair hx hl)
  have h := Primrec.cond (anyNotReady_primrec P)
    (Primrec.const (none : Option (BitString × ℕ))) hval
  refine h.of_eq fun p ↦ ?_
  unfold reqRC
  cases (List.range (p.2 + 1)).any (fun i ↦ !readyB P p.1 (strEnum i)) <;> rfl

end Kolmogorov.Information.Oracle
