/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.AlgorithmicStatistics.NonStochastic
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting
import KolmogorovMathlib.AlgorithmicProbability.PairProjection
import KolmogorovMathlib.Prefix.Properties

/-!
# The search machine behind Gács Theorem 3.1.5

Gács' proof of Theorem 3.1.5 (§3.3.1) runs a program that, given a few numbers, finds a
string `x` of length `n` with `K(x) ≥ m`. This file builds that program and proves it
correct; the counting argument is in `SometimesComplex.lean`.

Fix `n` and `s`. A program `p` with `|p| ≤ s` is **suitable** for `x` (`Suit`) when
`U(p, x)` outputs a string `y` with `K(x) ≤ |y| − 1`, i.e. `p` names (in unary-like length
form) an upper bound on `K(x)` that is witnessed by a program of `x`. Gács asks for a program
of length exactly `k`; "at most `k`" is equivalent for the argument and simpler. The number of
suitable programs is `cnt U s x`, and `M_j = {x : |x| = n, cnt x ≥ j}`.

If every `x` of length `n` has a program `p*`, `|p*| ≤ s`, with `U(p*, x)` of length `K(x)+1`
(this is `K(K(x) ∣ x) ≤ s` with `K(x)` written in unary), then `K(x)` is the least value
named by a suitable program. Knowing `N = |M_{i+1}|`, one can therefore:

1. enumerate `M_{i+1}` until `N` elements are seen, which determines `M_{i+1}` exactly;
2. for `x ∉ M_{i+1}` seen with `i` suitable programs, all suitable programs are found, so
   `K(x)` is known;
3. output the first such `x` with `K(x) ≥ m`.

Everything is made primitive recursive in a stage `t` (fuel for `evaln`): `runC`, `suitB`,
`cntB`, `condB`, `goodB`, `pickB`. The machine `dec` is `Nat.rfind` over stages, followed by
`pickB` (`dec_partrec`). Correctness is `dec_spec`.
-/

namespace Kolmogorov.Information.CompComp

open Nat.Partrec (Code)

/-! ### Primitive recursive helpers -/

theorem primrec_decide_le : Primrec (fun p : ℕ × ℕ ↦ decide (p.1 ≤ p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.nat_le : PrimrecRel ((· ≤ ·) : ℕ → ℕ → Prop))
  exact Primrec.of_eq h (fun p ↦ by congr)

theorem primrec_decide_lt : Primrec (fun p : ℕ × ℕ ↦ decide (p.1 < p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.nat_lt : PrimrecRel ((· < ·) : ℕ → ℕ → Prop))
  exact Primrec.of_eq h (fun p ↦ by congr)

theorem primrec_decide_eq {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec (fun p : α × α ↦ decide (p.1 = p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.eq : PrimrecRel (@Eq α))
  exact Primrec.of_eq h (fun p ↦ by congr)

/-- `List.countP` with a primitive recursive list and predicate is primitive recursive. -/
theorem primrec_countP {α β : Type*} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a ↦ (f a).countP (p a)) := by
  have heq : ∀ a, (f a).countP (p a) =
      (f a).foldr (fun b acc ↦ bif p a b then acc + 1 else acc) 0 := by
    intro a
    induction f a with
    | nil => rfl
    | cons b t ih =>
      rw [List.countP_cons, ih, List.foldr_cons]
      cases p a b <;> rfl
  have hstep : Primrec₂ (fun (a : α) (q : β × ℕ) ↦ bif p a q.1 then q.2 + 1 else q.2) :=
    (Primrec.cond (hp.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)).to₂
  exact (Primrec.list_foldr hf (Primrec.const 0) hstep).of_eq fun a ↦ (heq a).symm

/-! ### Generic list facts -/

/-- If `p ⊆ q` on `l` and the counts agree, then `p = q` on `l`. -/
theorem imp_of_countP_eq {β : Type*} (l : List β) (p q : β → Bool)
    (h : ∀ b ∈ l, p b = true → q b = true) (heq : l.countP p = l.countP q) :
    ∀ b ∈ l, q b = true → p b = true := by
  induction l with
  | nil => intro b hb; simp at hb
  | cons a t ih =>
    have ht : ∀ b ∈ t, p b = true → q b = true := fun b hb ↦ h b (List.mem_cons_of_mem _ hb)
    have hle : t.countP p ≤ t.countP q := List.countP_mono_left ht
    rw [List.countP_cons, List.countP_cons] at heq
    have hpa : q a = true → p a = true := by
      intro hqa
      by_contra hpa
      rw [Bool.not_eq_true] at hpa
      rw [hpa, hqa] at heq
      simp at heq
      omega
    have heqt : t.countP p = t.countP q := by
      by_cases hqa : q a = true
      · rw [hpa hqa, hqa] at heq; simpa using heq
      · rw [Bool.not_eq_true] at hqa
        have hpa' : p a = false := by
          by_contra hp'
          rw [Bool.not_eq_false] at hp'
          rw [h a List.mem_cons_self hp'] at hqa
          exact Bool.noConfusion hqa
        rw [hpa', hqa] at heq; simpa using heq
    intro b hb hqb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hpa hqb
    · exact ih ht heqt b hb hqb

/-- A monotone family of finite checks eventually confirms every true instance on a list. -/
theorem exists_stage {β : Type*} (l : List β) (Q : ℕ → β → Bool) (R : β → Prop)
    (hmono : ∀ b t t', t ≤ t' → Q t b = true → Q t' b = true)
    (hcomp : ∀ b ∈ l, R b → ∃ t, Q t b = true) :
    ∃ T, ∀ t, T ≤ t → ∀ b ∈ l, R b → Q t b = true := by
  induction l with
  | nil => exact ⟨0, fun _ _ b hb ↦ by simp at hb⟩
  | cons a l ih =>
    obtain ⟨T, hT⟩ := ih (fun b hb ↦ hcomp b (List.mem_cons_of_mem _ hb))
    by_cases ha : R a
    · obtain ⟨t₀, ht₀⟩ := hcomp a List.mem_cons_self ha
      refine ⟨max T t₀, fun t ht b hb hR ↦ ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hmono _ _ _ (le_of_max_le_right ht) ht₀
      · exact hT t (le_of_max_le_left ht) b hb hR
    · refine ⟨T, fun t ht b hb hR ↦ ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd hR ha
      · exact hT t ht b hb hR

theorem mem_exactLengthPrograms_iff {x : BitString} {n : ℕ} :
    x ∈ exactLengthPrograms n ↔ x.length = n := by
  constructor
  · exact exactLengthPrograms_length_eq n x
  · intro h
    have hb : x ∈ boundedPrograms n := (mem_boundedPrograms_iff x n).mpr h.le
    unfold boundedPrograms at hb
    obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hb
    have := exactLengthPrograms_length_eq k x hk
    rw [← h, this]
    exact hk

/-! ### Fuel-bounded runs of `U` -/

/-- `c` is a code for the machine `U`. -/
def CodeOf (U : Map) (c : Code) : Prop :=
  c.eval = fun n ↦ (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
    (fun a ↦ Part.map Encodable.encode (U a))

theorem exists_codeOf {U : Map} (hU : isDecompressor U) : ∃ c, CodeOf U c :=
  Nat.Partrec.Code.exists_code.mp hU

/-- Run `c` on `(p, x)` with fuel `t`, decoding the output. -/
def runC (c : Code) (t : ℕ) (p x : BitString) : Option BitString :=
  (Code.evaln t c (Encodable.encode (p, x))).bind (fun v ↦ Encodable.decode (α := BitString) v)

theorem runC_primrec (c : Code) :
    Primrec (fun q : ℕ × BitString × BitString ↦ runC c q.1 q.2.1 q.2.2) := by
  have h1 := Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair (Primrec.fst (α := ℕ) (β := BitString × BitString))
      (Primrec.const c)) (Primrec.encode.comp Primrec.snd))
  have h2 := Primrec.option_bind h1
    ((Primrec.decode (α := BitString)).comp (Primrec.snd (α := ℕ × BitString × BitString)
      (β := ℕ))).to₂
  exact h2.of_eq fun _ ↦ rfl

section Run

variable {U : Map} {c : Code}

theorem runC_sound (hc : CodeOf U c) {t : ℕ} {p x y : BitString}
    (h : runC c t p x = some y) : y ∈ U (p, x) := by
  unfold runC at h
  obtain ⟨v, hv, hdec⟩ := Option.bind_eq_some_iff.mp h
  have hev : v ∈ c.eval (Encodable.encode (p, x)) :=
    Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hv)
  rw [hc, Part.mem_bind_iff] at hev
  obtain ⟨a, ha, hva⟩ := hev
  rw [Part.mem_ofOption, Encodable.encodek] at ha
  have ha' := Option.some_inj.mp (Option.mem_def.mp ha)
  subst ha'
  obtain ⟨b, hb, hbv⟩ := (Part.mem_map_iff _).mp hva
  subst hbv
  rw [Encodable.encodek] at hdec
  cases hdec
  exact hb

theorem runC_complete (hc : CodeOf U c) {p x y : BitString} (h : y ∈ U (p, x)) :
    ∃ t, runC c t p x = some y := by
  have hmem : Encodable.encode y ∈ c.eval (Encodable.encode (p, x)) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨(p, x), by simp [Encodable.encodek], Part.mem_map Encodable.encode h⟩
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
  refine ⟨k, ?_⟩
  unfold runC
  rw [Option.mem_def.mp hk]
  simp [Encodable.encodek]

theorem runC_mono {t t' : ℕ} (h : t ≤ t') {p x y : BitString}
    (hy : runC c t p x = some y) : runC c t' p x = some y := by
  unfold runC at hy ⊢
  obtain ⟨v, hv, hdec⟩ := Option.bind_eq_some_iff.mp hy
  have := Nat.Partrec.Code.evaln_mono h (Option.mem_def.mpr hv)
  rw [Option.mem_def.mp this]
  exact hdec

end Run

/-! ### Suitable programs, by stage and in the limit -/

/-- Stage-`t` witness that `x` has a program of length `≤ k`. -/
def validB (c : Code) (t k : ℕ) (x : BitString) : Bool :=
  (boundedPrograms k).any (fun q ↦ decide (runC c t q [] = some x))

/-- Stage-`t` suitability: `U(p, x)` has halted with `y`, and `x` has a program of length
`≤ |y| − 1` found by stage `t`. -/
def suitB (c : Code) (t : ℕ) (p x : BitString) : Bool :=
  ((runC c t p x).map (fun y ↦ validB c t (y.length - 1) x)).getD false

/-- A suitable program naming a value `< m`. -/
def badB (c : Code) (t m : ℕ) (p x : BitString) : Bool :=
  suitB c t p x && decide ((((runC c t p x).map (fun y ↦ y.length - 1)).getD 0) < m)

/-- **Suitability** in the limit. -/
def Suit (U : Map) (p x : BitString) : Prop :=
  ∃ y, y ∈ U (p, x) ∧ KP U x [] ≤ ((y.length - 1 : ℕ) : ENat)

/-- Stage-`t` count of suitable programs of length `≤ s`. -/
def cntB (c : Code) (t s : ℕ) (x : BitString) : ℕ :=
  (boundedPrograms s).countP (fun p ↦ suitB c t p x)

open Classical in
/-- The number of suitable programs of length `≤ s`. -/
noncomputable def cnt (U : Map) (s : ℕ) (x : BitString) : ℕ :=
  (boundedPrograms s).countP (fun p ↦ decide (Suit U p x))

section Suit

variable {U : Map} {c : Code}

theorem validB_mono {t t' k : ℕ} (h : t ≤ t') {x : BitString} (hv : validB c t k x = true) :
    validB c t' k x = true := by
  unfold validB at hv ⊢
  obtain ⟨q, hq, hqx⟩ := List.any_eq_true.mp hv
  exact List.any_eq_true.mpr ⟨q, hq, by
    rw [decide_eq_true_iff] at hqx ⊢; exact runC_mono h hqx⟩

theorem suitB_eq {t : ℕ} {p x y : BitString} (h : runC c t p x = some y) :
    suitB c t p x = validB c t (y.length - 1) x := by
  unfold suitB; rw [h]; rfl

theorem suitB_mono {t t' : ℕ} (h : t ≤ t') {p x : BitString} (hs : suitB c t p x = true) :
    suitB c t' p x = true := by
  unfold suitB at hs
  cases hr : runC c t p x with
  | none => rw [hr] at hs; exact absurd hs (by simp)
  | some y =>
    rw [hr] at hs
    rw [suitB_eq (runC_mono h hr)]
    exact validB_mono h hs

theorem suitB_sound (hc : CodeOf U c) {t : ℕ} {p x y : BitString}
    (hr : runC c t p x = some y) (hs : suitB c t p x = true) :
    y ∈ U (p, x) ∧ KP U x [] ≤ ((y.length - 1 : ℕ) : ENat) := by
  refine ⟨runC_sound hc hr, ?_⟩
  rw [suitB_eq hr] at hs
  unfold validB at hs
  obtain ⟨q, hq, hqx⟩ := List.any_eq_true.mp hs
  rw [decide_eq_true_iff] at hqx
  have hprod : x ∈ U (q, []) := runC_sound hc hqx
  change condK U x [] ≤ _
  exact (condKLeIff U x [] _).mpr ⟨q, (mem_boundedPrograms_iff q _).mp hq, hprod⟩

theorem suit_of_suitB (hc : CodeOf U c) {t : ℕ} {p x : BitString}
    (hs : suitB c t p x = true) : Suit U p x := by
  cases hr : runC c t p x with
  | none => unfold suitB at hs; rw [hr] at hs; exact absurd hs (by simp)
  | some y => exact ⟨y, suitB_sound hc hr hs⟩

theorem suitB_complete (hc : CodeOf U c) {p x : BitString} (h : Suit U p x) :
    ∃ t, suitB c t p x = true := by
  obtain ⟨y, hy, hK⟩ := h
  obtain ⟨t₁, ht₁⟩ := runC_complete hc hy
  obtain ⟨q, hq, hqx⟩ := (condKLeIff U x [] _).mp hK
  obtain ⟨t₂, ht₂⟩ := runC_complete hc hqx
  refine ⟨max t₁ t₂, ?_⟩
  rw [suitB_eq (runC_mono (le_max_left _ _) ht₁)]
  unfold validB
  exact List.any_eq_true.mpr ⟨q, (mem_boundedPrograms_iff q _).mpr hq, by
    rw [decide_eq_true_iff]; exact runC_mono (le_max_right _ _) ht₂⟩

theorem cntB_le_cnt (hc : CodeOf U c) (t s : ℕ) (x : BitString) : cntB c t s x ≤ cnt U s x := by
  classical
  unfold cntB cnt
  refine List.countP_mono_left fun p _ hp ↦ ?_
  simpa using suit_of_suitB hc hp

end Suit

/-! ### The stage predicates of the search -/

/-- The number of suitable programs naming a value `< m`, seen at stage `t`. -/
def badCount (c : Code) (t s m : ℕ) (x : BitString) : ℕ :=
  (boundedPrograms s).countP (fun p ↦ badB c t m p x)

/-- `x` is a candidate at stage `t`: exactly `i` suitable programs seen, none naming `< m`. -/
def condB (c : Code) (t s i m : ℕ) (x : BitString) : Bool :=
  decide (cntB c t s x = i) && decide (badCount c t s m x = 0)

/-- Stage-`t` size of `M_j`. -/
def mcountB (c : Code) (t s n j : ℕ) : ℕ :=
  (exactLengthPrograms n).countP (fun x ↦ decide (j ≤ cntB c t s x))

/-- Parameters `(n, s, i, N, m)`. -/
abbrev Params := ℕ × ℕ × ℕ × ℕ × ℕ

/-- The search succeeds at stage `t`: `|M_{i+1}| = N` is reached and a candidate exists. -/
def goodB (c : Code) (q : Params) (t : ℕ) : Bool :=
  decide (q.2.2.2.1 ≤ mcountB c t q.2.1 q.1 (q.2.2.1 + 1)) &&
    (exactLengthPrograms q.1).any (fun x ↦ condB c t q.2.1 q.2.2.1 q.2.2.2.2 x)

/-- The first candidate at stage `t`. -/
def pickB (c : Code) (q : Params) (t : ℕ) : BitString :=
  (exactLengthPrograms q.1).getD
    ((exactLengthPrograms q.1).findIdx (fun x ↦ condB c t q.2.1 q.2.2.1 q.2.2.2.2 x)) []

/-! ### Primitive recursiveness -/

section Primrec

variable (c : Code)

theorem validB_primrec : Primrec (fun r : ℕ × ℕ × BitString ↦ validB c r.1 r.2.1 r.2.2) := by
  have hl := primrec_boundedPrograms.comp
    (Primrec.fst.comp (Primrec.snd (α := ℕ) (β := ℕ × BitString)))
  have hrun := (runC_primrec c).comp (Primrec.pair
    (Primrec.fst.comp (Primrec.fst (α := ℕ × ℕ × BitString) (β := BitString)))
    (Primrec.pair Primrec.snd (Primrec.const ([] : BitString))))
  have hp := primrec_decide_eq.comp (Primrec.pair hrun
    (Primrec.option_some.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  exact (list_any_primrec hl hp.to₂).of_eq fun _ ↦ rfl

theorem suitB_primrec : Primrec (fun r : ℕ × BitString × BitString ↦ suitB c r.1 r.2.1 r.2.2) := by
  have hrun := runC_primrec c
  have hv := (validB_primrec c).comp (Primrec.pair
    (Primrec.fst.comp (Primrec.fst (α := ℕ × BitString × BitString) (β := BitString)))
    (Primrec.pair (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 1))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have h := Primrec.option_getD.comp (Primrec.option_map hrun hv.to₂) (Primrec.const false)
  exact h.of_eq fun _ ↦ rfl

theorem badB_primrec :
    Primrec (fun r : (ℕ × ℕ) × BitString × BitString ↦ badB c r.1.1 r.1.2 r.2.1 r.2.2) := by
  have hs := (suitB_primrec c).comp (Primrec.pair
    (Primrec.fst.comp (Primrec.fst (α := ℕ × ℕ) (β := BitString × BitString))) Primrec.snd)
  have hrun := (runC_primrec c).comp (Primrec.pair
    (Primrec.fst.comp (Primrec.fst (α := ℕ × ℕ) (β := BitString × BitString))) Primrec.snd)
  have hk := Primrec.option_getD.comp (Primrec.option_map hrun
    (Primrec.nat_sub.comp (Primrec.list_length.comp (Primrec.snd (α := (ℕ × ℕ) ×
      BitString × BitString) (β := BitString))) (Primrec.const 1)).to₂) (Primrec.const 0)
  have hlt := primrec_decide_lt.comp (Primrec.pair hk (Primrec.snd.comp Primrec.fst))
  exact (Primrec.and.comp hs hlt).of_eq fun _ ↦ rfl

theorem cntB_primrec : Primrec (fun r : (ℕ × ℕ) × BitString ↦ cntB c r.1.1 r.1.2 r.2) := by
  have hl := primrec_boundedPrograms.comp (Primrec.snd.comp
    (Primrec.fst (α := ℕ × ℕ) (β := BitString)))
  have hp := (suitB_primrec c).comp (Primrec.pair
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst (α := (ℕ × ℕ) × BitString)
      (β := BitString))))
    (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)))
  exact (primrec_countP hl hp.to₂).of_eq fun _ ↦ rfl

/-- `badCount` as a function of `((t, s, m), x)`. -/
theorem badCount_primrec :
    Primrec (fun r : (ℕ × ℕ × ℕ) × BitString ↦ badCount c r.1.1 r.1.2.1 r.1.2.2 r.2) := by
  have hl := primrec_boundedPrograms.comp (Primrec.fst.comp (Primrec.snd.comp
    (Primrec.fst (α := ℕ × ℕ × ℕ) (β := BitString))))
  have hbad := (badB_primrec c).comp (Primrec.pair (Primrec.pair
    (Primrec.fst.comp (Primrec.fst.comp (Primrec.fst (α := (ℕ × ℕ × ℕ) × BitString)
      (β := BitString))))
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
    (Primrec.pair Primrec.snd (Primrec.snd.comp Primrec.fst)))
  exact (primrec_countP hl hbad.to₂).of_eq fun _ ↦ rfl

/-- `condB` as a function of `((t, s, i, m), x)`. -/
theorem condB_primrec :
    Primrec (fun r : (ℕ × ℕ × ℕ × ℕ) × BitString ↦
      condB c r.1.1 r.1.2.1 r.1.2.2.1 r.1.2.2.2 r.2) := by
  have hcnt := (cntB_primrec c).comp (Primrec.pair (Primrec.pair
    (Primrec.fst.comp (Primrec.fst (α := ℕ × ℕ × ℕ × ℕ) (β := BitString)))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  have heq := primrec_decide_eq.comp (Primrec.pair hcnt
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.fst (α := ℕ × ℕ × ℕ × ℕ) (β := BitString))))))
  have hbc := (badCount_primrec c).comp (Primrec.pair (Primrec.pair
    (Primrec.fst.comp (Primrec.fst (α := ℕ × ℕ × ℕ × ℕ) (β := BitString)))
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))) Primrec.snd)
  have hz := primrec_decide_eq.comp (Primrec.pair hbc (Primrec.const 0))
  have h := Primrec.and.comp heq hz
  exact h.of_eq fun r ↦ by unfold condB; rfl

theorem mcountB_primrec :
    Primrec (fun r : ℕ × ℕ × ℕ × ℕ ↦ mcountB c r.1 r.2.1 r.2.2.1 r.2.2.2) := by
  have hl := primrec_exactLengthPrograms.comp (Primrec.fst.comp (Primrec.snd.comp
    (Primrec.snd (α := ℕ) (β := ℕ × ℕ × ℕ))))
  have hcnt := (cntB_primrec c).comp (Primrec.pair (Primrec.pair
    (Primrec.fst.comp (Primrec.fst (α := ℕ × ℕ × ℕ × ℕ) (β := BitString)))
    (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  have hp := primrec_decide_le.comp (Primrec.pair
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) hcnt)
  exact (primrec_countP hl hp.to₂).of_eq fun _ ↦ rfl

/-- The stage-`t` candidate test, as a function of `((q, t), x)`. -/
theorem condB_param_primrec :
    Primrec₂ (fun (r : Params × ℕ) (x : BitString) ↦
      condB c r.2 r.1.2.1 r.1.2.2.1 r.1.2.2.2.2 x) := by
  have h := (condB_primrec c).comp (Primrec.pair (Primrec.pair
    (Primrec.snd.comp (Primrec.fst (α := Params × ℕ) (β := BitString)))
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
      (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.fst.comp Primrec.fst))))
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
          (Primrec.fst.comp Primrec.fst))))))))
    Primrec.snd)
  exact (h.of_eq fun _ ↦ rfl).to₂

theorem goodB_primrec : Primrec₂ (goodB c) := by
  have hm := (mcountB_primrec c).comp (Primrec.pair
    (Primrec.snd (α := Params) (β := ℕ))
    (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
          Primrec.fst)))))))
  have hle := primrec_decide_le.comp (Primrec.pair
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.fst (α := Params) (β := ℕ)))))) hm)
  have hl := primrec_exactLengthPrograms.comp (Primrec.fst.comp
    (Primrec.fst (α := Params) (β := ℕ)))
  have hany := list_any_primrec hl (condB_param_primrec c)
  exact (Primrec.and.comp hle hany).of_eq fun _ ↦ rfl

theorem pickB_primrec : Primrec₂ (pickB c) := by
  have hl := primrec_exactLengthPrograms.comp (Primrec.fst.comp
    (Primrec.fst (α := Params) (β := ℕ)))
  have hidx := Primrec.list_findIdx hl (condB_param_primrec c)
  exact ((Primrec.list_getD ([] : BitString)).comp hl hidx).of_eq fun _ ↦ rfl

end Primrec

/-! ### Parameters as a bit string, and the machine -/

/-- The parameters `(n, s, i, N, m)` packed into one string. -/
def encParams (q : Params) : BitString :=
  pairCode (Nat.bits q.1) (pairCode (Nat.bits q.2.1) (pairCode (Nat.bits q.2.2.1)
    (pairCode (Nat.bits q.2.2.2.1) (Nat.bits q.2.2.2.2))))

/-- Unpacking. -/
def decParams (a : BitString) : Params :=
  (bitsToNat (decodeFirst a), bitsToNat (decodeFirst (decodeSecond a)),
    bitsToNat (decodeFirst (decodeSecond (decodeSecond a))),
    bitsToNat (decodeFirst (decodeSecond (decodeSecond (decodeSecond a)))),
    bitsToNat (decodeSecond (decodeSecond (decodeSecond (decodeSecond a)))))

theorem decParams_encParams (q : Params) : decParams (encParams q) = q := by
  simp [decParams, encParams, decodeFirst_pairCode, decodeSecond_pairCode, bitsToNat_bits]

theorem decParams_computable : Computable decParams := by
  have hF := decodeFirst_computable
  have hS := decodeSecond_computable
  have hb := bitsToNat_computable
  exact Computable.pair (hb.comp hF) (Computable.pair (hb.comp (hF.comp hS))
    (Computable.pair (hb.comp (hF.comp (hS.comp hS)))
      (Computable.pair (hb.comp (hF.comp (hS.comp (hS.comp hS))))
        (hb.comp (hS.comp (hS.comp (hS.comp hS)))))))

/-- **The search machine**: find the first good stage and output its candidate. -/
def dec (c : Code) (a : BitString) : Part BitString :=
  (Nat.rfind fun t ↦ Part.some (goodB c (decParams a) t)).map
    (fun t ↦ pickB c (decParams a) t)

theorem dec_partrec (c : Code) : Partrec (dec c) := by
  have hg : Computable₂ (fun (a : BitString) (t : ℕ) ↦ goodB c (decParams a) t) :=
    ((goodB_primrec c).to_comp.comp (decParams_computable.comp Computable.fst)
      Computable.snd).to₂
  have hp : Computable₂ (fun (a : BitString) (t : ℕ) ↦ pickB c (decParams a) t) :=
    ((pickB_primrec c).to_comp.comp (decParams_computable.comp Computable.fst)
      Computable.snd).to₂
  exact (Partrec.map (Partrec.rfind hg.partrec₂) hp).of_eq fun _ ↦ rfl

/-! ### Correctness -/

section Spec

variable {U : Map} {c : Code}

theorem cntB_eq_cnt_of_stage (hc : CodeOf U c) {s t : ℕ} {x : BitString}
    (hT : ∀ p ∈ boundedPrograms s, Suit U p x → suitB c t p x = true) :
    cntB c t s x = cnt U s x := by
  classical
  unfold cntB cnt
  refine List.countP_congr fun p hp ↦ ?_
  constructor
  · intro h; simpa using suit_of_suitB hc h
  · intro h; exact hT p hp (by simpa using h)

/-- **Correctness of the search.** Suppose every `x` of length `n` has a program
`|p| ≤ s` with `U(p, x)` of length `K(x) + 1`, that `N = |M_{i+1}|`, and that some `x₀` of
length `n` has exactly `i` suitable programs and `K(x₀) ≥ m`. Then the machine outputs some
`x` with `K(x) ≥ m`. -/
theorem dec_spec (hc : CodeOf U c) {n s i N m : ℕ}
    (hs : ∀ x : BitString, x.length = n → ∃ p, p.length ≤ s ∧ ∃ y, y ∈ U (p, x) ∧
      KP U x [] = ((y.length - 1 : ℕ) : ENat))
    (hN : (exactLengthPrograms n).countP (fun x ↦ decide (i + 1 ≤ cnt U s x)) = N)
    (hx₀ : ∃ x₀, x₀.length = n ∧ cnt U s x₀ = i ∧ (m : ENat) ≤ KP U x₀ []) :
    ∃ x, x ∈ dec c (encParams (n, s, i, N, m)) ∧ (m : ENat) ≤ KP U x [] := by
  classical
  set q : Params := (n, s, i, N, m) with hq
  -- A stage after which every suitable pair is confirmed.
  obtain ⟨T, hT⟩ := exists_stage ((boundedPrograms s).product (exactLengthPrograms n))
    (fun t r ↦ suitB c t r.1 r.2) (fun r ↦ Suit U r.1 r.2)
    (fun r t t' h hs ↦ suitB_mono h hs)
    (fun r _ hr ↦ suitB_complete hc hr)
  have hTx : ∀ t, T ≤ t → ∀ x ∈ exactLengthPrograms n, ∀ p ∈ boundedPrograms s,
      Suit U p x → suitB c t p x = true := fun t ht x hx p hp hS ↦
    hT t ht (p, x) (List.pair_mem_product.mpr ⟨hp, hx⟩) hS
  -- The stage `T` is good.
  have hgoodT : goodB c q T = true := by
    obtain ⟨x₀, hx₀n, hx₀i, hx₀m⟩ := hx₀
    have hx₀mem : x₀ ∈ exactLengthPrograms n := mem_exactLengthPrograms_iff.mpr hx₀n
    unfold goodB
    rw [Bool.and_eq_true, decide_eq_true_iff]
    refine ⟨?_, List.any_eq_true.mpr ⟨x₀, hx₀mem, ?_⟩⟩
    · change N ≤ mcountB c T s n (i + 1)
      unfold mcountB
      rw [← hN]
      refine le_of_eq (List.countP_congr fun x hx ↦ ?_)
      rw [cntB_eq_cnt_of_stage hc (fun p hp hS ↦ hTx T le_rfl x hx p hp hS)]
    · change condB c T s i m x₀ = true
      unfold condB
      rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
        cntB_eq_cnt_of_stage hc (fun p hp hS ↦ hTx T le_rfl x₀ hx₀mem p hp hS), hx₀i]
      refine ⟨rfl, List.countP_eq_zero.mpr fun p _ hbad ↦ ?_⟩
      unfold badB at hbad
      rw [Bool.and_eq_true, decide_eq_true_iff] at hbad
      obtain ⟨hsuit, hlt⟩ := hbad
      cases hr : runC c T p x₀ with
      | none => unfold suitB at hsuit; rw [hr] at hsuit; exact absurd hsuit (by simp)
      | some y =>
        rw [hr] at hlt
        have hK := (suitB_sound hc hr hsuit).2
        have : (m : ENat) ≤ ((y.length - 1 : ℕ) : ENat) := hx₀m.trans hK
        have : m ≤ y.length - 1 := by exact_mod_cast this
        exact absurd hlt (by simpa using this)
  -- The machine halts at the least good stage.
  have hdom : (Nat.rfind fun t ↦ Part.some (goodB c q t)).Dom :=
    Nat.rfind_dom.mpr ⟨T, by simpa using hgoodT, fun _ ↦ trivial⟩
  set t := (Nat.rfind fun t ↦ Part.some (goodB c q t)).get hdom with ht
  have htmem : t ∈ Nat.rfind fun t ↦ Part.some (goodB c q t) := Part.get_mem hdom
  have hgood : goodB c q t = true := by simpa using Nat.rfind_spec htmem
  refine ⟨pickB c q t, ?_, ?_⟩
  · unfold dec
    rw [decParams_encParams]
    exact Part.mem_map _ htmem
  -- Correctness of the output.
  unfold goodB at hgood
  rw [Bool.and_eq_true, decide_eq_true_iff] at hgood
  obtain ⟨hNle, hany⟩ := hgood
  change N ≤ mcountB c t s n (i + 1) at hNle
  change ((exactLengthPrograms n).any fun x ↦ condB c t s i m x) = true at hany
  set l := exactLengthPrograms n
  have hex : ∃ x ∈ l, condB c t s i m x = true := List.any_eq_true.mp hany
  have hidx : l.findIdx (fun x ↦ condB c t s i m x) < l.length :=
    List.findIdx_lt_length_of_exists hex
  set x := pickB c q t with hx
  have hxl : x = l[l.findIdx (fun x ↦ condB c t s i m x)] := by
    rw [hx]; unfold pickB; exact List.getD_eq_getElem _ _ hidx
  have hxmem : x ∈ l := by rw [hxl]; exact List.getElem_mem _
  have hxcond : condB c t s i m x = true := by
    rw [hxl]; exact List.findIdx_getElem (w := hidx)
  -- Stage `t` already sees all of `M_{i+1}`.
  have hMeq : (l.countP fun x ↦ decide (i + 1 ≤ cntB c t s x)) =
      l.countP fun x ↦ decide (i + 1 ≤ cnt U s x) := by
    refine le_antisymm (List.countP_mono_left fun x _ h ↦ ?_) ?_
    · simp only [decide_eq_true_iff] at h ⊢; exact h.trans (cntB_le_cnt hc t s x)
    · rw [hN]; exact hNle
  have hM : ∀ x ∈ l, i + 1 ≤ cnt U s x → i + 1 ≤ cntB c t s x := fun x hx h ↦ by
    have := imp_of_countP_eq l (fun x ↦ decide (i + 1 ≤ cntB c t s x))
      (fun x ↦ decide (i + 1 ≤ cnt U s x))
      (fun x _ h ↦ by
        simp only [decide_eq_true_iff] at h ⊢; exact h.trans (cntB_le_cnt hc t s x))
      hMeq x hx (by simpa using h)
    simpa using this
  unfold condB at hxcond
  rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff] at hxcond
  obtain ⟨hcntx, hbad0⟩ := hxcond
  -- All suitable programs of `x` are seen at stage `t`.
  have hcnteq : cntB c t s x = cnt U s x := by
    have h1 := cntB_le_cnt hc t s x
    have h2 : ¬ i + 1 ≤ cnt U s x := fun h ↦ by have := hM x hxmem h; omega
    omega
  have hall : ∀ p ∈ boundedPrograms s, Suit U p x → suitB c t p x = true := by
    intro p hp hS
    have := imp_of_countP_eq (boundedPrograms s) (fun p ↦ suitB c t p x)
      (fun p ↦ decide (Suit U p x))
      (fun p _ h ↦ by simpa using suit_of_suitB hc h)
      (by rw [show (boundedPrograms s).countP (fun p ↦ suitB c t p x) = cntB c t s x from rfl,
        hcnteq]; rfl) p hp (by simpa using hS)
    exact this
  -- The program naming `K(x)` is suitable, hence seen, hence names a value `≥ m`.
  obtain ⟨p, hps, y, hy, hKy⟩ := hs x (exactLengthPrograms_length_eq n x hxmem)
  have hSuit : Suit U p x := ⟨y, hy, hKy.le⟩
  have hsuitB := hall p ((mem_boundedPrograms_iff p s).mpr hps) hSuit
  obtain ⟨y', hr⟩ : ∃ y', runC c t p x = some y' := by
    cases hr : runC c t p x with
    | none => unfold suitB at hsuitB; rw [hr] at hsuitB; exact absurd hsuitB (by simp)
    | some y' => exact ⟨y', rfl⟩
  have hyy : y' = y := Part.mem_unique (runC_sound hc hr) hy
  subst hyy
  have hnotbad : badB c t m p x = false := by
    by_contra hb
    rw [Bool.not_eq_false] at hb
    have := (List.countP_pos_iff (p := fun p ↦ badB c t m p x)).mpr
      ⟨p, (mem_boundedPrograms_iff p s).mpr hps, hb⟩
    unfold badCount at hbad0
    omega
  unfold badB at hnotbad
  rw [hsuitB, Bool.true_and, decide_eq_false_iff_not, hr] at hnotbad
  simp only [Option.map_some, Option.getD_some, not_lt] at hnotbad
  rw [hKy]
  exact_mod_cast hnotbad

end Spec

end Kolmogorov.Information.CompComp
