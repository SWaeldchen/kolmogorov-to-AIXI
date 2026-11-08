/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Oracle.Defs
import Gacs_Chapter_2.Randomness.LevinSchnorr

/-!
# The monotone prefix filter for oracle machines

The oracle analogue of the upstream online prefix filter `prefixFiltered`
(`KolmogorovMathlib/Prefix/OptimalExistence.lean`). Fix a code `c`, read as a conditional map
`W(q, σ)` whose condition `σ` is a finite oracle prefix.

* **Candidates.** Index `n` encodes a triple `(q, j, s)`: `q = decode n.unpair.1`,
  `j = n.unpair.2.unpair.1` (how much of the oracle prefix is used), `s = n.unpair.2.unpair.2`
  (fuel). Candidate `n` **appears** at the oracle prefix `σ` (`oracleFilterAppears`) when
  `n ≤ |σ|` and `c` halts on `(q, σ↾j)` within `s + 1` steps. Since `j ≤ n`, the guard
  `n ≤ |σ|` makes the appearance of every `n' ≤ n` depend only on `σ↾n`: **appearances are
  stable under extending `σ`** (`oracleFilterAppears_of_prefix`).
* **Acceptance.** As upstream: `q` is accepted at its first appearance `N` if no earlier
  index carries a distinct comparable program; the output is the result of the computation of
  candidate `N`.

Hence the filtered machine `oracleFilterMachine c`

* is a prefix machine in every condition (`oracleFilterMachine_isPrefixMachine`),
* is monotone in the condition (`oracleFilterMachine_mono`), so it is an oracle machine
  (`oracleFilterMachine_isOracleMachine`), and
* if `c` computes an oracle machine `W`, it attains `K_W(x ∣ A)` in the limit over oracle
  prefixes (`KPrel_oracleFilterMachine_le`): the only program comparable to an accepted `q`
  that could appear earlier is `q` itself, by monotonicity and prefix-freeness of `W`.
-/

namespace Kolmogorov.Information.Oracle

open Nat.Partrec (Code)
open Kolmogorov.Randomness (Seq seqTake length_seqTake seqTake_prefix take_seqTake)

/-! ### Candidates -/

/-- The oracle-use component of candidate `n`. -/
def oracleFilterJ (n : ℕ) : ℕ := n.unpair.2.unpair.1

/-- The fuel component of candidate `n`. -/
def oracleFilterS (n : ℕ) : ℕ := n.unpair.2.unpair.2

theorem oracleFilterJ_le (n : ℕ) : oracleFilterJ n ≤ n :=
  (Nat.unpair_left_le _).trans (Nat.unpair_right_le _)

/-- The halting test of candidate `n` for the program `q`. -/
def oracleFilterInner (c : Code) (σ : BitString) (n : ℕ) (q : BitString) : Option BitString :=
  if (Code.evaln (oracleFilterS n + 1) c
      (Encodable.encode (q, σ.take (oracleFilterJ n)))).isSome then some q else none

/-- The program appearing at index `n` under the oracle prefix `σ`, if any. -/
def oracleFilterAppears (c : Code) (σ : BitString) (n : ℕ) : Option BitString :=
  if n ≤ σ.length then
    (Encodable.decode n.unpair.1 : Option BitString).bind (oracleFilterInner c σ n)
  else none

/-- The local prefix-freeness test at index `n` against `q`. -/
def oracleFilterGood (c : Code) (σ q : BitString) (n : ℕ) : Bool :=
  Option.casesOn (oracleFilterAppears c σ n) true (fun q' ↦ goodBool q' q)

/-- The acceptance test over the indices below `N`. -/
def oracleFilterAccept (c : Code) (σ q : BitString) (N : ℕ) : Bool :=
  (List.range N).foldr (fun n acc ↦ oracleFilterGood c σ q n && acc) true

/-- **The monotone prefix-filtered oracle machine** of a code `c`. -/
def oracleFilterMachine (c : Code) : Map := fun pr ↦
  (Nat.rfind fun n ↦ Part.some (decide (oracleFilterAppears c pr.2 n = some pr.1))).bind
    fun N ↦
      bif oracleFilterAccept c pr.2 pr.1 N then
        (c.eval (Encodable.encode (pr.1, pr.2.take (oracleFilterJ N)))).map decodeGetD
      else Part.none

/-! ### Elementary facts -/

theorem oracleFilterAppears_le {c : Code} {σ : BitString} {n : ℕ} {q : BitString}
    (h : oracleFilterAppears c σ n = some q) : n ≤ σ.length := by
  unfold oracleFilterAppears at h
  by_contra hn
  rw [if_neg hn] at h
  simp at h

theorem oracleFilterAppears_spec {c : Code} {σ : BitString} {n : ℕ} {q : BitString}
    (h : oracleFilterAppears c σ n = some q) :
    (Encodable.decode n.unpair.1 : Option BitString) = some q ∧
      (Code.evaln (oracleFilterS n + 1) c
        (Encodable.encode (q, σ.take (oracleFilterJ n)))).isSome = true := by
  have hn := oracleFilterAppears_le h
  unfold oracleFilterAppears at h
  rw [if_pos hn] at h
  cases hd : (Encodable.decode n.unpair.1 : Option BitString) with
  | none => rw [hd] at h; simp at h
  | some q' =>
    rw [hd] at h
    simp only [Option.bind, oracleFilterInner] at h
    split at h
    · obtain rfl := Option.some.inj h; exact ⟨rfl, by assumption⟩
    · simp at h

theorem oracleFilterAppears_eval_dom {c : Code} {σ : BitString} {n : ℕ} {q : BitString}
    (h : oracleFilterAppears c σ n = some q) :
    (c.eval (Encodable.encode (q, σ.take (oracleFilterJ n)))).Dom := by
  obtain ⟨_, hs⟩ := oracleFilterAppears_spec h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
  exact Part.dom_iff_mem.mpr ⟨v, Nat.Partrec.Code.evaln_complete.mpr ⟨_, hv⟩⟩

/-- Taking a short prefix of an extension is taking it of the original. -/
theorem take_of_prefix {σ τ : BitString} (h : σ <+: τ) {j : ℕ} (hj : j ≤ σ.length) :
    τ.take j = σ.take j := by
  rw [List.prefix_iff_eq_take.mp h, List.take_take, min_eq_left hj]

/-- **Appearances are stable under extending the oracle prefix.** -/
theorem oracleFilterAppears_of_prefix (c : Code) {σ τ : BitString} (h : σ <+: τ) {n : ℕ}
    (hn : n ≤ σ.length) : oracleFilterAppears c τ n = oracleFilterAppears c σ n := by
  have hτ : n ≤ τ.length := hn.trans h.length_le
  have hinner : oracleFilterInner c τ n = oracleFilterInner c σ n := by
    funext q
    unfold oracleFilterInner
    rw [take_of_prefix h ((oracleFilterJ_le n).trans hn)]
  unfold oracleFilterAppears
  rw [if_pos hn, if_pos hτ, hinner]

theorem oracleFilterGood_of_prefix (c : Code) {σ τ : BitString} (h : σ <+: τ) (q : BitString)
    {n : ℕ} (hn : n ≤ σ.length) : oracleFilterGood c τ q n = oracleFilterGood c σ q n := by
  unfold oracleFilterGood; rw [oracleFilterAppears_of_prefix c h hn]

/-- A conjunctive `foldr` over a list is `true` iff each entry is `true`. -/
theorem oracleFilter_foldr_and_true_iff (l : List ℕ) (f : ℕ → Bool) :
    (l.foldr (fun n acc ↦ f n && acc) true) = true ↔ ∀ n ∈ l, f n = true := by
  induction l with
  | nil => simp
  | cons a t ih => simp [ih]

theorem oracleFilterAccept_eq_true_iff {c : Code} {σ q : BitString} {N : ℕ} :
    oracleFilterAccept c σ q N = true ↔ ∀ n < N, oracleFilterGood c σ q n = true := by
  unfold oracleFilterAccept
  rw [oracleFilter_foldr_and_true_iff]
  simp [List.mem_range]

theorem oracleFilterGood_eq_false_iff {c : Code} {σ q : BitString} {n : ℕ} :
    oracleFilterGood c σ q n = false ↔
      ∃ q', oracleFilterAppears c σ n = some q' ∧ q' ≠ q ∧ (q' <+: q ∨ q <+: q') := by
  unfold oracleFilterGood
  cases h : oracleFilterAppears c σ n with
  | none => simp
  | some q' =>
    simp only [goodBool_eq, decide_eq_false_iff_not, not_not]
    constructor
    · intro hf; exact ⟨q', rfl, hf⟩
    · rintro ⟨q'', hq'', hne, hcomp⟩
      obtain rfl := Option.some.inj hq''
      exact ⟨hne, hcomp⟩

/-! ### Membership -/

theorem mem_oracleFilterMachine_iff {c : Code} {q σ x : BitString} :
    x ∈ oracleFilterMachine c (q, σ) ↔
      ∃ N, (oracleFilterAppears c σ N = some q ∧ ∀ m < N, oracleFilterAppears c σ m ≠ some q) ∧
        oracleFilterAccept c σ q N = true ∧
        x ∈ (c.eval (Encodable.encode (q, σ.take (oracleFilterJ N)))).map decodeGetD := by
  unfold oracleFilterMachine
  simp only [Part.mem_bind_iff, Nat.mem_rfind, Part.mem_some_iff]
  constructor
  · rintro ⟨N, ⟨hN, hlt⟩, hmem⟩
    refine ⟨N, ⟨of_decide_eq_true hN.symm, fun m hm ↦ of_decide_eq_false (hlt hm).symm⟩, ?_⟩
    cases hb : oracleFilterAccept c σ q N with
    | true => rw [hb] at hmem; exact ⟨rfl, by simpa using hmem⟩
    | false => rw [hb] at hmem; simp at hmem
  · rintro ⟨N, ⟨hN, hlt⟩, hacc, hmem⟩
    refine ⟨N, ⟨?_, ?_⟩, ?_⟩
    · rw [hN]; exact (decide_eq_true rfl).symm
    · intro m hm; exact (decide_eq_false (hlt m hm)).symm
    · rw [hacc]; simpa using hmem

/-! ### Prefix-freeness and monotonicity -/

theorem oracleFilterMachine_isPrefixMachine (c : Code) :
    IsPrefixMachine (oracleFilterMachine c) := by
  intro σ p hp q hq hpre
  by_contra hne
  obtain ⟨xp, hxp⟩ := Part.dom_iff_mem.mp hp
  obtain ⟨Np, ⟨hNp, _⟩, haccp, _⟩ := mem_oracleFilterMachine_iff.mp hxp
  obtain ⟨xq, hxq⟩ := Part.dom_iff_mem.mp hq
  obtain ⟨Nq, ⟨hNq, _⟩, haccq, _⟩ := mem_oracleFilterMachine_iff.mp hxq
  have hNneq : Np ≠ Nq := by
    intro h; rw [h] at hNp; rw [hNp] at hNq; exact hne (Option.some.inj hNq)
  rcases lt_or_gt_of_ne hNneq with hlt | hgt
  · have hgood := (oracleFilterAccept_eq_true_iff.mp haccq) Np hlt
    have hbad : oracleFilterGood c σ q Np = false :=
      oracleFilterGood_eq_false_iff.mpr ⟨p, hNp, hne, Or.inl hpre⟩
    rw [hbad] at hgood; exact Bool.noConfusion hgood
  · have hgood := (oracleFilterAccept_eq_true_iff.mp haccp) Nq hgt
    have hbad : oracleFilterGood c σ p Nq = false :=
      oracleFilterGood_eq_false_iff.mpr ⟨q, hNq, fun h ↦ hne h.symm, Or.inr hpre⟩
    rw [hbad] at hgood; exact Bool.noConfusion hgood

/-- **Monotonicity in the oracle prefix.** -/
theorem oracleFilterMachine_mono (c : Code) {q σ τ x : BitString} (h : σ <+: τ)
    (hx : produces (oracleFilterMachine c) q σ x) : produces (oracleFilterMachine c) q τ x := by
  obtain ⟨N, ⟨hN, hlt⟩, hacc, hmem⟩ := mem_oracleFilterMachine_iff.mp hx
  have hNσ := oracleFilterAppears_le hN
  refine mem_oracleFilterMachine_iff.mpr ⟨N, ⟨?_, fun m hm ↦ ?_⟩, ?_, ?_⟩
  · rw [oracleFilterAppears_of_prefix c h hNσ]; exact hN
  · rw [oracleFilterAppears_of_prefix c h (hm.le.trans hNσ)]; exact hlt m hm
  · rw [oracleFilterAccept_eq_true_iff] at hacc ⊢
    intro n hn
    rw [oracleFilterGood_of_prefix c h q (hn.le.trans hNσ)]
    exact hacc n hn
  · rw [take_of_prefix h ((oracleFilterJ_le N).trans hNσ)]; exact hmem

/-! ### Completeness for oracle machines -/

/-- If `c` computes an oracle machine `W`, every `W`-computation on some oracle prefix of `A` is
reproduced by the filtered machine on a longer oracle prefix of `A`. -/
theorem oracleFilterMachine_complete {W : Map} (hW : IsOracleMachine W) {c : Code}
    (hc : ∀ q σ, (c.eval (Encodable.encode (q, σ))).map decodeGetD = W (q, σ))
    {A : Seq} {m : ℕ} {q x : BitString} (hx : produces W q (seqTake A m) x) :
    ∃ M, produces (oracleFilterMachine c) q (seqTake A M) x := by
  classical
  -- a halting `c`-computation for `(q, A↾m)`
  have hx' : x ∈ (c.eval (Encodable.encode (q, seqTake A m))).map decodeGetD := by
    rw [hc]; exact hx
  obtain ⟨v, hv, -⟩ := (Part.mem_map_iff _).mp hx'
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
  set n₀ := Nat.pair (Encodable.encode q) (Nat.pair m k) with hn₀
  have hJ : oracleFilterJ n₀ = m := by simp [oracleFilterJ, hn₀]
  have hS : oracleFilterS n₀ = k := by simp [oracleFilterS, hn₀]
  have hU1 : n₀.unpair.1 = Encodable.encode q := by simp [hn₀]
  set σ := seqTake A n₀ with hσ
  have hmn : m ≤ n₀ := hJ ▸ oracleFilterJ_le n₀
  have htake : σ.take m = seqTake A m := take_seqTake A hmn
  -- `q` appears at `n₀` under `σ`
  have happ : oracleFilterAppears c σ n₀ = some q := by
    unfold oracleFilterAppears
    rw [if_pos (by rw [hσ, length_seqTake]), hU1, Encodable.encodek]
    simp only [Option.bind, oracleFilterInner]
    rw [hJ, hS, htake, if_pos]
    exact Option.isSome_iff_exists.mpr ⟨v, Nat.Partrec.Code.evaln_mono (Nat.le_succ k) hk⟩
  -- `W` halts on `q` at the full prefix `σ`
  have hWq : produces W q σ x := hW.2 q _ _ x (by rw [← htake]; exact List.take_prefix _ _) hx
  -- appearing programs halt under `W` at `σ`
  have happW : ∀ {n q'}, oracleFilterAppears c σ n = some q' → (W (q', σ)).Dom := by
    intro n q' h
    have hd := oracleFilterAppears_eval_dom h
    obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp hd
    have hmemW : decodeGetD u ∈ W (q', σ.take (oracleFilterJ n)) := by
      rw [← hc]; exact Part.mem_map _ hu
    exact Part.dom_iff_mem.mpr ⟨_, hW.2 q' _ _ _ (List.take_prefix _ _) hmemW⟩
  have hex : ∃ n, oracleFilterAppears c σ n = some q := ⟨n₀, happ⟩
  set N := Nat.find hex
  have hN : oracleFilterAppears c σ N = some q := Nat.find_spec hex
  refine ⟨n₀, mem_oracleFilterMachine_iff.mpr ⟨N, ⟨hN, fun m' hm' ↦ Nat.find_min hex hm'⟩,
    ?_, ?_⟩⟩
  · rw [oracleFilterAccept_eq_true_iff]
    intro n _
    by_contra hbad
    rw [Bool.not_eq_true] at hbad
    obtain ⟨q', hq', hne, hcomp⟩ := oracleFilterGood_eq_false_iff.mp hbad
    have h1 : q' ∈ domainAt W σ := happW hq'
    have h2 : q ∈ domainAt W σ := Part.dom_iff_mem.mpr ⟨x, hWq⟩
    rcases hcomp with hc1 | hc2
    · exact hne (hW.1.isPrefixMachine σ h1 h2 hc1)
    · exact hne (hW.1.isPrefixMachine σ h2 h1 hc2).symm
  · -- the output of candidate `N` is `x`, by monotonicity of `W`
    have hd := oracleFilterAppears_eval_dom hN
    obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp hd
    have hmemW : decodeGetD u ∈ W (q, σ.take (oracleFilterJ N)) := by
      rw [← hc]; exact Part.mem_map _ hu
    have hmemσ : decodeGetD u ∈ W (q, σ) := hW.2 q _ _ _ (List.take_prefix _ _) hmemW
    have heq : decodeGetD u = x := Part.mem_unique hmemσ hWq
    rw [← heq]
    exact Part.mem_map _ hu

/-- **The filtered machine attains the relative complexity of an oracle machine.** -/
theorem KPrel_oracleFilterMachine_le {W : Map} (hW : IsOracleMachine W) {c : Code}
    (hc : ∀ q σ, (c.eval (Encodable.encode (q, σ))).map decodeGetD = W (q, σ))
    (A : Seq) (x : BitString) : KPrel (oracleFilterMachine c) A x ≤ KPrel W A x := by
  refine le_iInf fun m ↦ ?_
  by_cases hK : KP W x (seqTake A m) = ⊤
  · rw [hK]; exact le_top
  · obtain ⟨q, hq, hlen⟩ := exists_program_of_KP_ne_top hK
    obtain ⟨M, hM⟩ := oracleFilterMachine_complete hW hc hq
    rw [← hlen]
    exact (KPrel_le_KP _ A x M).trans (KP_le_programLength_of_produces hM)

/-! ### Uniform computability -/

theorem oracleFilter_primrec_decide_eq {α} [Primcodable α] [DecidableEq α] :
    Primrec (fun p : α × α ↦ decide (p.1 = p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.eq : PrimrecRel (@Eq α))
  exact h.of_eq (fun p ↦ by congr 1)

theorem oracleFilter_primrec_decide_le :
    Primrec (fun p : ℕ × ℕ ↦ decide (p.1 ≤ p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.nat_le : PrimrecRel (· ≤ ·))
  exact h.of_eq (fun p ↦ by congr 1)

theorem oracleFilterJ_primrec : Primrec oracleFilterJ := by
  have h := Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact h.of_eq fun _ ↦ rfl

theorem oracleFilterS_primrec : Primrec oracleFilterS := by
  have h := Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))
  exact h.of_eq fun _ ↦ rfl

theorem oracleFilterInner_uniform_primrec :
    Primrec (fun r : (Code × BitString × ℕ) × BitString ↦
      oracleFilterInner r.1.1 r.1.2.1 r.1.2.2 r.2) := by
  have hk := Primrec.succ.comp (oracleFilterS_primrec.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst (α := Code × BitString × ℕ)
      (β := BitString)))))
  have hcode := Primrec.fst.comp (Primrec.fst (α := Code × BitString × ℕ) (β := BitString))
  have htake := primrec_list_take.comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst (α := Code × BitString × ℕ)
      (β := BitString))))
    (oracleFilterJ_primrec.comp (Primrec.snd.comp (Primrec.snd.comp
      (Primrec.fst (α := Code × BitString × ℕ) (β := BitString)))))
  have hi := (Primrec.encode (α := BitString × BitString)).comp
    (Primrec.pair (Primrec.snd (α := Code × BitString × ℕ) (β := BitString)) htake)
  have hevaln := Nat.Partrec.Code.primrec_evaln.comp ((hk.pair hcode).pair hi)
  have h1 := Primrec.option_isSome.comp hevaln
  have h2 := Primrec.cond h1 (Primrec.option_some.comp
    (Primrec.snd (α := Code × BitString × ℕ) (β := BitString))) (Primrec.const none)
  exact h2.of_eq fun r ↦ by unfold oracleFilterInner; exact cond_eq_ite _ _ _

theorem oracleFilterAppears_uniform_primrec :
    Primrec (fun t : Code × BitString × ℕ ↦ oracleFilterAppears t.1 t.2.1 t.2.2) := by
  have hf := (Primrec.decode (α := BitString)).comp (Primrec.fst.comp (Primrec.unpair.comp
    (Primrec.snd.comp (Primrec.snd (α := Code) (β := BitString × ℕ)))))
  have hbind := Primrec.option_bind (β := BitString) hf oracleFilterInner_uniform_primrec.to₂
  have hguard := oracleFilter_primrec_decide_le.comp
    (Primrec.pair (Primrec.snd.comp (Primrec.snd (α := Code) (β := BitString × ℕ)))
      (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd (α := Code)
        (β := BitString × ℕ)))))
  have hc := Primrec.cond hguard hbind (Primrec.const none)
  exact hc.of_eq fun t ↦ by unfold oracleFilterAppears; exact Bool.cond_decide _ _ _

theorem oracleFilterGood_uniform_primrec :
    Primrec (fun t : Code × BitString × BitString × ℕ ↦
      oracleFilterGood t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  have hmap : Primrec (fun t : Code × BitString × BitString × ℕ ↦
      ((t.1, t.2.1, t.2.2.2) : Code × BitString × ℕ)) :=
    Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have happ : Primrec (fun t : Code × BitString × BitString × ℕ ↦
      oracleFilterAppears t.1 t.2.1 t.2.2.2) :=
    (oracleFilterAppears_uniform_primrec.comp hmap).of_eq (fun _ ↦ rfl)
  have hpair : Primrec (fun s : (Code × BitString × BitString × ℕ) × BitString ↦
      ((s.2, s.1.2.2.1) : BitString × BitString)) :=
    Primrec.snd.pair (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hgb : Primrec (fun p : BitString × BitString ↦ goodBool p.1 p.2) := goodBool_primrec
  have hg : Primrec₂ (fun (t : Code × BitString × BitString × ℕ) (q : BitString) ↦
      goodBool q t.2.2.1) := (hgb.comp hpair).of_eq (fun _ ↦ rfl)
  exact (Primrec.option_casesOn happ (Primrec.const true) hg).of_eq (fun _ ↦ rfl)

theorem oracleFilterAccept_uniform_primrec :
    Primrec (fun t : Code × BitString × BitString × ℕ ↦
      oracleFilterAccept t.1 t.2.1 t.2.2.1 t.2.2.2) := by
  unfold oracleFilterAccept
  have hf : Primrec (fun t : Code × BitString × BitString × ℕ ↦ List.range t.2.2.2) :=
    Primrec.list_range.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hmap : Primrec (fun s : (Code × BitString × BitString × ℕ) × (ℕ × Bool) ↦
      ((s.1.1, s.1.2.1, s.1.2.2.1, s.2.1) : Code × BitString × BitString × ℕ)) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
          (Primrec.fst.comp Primrec.snd)))
  have hgoodc : Primrec (fun s : (Code × BitString × BitString × ℕ) × (ℕ × Bool) ↦
      oracleFilterGood s.1.1 s.1.2.1 s.1.2.2.1 s.2.1) :=
    (oracleFilterGood_uniform_primrec.comp hmap).of_eq (fun _ ↦ rfl)
  have hh : Primrec₂ (fun (t : Code × BitString × BitString × ℕ) (bs : ℕ × Bool) ↦
      oracleFilterGood t.1 t.2.1 t.2.2.1 bs.1 && bs.2) :=
    (Primrec.and.comp hgoodc (Primrec.snd.comp Primrec.snd)).of_eq (fun _ ↦ rfl)
  exact Primrec.list_foldr hf (Primrec.const true) hh

/-- The filtered machine is uniformly partial recursive in the code and the input. -/
theorem oracleFilterMachine_uniform_partrec :
    Partrec (fun t : Code × BitString × BitString ↦ oracleFilterMachine t.1 t.2) := by
  have hcheck : Computable₂ (fun (t : Code × BitString × BitString) (n : ℕ) ↦
      decide (oracleFilterAppears t.1 t.2.2 n = some t.2.1)) := by
    have hmap : Computable (fun s : (Code × BitString × BitString) × ℕ ↦
        ((s.1.1, s.1.2.2, s.2) : Code × BitString × ℕ)) :=
      (Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)
    have happ : Computable (fun s : (Code × BitString × BitString) × ℕ ↦
        oracleFilterAppears s.1.1 s.1.2.2 s.2) :=
      ((Primrec.to_comp oracleFilterAppears_uniform_primrec).comp hmap).of_eq (fun _ ↦ rfl)
    have hsome : Computable (fun s : (Code × BitString × BitString) × ℕ ↦
        (some s.1.2.1 : Option BitString)) :=
      Computable.option_some.comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
    exact ((Primrec.to_comp oracleFilter_primrec_decide_eq).comp (happ.pair hsome)).of_eq
      (fun _ ↦ rfl)
  have hrfind : Partrec (fun t : Code × BitString × BitString ↦
      Nat.rfind (fun n ↦ Part.some (decide (oracleFilterAppears t.1 t.2.2 n = some t.2.1)))) :=
    Partrec.rfind hcheck.partrec₂
  have hbindfn : Partrec₂ (fun (t : Code × BitString × BitString) (N : ℕ) ↦
      bif oracleFilterAccept t.1 t.2.2 t.2.1 N then
        (t.1.eval (Encodable.encode (t.2.1, t.2.2.take (oracleFilterJ N)))).map decodeGetD
      else Part.none) := by
    have hacc : Computable (fun s : (Code × BitString × BitString) × ℕ ↦
        oracleFilterAccept s.1.1 s.1.2.2 s.1.2.1 s.2) := by
      have hmap : Computable (fun s : (Code × BitString × BitString) × ℕ ↦
          ((s.1.1, s.1.2.2, s.1.2.1, s.2) : Code × BitString × BitString × ℕ)) :=
        (Computable.fst.comp Computable.fst).pair
          ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair
            ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair Computable.snd))
      exact ((Primrec.to_comp oracleFilterAccept_uniform_primrec).comp hmap).of_eq
        (fun _ ↦ rfl)
    have hin : Computable (fun s : (Code × BitString × BitString) × ℕ ↦
        Encodable.encode (s.1.2.1, s.1.2.2.take (oracleFilterJ s.2))) := by
      have htake : Computable (fun s : (Code × BitString × BitString) × ℕ ↦
          s.1.2.2.take (oracleFilterJ s.2)) :=
        (primrec_list_take.to_comp.comp (Computable.snd.comp (Computable.snd.comp
          Computable.fst)) (oracleFilterJ_primrec.to_comp.comp Computable.snd))
      exact Computable.encode.comp
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair htake)
    have heval : Partrec (fun s : (Code × BitString × BitString) × ℕ ↦
        s.1.1.eval (Encodable.encode (s.1.2.1, s.1.2.2.take (oracleFilterJ s.2)))) :=
      Nat.Partrec.Code.eval_part.comp (Computable.fst.comp Computable.fst) hin
    have hmapp : Partrec (fun s : (Code × BitString × BitString) × ℕ ↦
        (s.1.1.eval (Encodable.encode (s.1.2.1, s.1.2.2.take (oracleFilterJ s.2)))).map
          decodeGetD) :=
      heval.map (decodeGetD_computable.comp Computable.snd).to₂
    exact Partrec.cond hacc hmapp Partrec.none
  exact hrfind.bind hbindfn

theorem oracleFilterMachine_isDecompressor (c : Code) :
    isDecompressor (oracleFilterMachine c) := by
  have h := oracleFilterMachine_uniform_partrec.comp
    ((Computable.const c).pair Computable.id)
  exact h

theorem oracleFilterMachine_isOracleMachine (c : Code) :
    IsOracleMachine (oracleFilterMachine c) :=
  ⟨⟨oracleFilterMachine_isDecompressor c, oracleFilterMachine_isPrefixMachine c⟩,
    fun _ _ _ _ h hx ↦ oracleFilterMachine_mono c h hx⟩

end Kolmogorov.Information.Oracle
