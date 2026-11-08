/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.Core.Invariance
import KolmogorovMathlib.Prefix.TwoStage
import KolmogorovMathlib.AlgorithmicStatistics.Selector

/-!
# Decision complexity (Gács §3.2, Definition 3.2.1, Theorem 3.2.1)

A **decision machine** is a partial recursive `T : BitString × ℕ →. Bool`. A program `p`
**decides** a string `x` on `T` if `T(p, i) = x_i` for every position `i < |x|` (positions are
`0`-indexed). The **decision complexity** `C_T(x; |x|)` (`decK T x`) is the length of a shortest
such program. For an infinite sequence `ω`, `C(ω; n)` is the decision complexity of the
prefix `ω_{0..n-1}` (`seqPrefix ω n`, Gács' Remark 3.2.2).

* `univDec`: an optimal decision machine, obtained from the repository's universal
  decompressor by reading position `i` from the context `natCode i` and keeping the first
  output bit. Its simulation property (`univDec_simulation`) gives the invariance theorem
  (`univDec_isOptimal`).
* `decK_le_plainK`: `C(x; n) ≤⁺ C(x)`.
* `condK_le_decK`: `C(x ∣ n) ≤⁺ C(x; n)` (with `n = |x|`, given as `natCode n`). The
  decompressor runs the decision program on all positions `i < n`, dovetailing with `evaln`.
* **Theorem 3.2.1** (`computable_iff_decK_bounded`): `ω` is computable iff `C(ω; n)` is
  bounded.
-/

namespace Kolmogorov.Information.Halting

open Kolmogorov
open Nat.Partrec (Code)

/-! ### Small helpers -/

/-- Unbounded search for a total Boolean predicate. -/
def rfindB (b : ℕ → Bool) : Part ℕ := Nat.rfind fun n ↦ Part.some (b n)

theorem mem_rfindB {b : ℕ → Bool} {n : ℕ} :
    n ∈ rfindB b ↔ b n = true ∧ ∀ m < n, b m = false := by
  unfold rfindB
  rw [Nat.mem_rfind]
  simp only [Part.mem_some_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1.symm, fun m hm ↦ (h2 hm).symm⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1.symm, fun hm ↦ (h2 _ hm).symm⟩

theorem rfindB_dom {b : ℕ → Bool} (h : ∃ n, b n = true) : (rfindB b).Dom := by
  obtain ⟨n, hn⟩ := h
  exact Nat.rfind_dom'.mpr ⟨n, by simpa using hn.symm, fun _ ↦ trivial⟩

theorem exists_mem_rfindB {b : ℕ → Bool} (h : ∃ n, b n = true) :
    ∃ n, n ∈ rfindB b := ⟨_, Part.get_mem (rfindB_dom h)⟩

theorem rfindB_partrec {α : Type*} [Primcodable α] {b : α → ℕ → Bool} (hb : Computable₂ b) :
    Partrec fun a ↦ rfindB (b a) :=
  Partrec.rfind hb.partrec₂

/-- Decoder of `natCode`. -/
def natOfCode (y : BitString) : ℕ := (y.takeWhile id).length

theorem natOfCode_natCode (n : ℕ) : natOfCode (natCode n) = n := by
  have := takeWhile_unaryPrefix n []
  simp only [List.append_nil] at this
  exact this

theorem natOfCode_primrec : Primrec natOfCode := by
  have h := Primrec.list_findIdx (Primrec.id (α := BitString))
    (Primrec.not.comp (Primrec.snd (α := BitString) (β := Bool))).to₂
  exact h.of_eq fun s ↦ (takeWhile_id_length_eq_findIdx s).symm

/-- The prefix `ω_0 … ω_{n-1}` of a sequence. -/
def seqPrefix (ω : ℕ → Bool) (n : ℕ) : BitString := List.ofFn fun i : Fin n ↦ ω i

@[simp] theorem length_seqPrefix (ω : ℕ → Bool) (n : ℕ) : (seqPrefix ω n).length = n := by
  simp [seqPrefix]

@[simp] theorem getElem_seqPrefix (ω : ℕ → Bool) (n i : ℕ) (h : i < (seqPrefix ω n).length) :
    (seqPrefix ω n)[i] = ω i := by
  simp [seqPrefix]

/-! ### Decision machines and decision complexity -/

/-- A **decision machine** (Gács Definition 3.2.1). -/
abbrev DecMap := BitString × ℕ →. Bool

/-- `p` decides `x` on `T`: `T(p, i) = x_i` for all `i < |x|`. -/
def Decides (T : DecMap) (p x : BitString) : Prop :=
  ∀ i (h : i < x.length), x[i] ∈ T (p, i)

/-- **Decision complexity** `C_T(x; |x|)`. -/
noncomputable def decK (T : DecMap) (x : BitString) : ENat :=
  sInf {n | ∃ p, Decides T p x ∧ (p.length : ENat) = n}

theorem decK_le_length {T : DecMap} {p x : BitString} (h : Decides T p x) :
    decK T x ≤ p.length :=
  sInf_le ⟨p, h, rfl⟩

theorem exists_decides_of_decK_le {T : DecMap} {x : BitString} {c : ℕ}
    (h : decK T x ≤ c) : ∃ p, Decides T p x ∧ p.length ≤ c := by
  have hne : {n : ENat | ∃ p, Decides T p x ∧ (p.length : ENat) = n}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    simp [decK, hemp] at h
  obtain ⟨p, hp, hlen⟩ := csInf_mem hne
  refine ⟨p, hp, ?_⟩
  have : (p.length : ENat) ≤ c := by rw [hlen]; exact h
  exact_mod_cast this

/-- An **optimal decision machine**: partial recursive and dominating every other one. -/
def IsOptimalDecision (T : DecMap) : Prop :=
  Partrec T ∧ ∀ T' : DecMap, Partrec T' → ∃ c : ℕ, ∀ x, decK T x ≤ decK T' x + c

/-! ### The universal decision machine -/

/-- The universal decision machine: run the universal decompressor on context `natCode i` and
keep the first output bit. -/
def univDec : DecMap := fun q ↦
  (universalDecompressor (q.1, natCode q.2)).map fun s ↦ s.getD 0 false

theorem univDec_partrec : Partrec univDec := by
  have h1 : Partrec fun q : BitString × ℕ ↦ universalDecompressor (q.1, natCode q.2) :=
    isDecompressorUniversalDecompressor.comp
      (Computable.pair Computable.fst (natCode_computable.comp Computable.snd))
  have h2 : Computable₂ fun (_ : BitString × ℕ) (s : BitString) ↦ s.getD 0 false :=
    ((Primrec.list_getD false).comp Primrec.snd (Primrec.const 0)).to_comp.to₂
  exact h1.map h2

/-- **Simulation.** Every decision machine `T` is simulated by `univDec` behind a fixed
prefix. -/
theorem univDec_simulation (T : DecMap) (hT : Partrec T) :
    ∃ pre : BitString, ∀ p i, univDec (pre ++ p, i) = T (p, i) := by
  set D : Map := fun pr ↦ (T (pr.1, natOfCode pr.2)).map fun b ↦ [b] with hD
  have hDc : isDecompressor D := by
    have h1 : Partrec fun pr : BitString × BitString ↦ T (pr.1, natOfCode pr.2) :=
      hT.comp (Computable.pair Computable.fst (natOfCode_primrec.to_comp.comp Computable.snd))
    have h2 : Computable₂ fun (_ : BitString × BitString) (b : Bool) ↦ [b] :=
      (Primrec.list_cons.comp Primrec.snd (Primrec.const ([] : BitString))).to_comp.to₂
    exact h1.map h2
  obtain ⟨code, hcode⟩ := existsCodeOfIsDecompressor D hDc
  refine ⟨unaryPrefix (Encodable.encode code), fun p i ↦ ?_⟩
  simp only [univDec]
  rw [universalSimulation, hcode, hD]
  simp only [natOfCode_natCode, Part.map_map, Function.comp_def]
  simp only [List.getD_cons_zero]
  exact Part.map_id' (fun _ ↦ rfl) _

theorem decides_univDec {T : DecMap} {pre : BitString}
    (hpre : ∀ p i, univDec (pre ++ p, i) = T (p, i)) {p x : BitString} (h : Decides T p x) :
    Decides univDec (pre ++ p) x := fun i hi ↦ by
  rw [hpre]; exact h i hi

/-- **Invariance theorem for decision complexity.** -/
theorem univDec_isOptimal : IsOptimalDecision univDec := by
  refine ⟨univDec_partrec, fun T hT ↦ ?_⟩
  obtain ⟨pre, hpre⟩ := univDec_simulation T hT
  refine ⟨pre.length, fun x ↦ ?_⟩
  apply sInfLeSInfAdd
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨((pre ++ p).length : ENat), ⟨pre ++ p, decides_univDec hpre hp, rfl⟩, ?_⟩
  rw [List.length_append]; push_cast; rw [add_comm]

theorem exists_isOptimalDecision : ∃ T, IsOptimalDecision T := ⟨_, univDec_isOptimal⟩

/-! ### `C(x; n) ≤⁺ C(x)` -/

/-- **`C(x; n) ≤⁺ C(x)`**, for any decompressor `U` and optimal decision machine `T₀`. -/
theorem decK_le_plainK {T₀ : DecMap} (hT₀ : IsOptimalDecision T₀) {U : Map}
    (hU : isDecompressor U) : ∃ c : ℕ, ∀ x, decK T₀ x ≤ plainK U x + c := by
  set T : DecMap := fun q ↦ (U (q.1, [])).map fun s ↦ s.getD q.2 false with hTdef
  have hT : Partrec T := by
    have h1 : Partrec fun q : BitString × ℕ ↦ U (q.1, []) :=
      hU.comp (Computable.pair Computable.fst (Computable.const []))
    have h2 : Computable₂ fun (q : BitString × ℕ) (s : BitString) ↦ s.getD q.2 false :=
      ((Primrec.list_getD false).comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to_comp.to₂
    exact h1.map h2
  obtain ⟨c, hc⟩ := hT₀.2 T hT
  refine ⟨c, fun x ↦ (hc x).trans (add_le_add ?_ le_rfl)⟩
  refine le_sInf ?_
  rintro _ ⟨p, hp, rfl⟩
  refine decK_le_length fun i hi ↦ ?_
  rw [hTdef]
  exact Part.mem_map_iff _ |>.mpr ⟨x, hp, by simp [List.getD_eq_getElem?_getD, hi]⟩

/-! ### `C(x ∣ n) ≤⁺ C(x; n)` -/

section CondLe

variable (T₀ : DecMap) (c₀ : Code)

/-- All positions `i < n` halt within fuel `s`. -/
def allHalt (s : ℕ) (p : BitString) (n : ℕ) : Bool :=
  !((List.range n).any fun i ↦ !(Code.evaln s c₀ (Encodable.encode (p, i))).isSome)

/-- Decode a Boolean answer. -/
def decodeBool (v : ℕ) : Bool := (Encodable.decode v : Option Bool).getD false

/-- The answers at fuel `s`. -/
def outList (s : ℕ) (p : BitString) (n : ℕ) : BitString :=
  (List.range n).map fun i ↦ decodeBool ((Code.evaln s c₀ (Encodable.encode (p, i))).getD 0)

/-- The decompressor reconstructing `x` from a decision program and `natCode |x|`. -/
def decToPlain : Map := fun pr ↦
  (rfindB fun s ↦ allHalt c₀ s pr.1 (natOfCode pr.2)).map fun s ↦
    outList c₀ s pr.1 (natOfCode pr.2)

theorem allHalt_primrec :
    Primrec fun q : (ℕ × BitString) × ℕ ↦ allHalt c₀ q.1.1 q.1.2 q.2 := by
  have hev : Primrec fun r : ((ℕ × BitString) × ℕ) × ℕ ↦
      !(Code.evaln r.1.1.1 c₀ (Encodable.encode (r.1.1.2, r.2))).isSome := by
    have h := Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst (α := (ℕ × BitString) × ℕ) (β := ℕ)))) (Primrec.const c₀))
      ((Primrec.encode (α := BitString × ℕ)).comp (Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)))
    exact Primrec.not.comp (Primrec.option_isSome.comp h)
  have hany := list_any_primrec (f := fun q : (ℕ × BitString) × ℕ ↦ List.range q.2)
    (Primrec.list_range.comp Primrec.snd) hev.to₂
  exact (Primrec.not.comp hany).of_eq fun _ ↦ rfl

theorem outList_primrec :
    Primrec fun q : (ℕ × BitString) × ℕ ↦ outList c₀ q.1.1 q.1.2 q.2 := by
  have hdec : Primrec decodeBool :=
    (Primrec.option_getD.comp Primrec.decode (Primrec.const false)).of_eq fun _ ↦ rfl
  have hev : Primrec fun r : ((ℕ × BitString) × ℕ) × ℕ ↦
      decodeBool ((Code.evaln r.1.1.1 c₀ (Encodable.encode (r.1.1.2, r.2))).getD 0) := by
    have h := Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp
        (Primrec.fst (α := (ℕ × BitString) × ℕ) (β := ℕ)))) (Primrec.const c₀))
      ((Primrec.encode (α := BitString × ℕ)).comp (Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)))
    exact hdec.comp (Primrec.option_getD.comp h (Primrec.const 0))
  exact (Primrec.list_map (Primrec.list_range.comp Primrec.snd) hev.to₂).of_eq fun _ ↦ rfl

theorem decToPlain_isDecompressor : isDecompressor (decToPlain c₀) := by
  have hb : Computable₂ fun (pr : BitString × BitString) (s : ℕ) ↦
      allHalt c₀ s pr.1 (natOfCode pr.2) :=
    ((allHalt_primrec c₀).comp (Primrec.pair (Primrec.pair Primrec.snd
      (Primrec.fst.comp Primrec.fst)) (natOfCode_primrec.comp
        (Primrec.snd.comp Primrec.fst)))).to_comp.to₂
  have hm : Computable₂ fun (pr : BitString × BitString) (s : ℕ) ↦
      outList c₀ s pr.1 (natOfCode pr.2) :=
    ((outList_primrec c₀).comp (Primrec.pair (Primrec.pair Primrec.snd
      (Primrec.fst.comp Primrec.fst)) (natOfCode_primrec.comp
        (Primrec.snd.comp Primrec.fst)))).to_comp.to₂
  exact (rfindB_partrec hb).map hm

variable {T₀ c₀}

theorem decToPlain_spec
    (hc : Code.eval c₀ = fun m ↦ Part.bind (Encodable.decode (α := BitString × ℕ) m)
      fun a ↦ (T₀ a).map Encodable.encode)
    {p x : BitString} (h : Decides T₀ p x) :
    x ∈ decToPlain c₀ (p, natCode x.length) := by
  have heval : ∀ i (hi : i < x.length),
      Encodable.encode x[i] ∈ Code.eval c₀ (Encodable.encode (p, i)) := fun i hi ↦ by
    rw [hc]; simp only [Encodable.encodek, Part.coe_some, Part.bind_some]
    exact Part.mem_map _ (h i hi)
  -- A common fuel for all positions.
  have hfuel : ∀ i (hi : i < x.length), ∃ k,
      Encodable.encode x[i] ∈ Code.evaln k c₀ (Encodable.encode (p, i)) := fun i hi ↦
    Nat.Partrec.Code.evaln_complete.mp (heval i hi)
  choose! k hk using hfuel
  set K := (Finset.range x.length).sup k
  have hK : ∀ i (hi : i < x.length),
      Encodable.encode x[i] ∈ Code.evaln K c₀ (Encodable.encode (p, i)) := fun i hi ↦
    Nat.Partrec.Code.evaln_mono (Finset.le_sup (f := k) (Finset.mem_range.mpr hi)) (hk i hi)
  have hall : allHalt c₀ K p x.length = true := by
    simp only [allHalt, Bool.not_eq_true', List.any_eq_false, List.mem_range,
      Bool.not_eq_false]
    intro i hi
    exact Option.isSome_iff_exists.mpr ⟨_, hK i hi⟩
  obtain ⟨s, hs⟩ := exists_mem_rfindB (b := fun s ↦ allHalt c₀ s p x.length) ⟨K, hall⟩
  have hs' := (mem_rfindB.mp hs).1
  simp only [decToPlain, natOfCode_natCode]
  refine Part.mem_map_iff _ |>.mpr ⟨s, hs, ?_⟩
  -- At fuel `s` every position halts with the right answer.
  have hpos : ∀ i (hi : i < x.length),
      Code.evaln s c₀ (Encodable.encode (p, i)) = some (Encodable.encode x[i]) := by
    intro i hi
    simp only [allHalt, Bool.not_eq_true', List.any_eq_false, List.mem_range,
      Bool.not_eq_false] at hs'
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (hs' i hi)
    have hv' := Nat.Partrec.Code.evaln_sound (show v ∈ Code.evaln s c₀ _ from hv)
    rw [hv, Part.mem_unique hv' (heval i hi)]
  apply List.ext_getElem (by simp [outList])
  intro i h1 h2
  simp only [outList, List.getElem_map, List.getElem_range]
  rw [hpos i h2]
  simp [decodeBool]

end CondLe

/-- **`C(x ∣ n) ≤⁺ C(x; n)`** (with `n = |x|` given as `natCode n`), for an optimal
decompressor `U` and any partial recursive decision machine `T₀`. -/
theorem condK_le_decK {U : Map} (hU : isOptimalConditional U) {T₀ : DecMap}
    (hT₀ : Partrec T₀) : ∃ c : ℕ, ∀ x, condK U x (natCode x.length) ≤ decK T₀ x + c := by
  obtain ⟨c₀, hc₀⟩ := Nat.Partrec.Code.exists_code.mp hT₀
  obtain ⟨c, hc⟩ := hU.2 _ (decToPlain_isDecompressor c₀)
  refine ⟨c, fun x ↦ (hc x _).trans (add_le_add ?_ le_rfl)⟩
  refine le_sInf ?_
  rintro _ ⟨p, hp, rfl⟩
  exact sInf_le ⟨p, decToPlain_spec hc₀ hp, rfl⟩

/-! ### Theorem 3.2.1 -/

/-- **Gács Theorem 3.2.1.** An infinite sequence is computable iff its decision complexity
`C(ω; n)` is bounded. -/
theorem computable_iff_decK_bounded {T₀ : DecMap} (hT₀ : IsOptimalDecision T₀)
    (ω : ℕ → Bool) : Computable ω ↔ ∃ c : ℕ, ∀ n, decK T₀ (seqPrefix ω n) ≤ c := by
  constructor
  · intro hω
    set T : DecMap := fun q ↦ Part.some (ω q.2)
    have hT : Partrec T := (hω.comp Computable.snd).partrec
    obtain ⟨c, hc⟩ := hT₀.2 T hT
    refine ⟨c, fun n ↦ (hc _).trans ?_⟩
    have : decK T (seqPrefix ω n) ≤ ([] : BitString).length :=
      decK_le_length fun i hi ↦ by simp [T]
    calc decK T (seqPrefix ω n) + c ≤ 0 + c := add_le_add (this.trans (by simp)) le_rfl
      _ = c := zero_add _
  · rintro ⟨c, hc⟩
    choose p hp hlen using fun n ↦ exists_decides_of_decK_le (hc n)
    -- Pigeonhole over the finitely many programs of length `≤ c`.
    set S : Finset BitString := (boundedPrograms c).toFinset
    have hpS : ∀ n, p n ∈ S := fun n ↦ by
      simp only [S, List.mem_toFinset, mem_boundedPrograms_iff]; exact hlen n
    obtain ⟨q, hq⟩ := Finite.exists_infinite_fiber (fun n ↦ (⟨p n, hpS n⟩ : S))
    have hinf : ((fun n ↦ (⟨p n, hpS n⟩ : S)) ⁻¹' {q}).Infinite := Set.infinite_coe_iff.mp hq
    have hall : ∀ i, ω i ∈ T₀ (q.1, i) := by
      intro i
      obtain ⟨n, hn, hin⟩ := hinf.exists_gt i
      have hpq : p n = q.1 := congrArg Subtype.val hn
      have := hp n i (by simpa using hin)
      rw [hpq] at this
      simpa using this
    have hT : Partrec fun i ↦ T₀ (q.1, i) :=
      hT₀.1.comp (Computable.pair (Computable.const q.1) Computable.id)
    exact hT.of_eq fun i ↦ (Part.eq_some_iff.mpr (hall i))

end Kolmogorov.Information.Halting
