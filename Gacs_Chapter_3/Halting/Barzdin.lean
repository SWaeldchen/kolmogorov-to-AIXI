/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Halting.DecisionComplexity
import KolmogorovMathlib.DescriptionStatistics.MonotoneBound
import Gacs_Chapter_2.Randomness.LowerSemicomputable
import Mathlib.Data.Nat.Log

/-!
# Barzdin's theorem (Gács Theorem 3.2.2)

* **(a)** (`decK_le_log_of_isRE`): if `{i : ω i}` is recursively enumerable then
  `C(ω; n) ≤ log n + c`. The decision program is the number `k` of elements of the set below
  `N = 2^L − 1` written in `L = ⌊log n⌋ + 1` bits; the length `L` of the program tells the
  machine `N`. The machine enumerates the set until it has seen `k` elements below `N`, which
  then are all of them.
* **(b)** (`exists_isRE_log_le_decK`): for every partial recursive decision machine `T₀`
  (in particular an optimal one) there is a recursively enumerable set with
  `C_{T₀}(ω; n) ≥ ⌊log n⌋` for all `n`. Programs are numbered by `idx p = bin(1p)`, so that
  `2^{|p|} ≤ idx p < 2^{|p|+1}`, and `ω(idx p) = 1` iff `T₀(p, idx p) = 0`.
-/

namespace Kolmogorov.Information.Halting

open Kolmogorov
open Nat.Partrec (Code)

/-! ### Counting with a Boolean predicate -/

/-- `∑_{j < N} [b j]`, written as a fold for primitive recursiveness. -/
def countBelow (b : ℕ → Bool) (N : ℕ) : ℕ :=
  (List.range N).foldr (fun j acc ↦ (if b j then 1 else 0) + acc) 0

theorem countBelow_eq_card (b : ℕ → Bool) (N : ℕ) :
    countBelow b N = ((Finset.range N).filter fun j ↦ b j = true).card := by
  have hfold : ∀ l : List ℕ,
      l.foldr (fun j acc ↦ (if b j then 1 else 0) + acc) 0 =
        (l.map fun j ↦ if b j then 1 else 0).sum := by
    intro l; induction l with
    | nil => rfl
    | cons a l ih => simp [ih]
  rw [countBelow, hfold, Finset.card_filter, Finset.sum, Finset.range_val, Multiset.range,
    Multiset.map_coe, Multiset.sum_coe]

/-! ### Part (a) -/

section PartA

variable (c : Code)

/-- `j` has been enumerated within fuel `s`. -/
def halted (s j : ℕ) : Bool := (Code.evaln s c j).isSome

/-- The number of elements below `N` enumerated within fuel `s`. -/
def cntHalted (s N : ℕ) : ℕ := countBelow (halted c s) N

theorem halted_primrec : Primrec fun q : ℕ × ℕ ↦ halted c q.1 q.2 :=
  Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
    (Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c)) Primrec.snd))

theorem cntHalted_primrec : Primrec fun q : ℕ × ℕ ↦ cntHalted c q.1 q.2 := by
  have hh : Primrec₂ fun (q : ℕ × ℕ) (p : ℕ × ℕ) ↦ (if halted c q.1 p.1 then 1 else 0) + p.2 := by
    have h1 : Primrec fun r : (ℕ × ℕ) × (ℕ × ℕ) ↦ halted c r.1.1 r.2.1 :=
      (halted_primrec c).comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
    exact (Primrec.nat_add.comp (Primrec.ite (Primrec.eq.comp h1 (Primrec.const true))
      (Primrec.const 1) (Primrec.const 0)) (Primrec.snd.comp Primrec.snd)).to₂.of_eq
      fun r p ↦ by simp
  exact (Primrec.list_foldr (Primrec.list_range.comp Primrec.snd) (Primrec.const 0) hh).of_eq
    fun _ ↦ rfl

/-- **Barzdin's decision machine.** Program `p` of length `L` carries `k = bitsToNat p`; the
machine waits until `k` elements below `2^L − 1` have been enumerated. -/
def barzdinMachine : DecMap := fun q ↦
  (rfindB fun s ↦ decide (cntHalted c s (2 ^ q.1.length - 1) = bitsToNat q.1)).map
    fun s ↦ halted c s q.2

theorem barzdinMachine_partrec : Partrec (barzdinMachine c) := by
  have hb : Computable₂ fun (q : BitString × ℕ) (s : ℕ) ↦
      decide (cntHalted c s (2 ^ q.1.length - 1) = bitsToNat q.1) := by
    have h1 : Primrec fun r : (BitString × ℕ) × ℕ ↦ cntHalted c r.2 (2 ^ r.1.1.length - 1) :=
      (cntHalted_primrec c).comp (Primrec.pair Primrec.snd
        (Primrec.nat_sub.comp (Kolmogorov.Randomness.natPow_primrec.comp (Primrec.const 2)
          (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst))) (Primrec.const 1)))
    have h2 : Primrec fun r : (BitString × ℕ) × ℕ ↦ bitsToNat r.1.1 :=
      bitsToNat_primrec.comp (Primrec.fst.comp Primrec.fst)
    exact (PrimrecPred.decide (Primrec.eq.comp h1 h2)).to_comp.to₂
  have hm : Computable₂ fun (q : BitString × ℕ) (s : ℕ) ↦ halted c s q.2 :=
    ((halted_primrec c).comp (Primrec.pair Primrec.snd
      (Primrec.snd.comp Primrec.fst))).to_comp.to₂
  exact (rfindB_partrec hb).map hm

end PartA

/-- Pad the binary representation of `k` to `L` bits. -/
def padBits (L k : ℕ) : BitString := Nat.bits k ++ List.replicate (L - (Nat.bits k).length) false

theorem bitsToNat_padBits (L k : ℕ) : bitsToNat (padBits L k) = k := by
  rw [padBits, bitsToNat_append_replicate_false, bitsToNat_bits]

theorem length_padBits {L k : ℕ} (hk : k < 2 ^ L) : (padBits L k).length = L := by
  have : (Nat.bits k).length ≤ L := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr hk
  simp [padBits]; omega

/-- **Gács Theorem 3.2.2 (a) (Barzdin).** For the indicator `ω` of a recursively enumerable
set, `C(ω; n) ≤ log n + c`. -/
theorem decK_le_log_of_isRE {T₀ : DecMap} (hT₀ : IsOptimalDecision T₀) {ω : ℕ → Bool}
    (hω : IsRE fun i ↦ ω i = true) :
    ∃ c : ℕ, ∀ n, decK T₀ (seqPrefix ω n) ≤ Nat.log 2 n + c := by
  obtain ⟨f, hf, hdom⟩ := hω
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.mp hf
  have heval : ∀ j, Code.eval code j = (f j).map Encodable.encode := fun j ↦ by
    rw [hcode]; simp [Encodable.decode, Part.bind_some]
  -- Enumeration facts.
  have hsound : ∀ s j, halted code s j = true → ω j = true := fun s j h ↦ by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    have := Nat.Partrec.Code.evaln_sound (show v ∈ Code.evaln s code j from hv)
    rw [heval] at this
    exact (hdom j).mp (Part.dom_iff_mem.mpr ⟨_, (Part.mem_map_iff _).mp this |>.choose_spec.1⟩)
  have hcomplete : ∀ j, ω j = true → ∃ s, halted code s j = true := fun j h ↦ by
    obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp ((hdom j).mpr h)
    have : Encodable.encode u ∈ Code.eval code j := by rw [heval]; exact Part.mem_map _ hu
    obtain ⟨s, hs⟩ := Nat.Partrec.Code.evaln_complete.mp this
    exact ⟨s, Option.isSome_iff_exists.mpr ⟨_, hs⟩⟩
  have hmono : ∀ {s s'} j, s ≤ s' → halted code s j = true → halted code s' j = true :=
    fun j hss h ↦ by
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
      exact Option.isSome_iff_exists.mpr ⟨v, Nat.Partrec.Code.evaln_mono hss hv⟩
  obtain ⟨c, hc⟩ := hT₀.2 _ (barzdinMachine_partrec code)
  refine ⟨c + 1, fun n ↦ ?_⟩
  set L := Nat.log 2 n + 1
  set N := 2 ^ L - 1
  have hnN : n ≤ N := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) n
    simp only [N, L]; omega
  set E := (Finset.range N).filter fun j ↦ ω j = true
  set k := E.card
  have hkL : k < 2 ^ L := by
    have : k ≤ N := (Finset.card_filter_le _ _).trans (by simp)
    have : 0 < 2 ^ L := by positivity
    omega
  -- The halted set at fuel `s`.
  set H : ℕ → Finset ℕ := fun s ↦ (Finset.range N).filter fun j ↦ halted code s j = true
  have hHE : ∀ s, H s ⊆ E := fun s j hj ↦ by
    simp only [H, E, Finset.mem_filter] at hj ⊢; exact ⟨hj.1, hsound s j hj.2⟩
  have hcnt : ∀ s, cntHalted code s N = (H s).card := fun s ↦ countBelow_eq_card _ _
  have hex : ∃ s, decide (cntHalted code s (2 ^ (padBits L k).length - 1) =
      bitsToNat (padBits L k)) = true := by
    choose! sj hsj using fun j (hj : j ∈ E) ↦ hcomplete j (Finset.mem_filter.mp hj).2
    refine ⟨E.sup sj, ?_⟩
    rw [length_padBits hkL, bitsToNat_padBits, decide_eq_true_iff, hcnt]
    congr 1
    refine Finset.Subset.antisymm (hHE _) fun j hj ↦ ?_
    simp only [H, Finset.mem_filter]
    exact ⟨(Finset.mem_filter.mp hj).1, hmono j (Finset.le_sup hj) (hsj j hj)⟩
  obtain ⟨s, hs⟩ := exists_mem_rfindB hex
  have hs' := (mem_rfindB.mp hs).1
  rw [length_padBits hkL, bitsToNat_padBits, decide_eq_true_iff, hcnt] at hs'
  have hHs : H s = E := Finset.eq_of_subset_of_card_le (hHE s) hs'.ge
  have hdec : Decides (barzdinMachine code) (padBits L k) (seqPrefix ω n) := by
    intro i hi
    rw [length_seqPrefix] at hi
    simp only [barzdinMachine, getElem_seqPrefix]
    refine (Part.mem_map_iff _).mpr ⟨s, hs, ?_⟩
    have hiN : i < N := lt_of_lt_of_le hi hnN
    by_cases hωi : ω i = true
    · have : i ∈ H s := by rw [hHs]; exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiN, hωi⟩
      rw [hωi]; exact (Finset.mem_filter.mp this).2
    · have : i ∉ H s := by
        rw [hHs]; intro h; exact hωi (Finset.mem_filter.mp h).2
      simp only [H, Finset.mem_filter, Finset.mem_range, not_and] at this
      rw [Bool.not_eq_true] at hωi
      rw [hωi]; simpa using this hiN
  calc decK T₀ (seqPrefix ω n) ≤ decK (barzdinMachine code) (seqPrefix ω n) + c := hc _
    _ ≤ (padBits L k).length + c := add_le_add (decK_le_length hdec) le_rfl
    _ = (Nat.log 2 n : ENat) + (c + 1 : ℕ) := by
        rw [length_padBits hkL]; simp only [L]; push_cast; ring

/-! ### Part (b) -/

/-- The number `bin(1p)` of a program: `2^{|p|} ≤ idx p < 2^{|p|+1}`. -/
def idx (p : BitString) : ℕ := bitsToNat (p ++ [true])

theorem idx_cons (b : Bool) (p : BitString) :
    idx (b :: p) = 2 * idx p + (if b then 1 else 0) := rfl

theorem idx_nil : idx [] = 1 := rfl

theorem idx_bounds (p : BitString) : 2 ^ p.length ≤ idx p ∧ idx p < 2 ^ (p.length + 1) := by
  induction p with
  | nil => simp [idx_nil]
  | cons b p ih =>
    rw [idx_cons]
    simp only [List.length_cons, pow_succ]
    cases b <;> (simp; omega)

theorem idx_injective : Function.Injective idx := by
  intro p q h
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons b q =>
      have := (idx_bounds q).1; rw [idx_nil, idx_cons] at h
      have : 1 ≤ 2 ^ q.length := Nat.one_le_two_pow
      split_ifs at h <;> omega
  | cons b p ih =>
    cases q with
    | nil =>
      have := (idx_bounds p).1; rw [idx_nil, idx_cons] at h
      have : 1 ≤ 2 ^ p.length := Nat.one_le_two_pow
      split_ifs at h <;> omega
    | cons b' q =>
      rw [idx_cons, idx_cons] at h
      have hb : b = b' := by cases b <;> cases b' <;> simp at h ⊢ <;> omega
      subst hb
      have : idx p = idx q := by cases b <;> simp at h <;> omega
      rw [ih this]

theorem idx_primrec : Primrec idx :=
  bitsToNat_primrec.comp (Primrec.list_append.comp Primrec.id (Primrec.const [true]))

open Classical in
/-- The diagonal sequence: `ω(j) = 1` iff `j = idx p` and `T₀(p, j) = 0`. -/
noncomputable def diagSeq (T₀ : DecMap) (j : ℕ) : Bool :=
  decide (∃ p ∈ boundedPrograms j, idx p = j ∧ false ∈ T₀ (p, j))

theorem diagSeq_eq_true_iff {T₀ : DecMap} {j : ℕ} :
    diagSeq T₀ j = true ↔ ∃ p ∈ boundedPrograms j, idx p = j ∧ false ∈ T₀ (p, j) := by
  unfold diagSeq; simp only [decide_eq_true_eq]

theorem diagSeq_isRE {T₀ : DecMap} (hT₀ : Partrec T₀) :
    IsRE fun j ↦ diagSeq T₀ j = true := by
  have hinner : IsRE fun q : ℕ × BitString ↦ false ∈ T₀ (q.2, q.1) := by
    refine ⟨fun q ↦ (T₀ (q.2, q.1)).bind fun b ↦ Part.ofOption (if b then none else some ()),
      ?_, fun q ↦ ?_⟩
    · have h1 : Partrec fun q : ℕ × BitString ↦ T₀ (q.2, q.1) :=
        hT₀.comp (Computable.pair Computable.snd Computable.fst)
      have h2 : Computable₂ fun (_ : ℕ × BitString) (b : Bool) ↦
          (if b then none else some () : Option Unit) :=
        (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const true))
          (Primrec.const none) (Primrec.const (some ()))).to_comp.to₂
      exact h1.bind (Computable.ofOption h2)
    · constructor
      · intro h
        obtain ⟨u, hu⟩ := Part.dom_iff_mem.mp h
        obtain ⟨b, hb, hu'⟩ := Part.mem_bind_iff.mp hu
        cases b
        · exact hb
        · simp at hu'
      · intro h
        exact Part.dom_iff_mem.mpr ⟨(), Part.mem_bind_iff.mpr ⟨false, h, by simp⟩⟩
  have hR : IsRE fun q : ℕ × BitString ↦ idx q.2 = q.1 ∧ false ∈ T₀ (q.2, q.1) :=
    hinner.inter_decidable _ (PrimrecPred.decide (Primrec.eq.comp (idx_primrec.comp Primrec.snd)
      Primrec.fst)).to_comp
  refine (IsRE.existsInList (R := fun j p ↦ idx p = j ∧ false ∈ T₀ (p, j)) hR boundedPrograms
    Computable.boundedPrograms).congr fun j ↦ ?_
  rw [diagSeq_eq_true_iff]

/-- **Gács Theorem 3.2.2 (b) (Barzdin).** There is a recursively enumerable set whose
indicator has `C(ω; n) ≥ ⌊log n⌋` for all `n`, against any partial recursive (in particular
any optimal) decision machine. -/
theorem exists_isRE_log_le_decK {T₀ : DecMap} (hT₀ : Partrec T₀) :
    ∃ ω : ℕ → Bool, IsRE (fun i ↦ ω i = true) ∧
      ∀ n, (Nat.log 2 n : ENat) ≤ decK T₀ (seqPrefix ω n) := by
  refine ⟨diagSeq T₀, diagSeq_isRE hT₀, fun n ↦ le_sInf ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  have hge : n ≤ idx p := by
    by_contra hlt
    rw [not_le] at hlt
    have hmem := hp (idx p) (by simpa using hlt)
    simp only [getElem_seqPrefix] at hmem
    have hpj : p ∈ boundedPrograms (idx p) := by
      rw [mem_boundedPrograms_iff]
      exact (Nat.lt_two_pow_self).le.trans (idx_bounds p).1
    cases hω : diagSeq T₀ (idx p)
    · rw [hω] at hmem
      have : diagSeq T₀ (idx p) = true := diagSeq_eq_true_iff.mpr ⟨p, hpj, rfl, hmem⟩
      rw [hω] at this; exact Bool.noConfusion this
    · rw [hω] at hmem
      obtain ⟨p', -, hidx, hfalse⟩ := diagSeq_eq_true_iff.mp hω
      rw [idx_injective hidx] at hfalse
      exact Bool.noConfusion (Part.mem_unique hfalse hmem)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · have := Nat.log_lt_of_lt_pow (b := 2) hpos.ne' (lt_of_le_of_lt hge (idx_bounds p).2)
    exact_mod_cast Nat.lt_succ_iff.mp this

end Kolmogorov.Information.Halting
