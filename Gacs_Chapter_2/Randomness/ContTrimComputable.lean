/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.ContTrim
import Gacs_Chapter_2.Randomness.Conservation

/-!
# Computability of the trimming construction

`bump` is a tree recursion; Mathlib's computability library has no closure lemma for it.
We evaluate it level by level on lists instead: `levelVals g x k j` holds the values of
`bump g j` on all extensions of `x` by `k − j` bits, and is a `Nat.rec` with list state
whose step is a pointwise maximum of `g` with the sums of adjacent pairs
(`bump_eq_levelVals`).

Everything here is **primitive recursive**, including the repository's enumeration
`approxEnum` of lower semicomputable functions (`approxEnum_primrec`, proved by unfolding
its irreducible definition and writing the `Finset.range` supremum as a list fold). Staying
in `Primrec` avoids the `Computable` unification timeouts met elsewhere in this project.
-/

namespace Kolmogorov.Randomness

/-! ### The enumeration is primitive recursive -/

theorem finset_range_sup_eq_foldr (n : ℕ) (g : ℕ → ℕ) :
    (Finset.range n).sup g = (List.range n).foldr (fun i acc ↦ max (g i) acc) 0 := by
  rw [Finset.sup_def, Finset.range_val]
  change ((↑(List.range n) : Multiset ℕ).map g).sup = _
  rw [Multiset.map_coe, Multiset.sup_coe, List.foldr_map]
  rfl

theorem approxEnum_primrec :
    Primrec (fun p : ℕ × ℕ × BitString × BitString ↦ approxEnum p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  -- The summand at `s'`.
  have hterm : Primrec (fun q : (ℕ × ℕ × BitString × BitString) × ℕ ↦
      match Nat.Partrec.Code.evaln q.1.2.1
          ((Encodable.decode (α := Nat.Partrec.Code) q.1.1).getD Nat.Partrec.Code.zero)
          (Encodable.encode (q.2, q.1.2.2.1, q.1.2.2.2)) with
      | some v => v * 2 ^ (q.1.2.1 - q.2)
      | none => 0) := by
    have hev : Primrec (fun q : (ℕ × ℕ × BitString × BitString) × ℕ ↦
        Nat.Partrec.Code.evaln q.1.2.1
          ((Encodable.decode (α := Nat.Partrec.Code) q.1.1).getD Nat.Partrec.Code.zero)
          (Encodable.encode (q.2, q.1.2.2.1, q.1.2.2.2))) :=
      Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.option_getD.comp (Primrec.decode.comp (Primrec.fst.comp Primrec.fst))
            (Primrec.const Nat.Partrec.Code.zero)))
        (Primrec.encode.comp (Primrec.pair Primrec.snd (Primrec.pair
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))))
    have hsome : Primrec₂ (fun (q : (ℕ × ℕ × BitString × BitString) × ℕ) (v : ℕ) ↦
        v * 2 ^ (q.1.2.1 - q.2)) :=
      (Primrec.nat_mul.comp Primrec.snd (natPow_primrec.comp (Primrec.const 2)
        (Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst)))).to₂
    exact (Primrec.option_casesOn hev (Primrec.const 0) hsome).of_eq (fun q ↦ by
      cases Nat.Partrec.Code.evaln q.1.2.1
        ((Encodable.decode (α := Nat.Partrec.Code) q.1.1).getD Nat.Partrec.Code.zero)
        (Encodable.encode (q.2, q.1.2.2.1, q.1.2.2.2)) <;> rfl)
  have hfold : Primrec (fun p : ℕ × ℕ × BitString × BitString ↦
      (List.range (p.2.1 + 1)).foldr (fun s' acc ↦ max
        (match Nat.Partrec.Code.evaln p.2.1
            ((Encodable.decode (α := Nat.Partrec.Code) p.1).getD Nat.Partrec.Code.zero)
            (Encodable.encode (s', p.2.2.1, p.2.2.2)) with
          | some v => v * 2 ^ (p.2.1 - s')
          | none => 0) acc) 0) :=
    Primrec.list_foldr (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.const 0)
      ((Primrec.nat_max.comp (hterm.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)).to₂)
  refine hfold.of_eq (fun p ↦ ?_)
  unfold approxEnum
  rw [finset_range_sup_eq_foldr]
  congr 1

theorem makeMono_approxEnum_primrec :
    Primrec (fun p : ℕ × ℕ × BitString ↦ makeMono (approxEnum p.1) p.2.1 p.2.2 []) := by
  have hstep : Primrec₂ (fun (p : ℕ × ℕ × BitString) (r : ℕ × ℕ) ↦
      max (2 * r.2) (approxEnum p.1 (r.1 + 1) p.2.2 [])) :=
    (Primrec.nat_max.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd))
      (approxEnum_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.pair
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const [])))))).to₂
  refine (Primrec.nat_rec' (f := fun p : ℕ × ℕ × BitString ↦ p.2.1)
    (g := fun p : ℕ × ℕ × BitString ↦ approxEnum p.1 0 p.2.2 [])
    (h := fun (p : ℕ × ℕ × BitString) (r : ℕ × ℕ) ↦
      max (2 * r.2) (approxEnum p.1 (r.1 + 1) p.2.2 []))
    (Primrec.fst.comp Primrec.snd)
    (approxEnum_primrec.comp (Primrec.pair Primrec.fst (Primrec.pair (Primrec.const 0)
      (Primrec.pair (Primrec.snd.comp Primrec.snd) (Primrec.const []))))) hstep).of_eq (fun p ↦ ?_)
  induction p.2.1 with
  | zero => rfl
  | succ s ih => simp only [makeMono, ← ih]

/-! ### List helpers -/

/-- Sums of adjacent pairs. -/
def pairSums (l : List ℕ) : List ℕ :=
  (List.range (l.length / 2)).map (fun j ↦ l.getD (2 * j) 0 + l.getD (2 * j + 1) 0)

/-- Pointwise maximum, indexed by the first list. -/
def zipMax (l₁ l₂ : List ℕ) : List ℕ :=
  (List.range l₁.length).map (fun j ↦ max (l₁.getD j 0) (l₂.getD j 0))

theorem getD_map_of_lt {α : Type*} (g : α → ℕ) (l : List α) (d : α) {j : ℕ} (hj : j < l.length) :
    (l.map g).getD j 0 = g (l.getD j d) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hj]
  rfl

theorem pairSums_map_extList (h : BitString → ℕ) (x : BitString) (m : ℕ) :
    pairSums ((extList x (m + 1)).map h)
      = (extList x m).map (fun y ↦ h (y ++ [false]) + h (y ++ [true])) := by
  have hE : extList x (m + 1) = (extList x m).flatMap (fun y ↦ [y ++ [false], y ++ [true]]) := rfl
  have hlen : ((extList x (m + 1)).map h).length / 2 = 2 ^ m := by
    rw [List.length_map, length_extList, pow_succ]; omega
  apply List.ext_getElem?
  intro j
  unfold pairSums
  rw [hlen, List.getElem?_map, List.getElem?_map]
  by_cases hj : j < 2 ^ m
  · have hj' : j < (extList x m).length := by rw [length_extList]; exact hj
    rw [List.getElem?_range hj, List.getElem?_eq_getElem hj']
    obtain ⟨h0, h1⟩ := getElem?_flatMap_pair (extList x m) j
    rw [List.getElem?_eq_getElem hj'] at h0 h1
    simp only [Option.map_some, List.getD_eq_getElem?_getD, List.getElem?_map, hE, h0, h1,
      Option.getD_some]
  · rw [List.getElem?_eq_none (by simp; omega),
      List.getElem?_eq_none (by rw [length_extList]; omega)]
    rfl

theorem zipMax_map_map (g h : BitString → ℕ) (l : List BitString) :
    zipMax (l.map g) (l.map h) = l.map (fun y ↦ max (g y) (h y)) := by
  apply List.ext_getElem?
  intro j
  unfold zipMax
  rw [List.length_map, List.getElem?_map, List.getElem?_map]
  by_cases hj : j < l.length
  · rw [List.getElem?_range hj, List.getElem?_eq_getElem hj, Option.map_some, Option.map_some,
      getD_map_of_lt g l [] hj, getD_map_of_lt h l [] hj, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj]
    rfl
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
    rfl

/-! ### Level-by-level evaluation -/

/-- Values of `bump g j` on the extensions of `x` by `k − j` bits. -/
def levelVals (g : BitString → ℕ) (x : BitString) (k : ℕ) : ℕ → List ℕ :=
  Nat.rec (motive := fun _ ↦ List ℕ) ((extList x k).map g)
    (fun j acc ↦ zipMax ((extList x (k - j - 1)).map g) (pairSums acc))

theorem levelVals_eq (g : BitString → ℕ) (x : BitString) (k : ℕ) :
    ∀ j ≤ k, levelVals g x k j = (extList x (k - j)).map (bump g j) := by
  intro j hj
  induction j with
  | zero =>
    change (extList x k).map g = _
    rw [Nat.sub_zero]
    exact List.map_congr_left (fun y _ ↦ rfl)
  | succ j ih =>
    change zipMax ((extList x (k - j - 1)).map g) (pairSums (levelVals g x k j)) = _
    have e : extList x (k - j) = extList x ((k - j - 1) + 1) := by congr 1; omega
    rw [ih (by omega), e, pairSums_map_extList, zipMax_map_map,
      show k - (j + 1) = k - j - 1 by omega]
    exact List.map_congr_left (fun y _ ↦ rfl)

theorem bump_eq_levelVals (g : BitString → ℕ) (x : BitString) (k : ℕ) :
    bump g k x = (levelVals g x k k).getD 0 0 := by
  rw [levelVals_eq g x k k le_rfl, Nat.sub_self]
  rfl

/-! ### Primitive recursiveness -/

theorem extList_primrec : Primrec (fun p : BitString × ℕ ↦ extList p.1 p.2) := by
  have hstep : Primrec₂ (fun (_ : BitString × ℕ) (q : ℕ × List BitString) ↦
      q.2.flatMap (fun y ↦ [y ++ [false], y ++ [true]])) :=
    (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
      ((Primrec.list_cons.comp (Primrec.list_append.comp Primrec.snd (Primrec.const [false]))
        (Primrec.list_cons.comp (Primrec.list_append.comp Primrec.snd (Primrec.const [true]))
          (Primrec.const []))).to₂)).to₂
  refine (Primrec.nat_rec' (f := fun p : BitString × ℕ ↦ p.2)
    (g := fun p : BitString × ℕ ↦ [p.1])
    (h := fun (_ : BitString × ℕ) (q : ℕ × List BitString) ↦
      q.2.flatMap (fun y ↦ [y ++ [false], y ++ [true]]))
    Primrec.snd (Primrec.list_cons.comp Primrec.fst (Primrec.const [])) hstep).of_eq (fun p ↦ ?_)
  induction p.2 with
  | zero => rfl
  | succ n ih => simp only [extList, ← ih]

theorem pairSums_primrec : Primrec pairSums := by
  unfold pairSums
  refine Primrec.list_map
    (Primrec.list_range.comp (Primrec.nat_div.comp Primrec.list_length (Primrec.const 2))) ?_
  exact (Primrec.nat_add.comp
    ((Primrec.list_getD 0).comp Primrec.fst (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd))
    ((Primrec.list_getD 0).comp Primrec.fst
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)))).to₂

theorem zipMax_primrec : Primrec (fun p : List ℕ × List ℕ ↦ zipMax p.1 p.2) := by
  unfold zipMax
  refine Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp Primrec.fst)) ?_
  exact (Primrec.nat_max.comp
    ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
    ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂

section Uniform

/-- The enumerated, monotonised approximations, as unary functions of the string. -/
def enumApprox (i s : ℕ) (x : BitString) : ℕ := makeMono (approxEnum i) s x []

theorem enumApprox_primrec : Primrec (fun p : ℕ × ℕ × BitString ↦ enumApprox p.1 p.2.1 p.2.2) :=
  makeMono_approxEnum_primrec

theorem map_enumApprox_primrec :
    Primrec (fun q : (ℕ × ℕ) × List BitString ↦ q.2.map (enumApprox q.1.1 q.1.2)) :=
  Primrec.list_map Primrec.snd
    ((enumApprox_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))).to₂)

/-- `bump (enumApprox i s) k x` is primitive recursive. -/
theorem bump_enumApprox_primrec :
    Primrec (fun q : (ℕ × ℕ) × BitString × ℕ ↦ bump (enumApprox q.1.1 q.1.2) q.2.2 q.2.1) := by
  have hinit : Primrec (fun q : (ℕ × ℕ) × BitString × ℕ ↦
      (extList q.2.1 q.2.2).map (enumApprox q.1.1 q.1.2)) :=
    map_enumApprox_primrec.comp (Primrec.pair Primrec.fst (extList_primrec.comp Primrec.snd))
  have hstep : Primrec₂ (fun (q : (ℕ × ℕ) × BitString × ℕ) (r : ℕ × List ℕ) ↦
      zipMax ((extList q.2.1 (q.2.2 - r.1 - 1)).map (enumApprox q.1.1 q.1.2)) (pairSums r.2)) :=
    (zipMax_primrec.comp (Primrec.pair
      (map_enumApprox_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (extList_primrec.comp (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.nat_sub.comp (Primrec.nat_sub.comp
            (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
            (Primrec.const 1))))))
      (pairSums_primrec.comp (Primrec.snd.comp Primrec.snd)))).to₂
  have hlev : Primrec (fun q : (ℕ × ℕ) × BitString × ℕ ↦
      levelVals (enumApprox q.1.1 q.1.2) q.2.1 q.2.2 q.2.2) :=
    (Primrec.nat_rec' (f := fun q : (ℕ × ℕ) × BitString × ℕ ↦ q.2.2)
      (g := fun q : (ℕ × ℕ) × BitString × ℕ ↦ (extList q.2.1 q.2.2).map (enumApprox q.1.1 q.1.2))
      (h := fun (q : (ℕ × ℕ) × BitString × ℕ) (r : ℕ × List ℕ) ↦
        zipMax ((extList q.2.1 (q.2.2 - r.1 - 1)).map (enumApprox q.1.1 q.1.2)) (pairSums r.2))
      (Primrec.snd.comp Primrec.snd) hinit hstep).of_eq (fun _ ↦ rfl)
  exact ((Primrec.list_getD 0).comp hlev (Primrec.const 0)).of_eq
    (fun q ↦ (bump_eq_levelVals _ _ _).symm)

/-- `stageVal (enumApprox i) s x` is primitive recursive. -/
theorem stageVal_enumApprox_primrec :
    Primrec (fun q : (ℕ × ℕ) × BitString ↦ stageVal (enumApprox q.1.1) q.1.2 q.2) := by
  have hval : Primrec (fun q : (ℕ × ℕ) × BitString ↦
      bump (enumApprox q.1.1 q.1.2) (q.1.2 - q.2.length) q.2) :=
    bump_enumApprox_primrec.comp (Primrec.pair Primrec.fst (Primrec.pair Primrec.snd
      (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd))))
  have htest : Primrec (fun q : (ℕ × ℕ) × BitString ↦ decide (q.2.length ≤ q.1.2)) :=
    natLe_primrec.comp (Primrec.pair (Primrec.list_length.comp Primrec.snd)
      (Primrec.snd.comp Primrec.fst))
  exact (Primrec.cond htest hval (Primrec.const 0)).of_eq
    (fun q ↦ (Bool.cond_decide _ _ _).trans rfl)

/-- `trimSt (enumApprox i) s x` is primitive recursive. -/
theorem trimSt_enumApprox_primrec :
    Primrec (fun q : (ℕ × ℕ) × BitString ↦ trimSt (enumApprox q.1.1) q.1.2 q.2) := by
  have hok : Primrec (fun q : ℕ × ℕ ↦ decide (rootOk (enumApprox q.1) q.2)) := by
    have hroot : Primrec (fun q : ℕ × ℕ ↦ bump (enumApprox q.1 q.2) q.2 []) :=
      bump_enumApprox_primrec.comp (Primrec.pair Primrec.id
        (Primrec.pair (Primrec.const []) Primrec.snd))
    exact natLe_primrec.comp (Primrec.pair hroot
      (natPow_primrec.comp (Primrec.const 2) Primrec.snd))
  have hinit : Primrec (fun a : ℕ × BitString ↦
      if rootOk (enumApprox a.1) 0 then stageVal (enumApprox a.1) 0 a.2 else 0) := by
    have htest : Primrec (fun a : ℕ × BitString ↦ decide (rootOk (enumApprox a.1) 0)) :=
      hok.comp (Primrec.pair Primrec.fst (Primrec.const 0))
    have hval : Primrec (fun a : ℕ × BitString ↦ stageVal (enumApprox a.1) 0 a.2) :=
      stageVal_enumApprox_primrec.comp
        (Primrec.pair (Primrec.pair Primrec.fst (Primrec.const 0)) Primrec.snd)
    exact (Primrec.cond htest hval (Primrec.const 0)).of_eq (fun _ ↦ Bool.cond_decide _ _ _)
  have hstep : Primrec₂ (fun (a : ℕ × BitString) (r : ℕ × ℕ) ↦
      if rootOk (enumApprox a.1) (r.1 + 1) then stageVal (enumApprox a.1) (r.1 + 1) a.2
      else 2 * r.2) := by
    have htest : Primrec (fun b : (ℕ × BitString) × (ℕ × ℕ) ↦
        decide (rootOk (enumApprox b.1.1) (b.2.1 + 1))) :=
      hok.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
    have hval : Primrec (fun b : (ℕ × BitString) × (ℕ × ℕ) ↦
        stageVal (enumApprox b.1.1) (b.2.1 + 1) b.1.2) :=
      stageVal_enumApprox_primrec.comp (Primrec.pair (Primrec.pair (Primrec.fst.comp Primrec.fst)
        (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.fst))
    have hold : Primrec (fun b : (ℕ × BitString) × (ℕ × ℕ) ↦ 2 * b.2.2) :=
      Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)
    exact ((Primrec.cond htest hval hold).of_eq (fun _ ↦ Bool.cond_decide _ _ _)).to₂
  have hrec : Primrec (fun q : (ℕ × ℕ) × BitString ↦
      Nat.rec (motive := fun _ ↦ ℕ)
        (if rootOk (enumApprox q.1.1) 0 then stageVal (enumApprox q.1.1) 0 q.2 else 0)
        (fun s acc ↦ if rootOk (enumApprox q.1.1) (s + 1)
          then stageVal (enumApprox q.1.1) (s + 1) q.2 else 2 * acc) q.1.2) :=
    Primrec.nat_rec' (f := fun q : (ℕ × ℕ) × BitString ↦ q.1.2)
      (g := fun q : (ℕ × ℕ) × BitString ↦
        if rootOk (enumApprox q.1.1) 0 then stageVal (enumApprox q.1.1) 0 q.2 else 0)
      (h := fun (q : (ℕ × ℕ) × BitString) (r : ℕ × ℕ) ↦
        if rootOk (enumApprox q.1.1) (r.1 + 1) then stageVal (enumApprox q.1.1) (r.1 + 1) q.2
        else 2 * r.2)
      (Primrec.snd.comp Primrec.fst)
      (hinit.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))
      ((hstep.comp (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂)
  refine hrec.of_eq (fun q ↦ ?_)
  induction q.1.2 with
  | zero => rfl
  | succ s ih => simp only [trimSt, ← ih]

end Uniform

end Kolmogorov.Randomness
