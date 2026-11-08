/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Mathlib.Computability.TuringDegree

/-!
# Oracle computations through finite tables (a closure layer for `Nat.RecursiveIn`)

Mathlib's `Nat.RecursiveIn O` is the inductive class of partial functions computable with
oracles from `O`; it comes with constructors but no closure lemmas beyond substitution. For
a **total** oracle `g : ℕ → ℕ` the classical "use principle" description is enough for our
reductions: `f` is computable from `g` if `f n` is a partial recursive function of `n` and of
the finite table `g 0, …, g (ℓ n − 1)`, for a computable table length `ℓ`.

* `toPart g`: the total function `g` as a partial function (an oracle).
* `tableOf g m = [g 0, …, g (m − 1)]`.
* `recursiveIn_table`: `m ↦ encode (tableOf g m)` is recursive in `g` (by `prec`).
* **`recursiveIn_of_table`** (the bridge): if `f n = Φ (n, tableOf g (ℓ n))` with `Φ` partial
  recursive and `ℓ` computable, then `f` is recursive in `g`; `turingReducible_of_table` is the
  same statement for Mathlib's `≤ᵀ`.
-/

namespace Kolmogorov.Information.Turing

open Encodable

/-- A total function as an oracle. -/
def toPart (g : ℕ → ℕ) : ℕ →. ℕ := fun n ↦ Part.some (g n)

/-- The table `[g 0, …, g (m − 1)]`. -/
def tableOf (g : ℕ → ℕ) (m : ℕ) : List ℕ := (List.range m).map g

theorem tableOf_succ (g : ℕ → ℕ) (m : ℕ) : tableOf g (m + 1) = tableOf g m ++ [g m] := by
  simp [tableOf, List.range_succ]

theorem length_tableOf (g : ℕ → ℕ) (m : ℕ) : (tableOf g m).length = m := by simp [tableOf]

theorem getD_tableOf (g : ℕ → ℕ) {m i : ℕ} (h : i < m) : (tableOf g m).getD i 0 = g i := by
  simp [tableOf, List.getD_eq_getElem?_getD, h]

/-- Partial recursive functions are recursive in every oracle set. -/
theorem recursiveIn_of_partrec {O : Set (ℕ →. ℕ)} {f : ℕ →. ℕ} (hf : Partrec f) :
    Nat.RecursiveIn O f :=
  Nat.Partrec.recursiveIn (Partrec.nat_iff.mp hf)

theorem some_seq_some {α β : Type} (f : α → β) (x : α) :
    (Part.some f <*> Part.some x : Part β) = Part.some (f x) := by
  simp [Seq.seq]

theorem pair_some_some (a b : ℕ) :
    (Nat.pair <$> Part.some a <*> Part.some b : Part ℕ) = Part.some (Nat.pair a b) := by
  simp [Seq.seq]

/-- The encoded table is recursive in the oracle. -/
theorem recursiveIn_table (g : ℕ → ℕ) :
    Nat.RecursiveIn {toPart g} (fun m ↦ Part.some (encode (tableOf g m))) := by
  -- one step of the recursion: `⟨a, ⟨y, i⟩⟩ ↦ encode (decode i ++ [g y])`
  set step : ℕ → ℕ := fun w ↦
    encode (((decode (α := List ℕ) (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).2).getD []) ++
      [(Nat.unpair w).2]) with hstep
  have hstep_c : Computable step := by
    have hdec : Computable fun w : ℕ ↦
        (decode (α := List ℕ) (Nat.unpair (Nat.unpair (Nat.unpair w).1).2).2).getD [] :=
      Computable.option_getD (Computable.decode.comp ((Computable.snd.comp Computable.unpair).comp
        ((Computable.snd.comp Computable.unpair).comp (Computable.fst.comp Computable.unpair))))
        (Computable.const [])
    have happ := (Primrec.list_append (α := ℕ)).to_comp.comp hdec
      ((Primrec.list_cons.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const [])).to_comp)
    exact (Computable.encode.comp happ).of_eq fun _ ↦ rfl
  -- the oracle read: `q ↦ ⟨q, g (y q)⟩`
  have hread : Nat.RecursiveIn {toPart g}
      (fun q ↦ Nat.pair <$> Part.some q <*> toPart g (Nat.unpair (Nat.unpair q).2).1) := by
    have hy : Nat.RecursiveIn {toPart g}
        (fun q ↦ Part.some (Nat.unpair (Nat.unpair q).2).1) :=
      recursiveIn_of_partrec ((Computable.fst.comp Computable.unpair).comp
        (Computable.snd.comp Computable.unpair)).partrec
    have hgy : Nat.RecursiveIn {toPart g}
        (fun q ↦ Part.some (Nat.unpair (Nat.unpair q).2).1 >>= toPart g) :=
      Nat.RecursiveIn.comp (Nat.RecursiveIn.oracle _ (Set.mem_singleton _)) hy
    have hid : Nat.RecursiveIn {toPart g} (fun q ↦ Part.some q) :=
      recursiveIn_of_partrec Partrec.some
    refine (Nat.RecursiveIn.pair hid hgy).of_eq fun q ↦ ?_
    simp [Part.bind_some]
  have hh : Nat.RecursiveIn {toPart g}
      (fun q ↦ (Nat.pair <$> Part.some q <*> toPart g (Nat.unpair (Nat.unpair q).2).1) >>=
        fun w ↦ Part.some (step w)) :=
    Nat.RecursiveIn.comp (recursiveIn_of_partrec hstep_c.partrec) hread
  have hf : Nat.RecursiveIn {toPart g} (fun _ : ℕ ↦ Part.some (encode ([] : List ℕ))) :=
    recursiveIn_of_partrec (Computable.const _).partrec
  have hprec := Nat.RecursiveIn.prec hf hh
  have hpair : Nat.RecursiveIn {toPart g} (fun m ↦ Part.some (Nat.pair 0 m)) :=
    recursiveIn_of_partrec ((Primrec₂.natPair.comp (Primrec.const 0) Primrec.id).to_comp.partrec)
  refine (Nat.RecursiveIn.comp hprec hpair).of_eq fun m ↦ ?_
  simp only [Part.bind_eq_bind, Part.bind_some, Nat.unpair_pair]
  induction m with
  | zero => simp [tableOf]
  | succ m ih =>
    dsimp only
    rw [ih]
    simp [toPart, some_seq_some, hstep, Nat.unpair_pair, tableOf_succ]

/-- **The use principle, as a closure lemma.** If `f n = Φ (n, [g 0, …, g (ℓ n − 1)])` with `Φ`
partial recursive and `ℓ` computable, then `f` is recursive in `g`. -/
theorem recursiveIn_of_table {g : ℕ → ℕ} {f : ℕ →. ℕ} {Φ : ℕ × List ℕ →. ℕ} (hΦ : Partrec Φ)
    {ℓ : ℕ → ℕ} (hℓ : Computable ℓ) (hf : ∀ n, f n = Φ (n, tableOf g (ℓ n))) :
    Nat.RecursiveIn {toPart g} f := by
  have hT : Nat.RecursiveIn {toPart g} (fun n ↦ Part.some (ℓ n) >>=
      fun m ↦ Part.some (encode (tableOf g m))) :=
    Nat.RecursiveIn.comp (recursiveIn_table g) (recursiveIn_of_partrec hℓ.partrec)
  have hid : Nat.RecursiveIn {toPart g} (fun n ↦ Part.some n) :=
    recursiveIn_of_partrec Partrec.some
  have hP := Nat.RecursiveIn.pair hid hT
  set Φ' : ℕ →. ℕ := fun w ↦
    Φ ((Nat.unpair w).1, (decode (α := List ℕ) (Nat.unpair w).2).getD []) with hΦ'
  have hΦ'p : Partrec Φ' := by
    have hin : Computable fun w : ℕ ↦
        ((Nat.unpair w).1, (decode (α := List ℕ) (Nat.unpair w).2).getD []) :=
      Computable.pair (Computable.fst.comp Computable.unpair)
        (Computable.option_getD (Computable.decode.comp (Computable.snd.comp Computable.unpair))
          (Computable.const []))
    exact (hΦ.comp hin).of_eq fun _ ↦ rfl
  refine (Nat.RecursiveIn.comp (recursiveIn_of_partrec hΦ'p) hP).of_eq fun n ↦ ?_
  simpa [hΦ', some_seq_some] using (hf n).symm

/-- `recursiveIn_of_table` for Mathlib's Turing reducibility. -/
theorem turingReducible_of_table {g : ℕ → ℕ} {f : ℕ →. ℕ} {Φ : ℕ × List ℕ →. ℕ}
    (hΦ : Partrec Φ) {ℓ : ℕ → ℕ} (hℓ : Computable ℓ)
    (hf : ∀ n, f n = Φ (n, tableOf g (ℓ n))) : TuringReducible f (toPart g) :=
  RecursiveIn.iff_nat.mpr (recursiveIn_of_table hΦ hℓ hf)

end Kolmogorov.Information.Turing
