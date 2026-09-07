/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.ProgramCount
import KolmogorovMathlib.Prefix.Optimal
import KolmogorovMathlib.Encoding.Tuples

/-!
# The length-pairing machine `F(p) = ⟨U(p), |p|⟩`

The `≤×` half of Gács' Theorem 1.7.1 rests on one derived machine. Given a
machine `U`, the **length-pairing machine** `progLenMap U` runs `U` on its
program in the empty context and, instead of returning the output `z`, returns
the *pair* of `z` with the length of the program that produced it:

  `progLenMap U (p, _) = pairCode (U (p, [])) (natCode |p|)`.

Gács writes this as `F(p) = ⟨T(p), l(p)⟩` (proof of `thm:Hstat`, line 2060) and
observes that under coin-tossing the probability of obtaining `⟨x, n⟩` from `F`
is exactly `2^{-n} · f(x, n)`. In our terms: every length-`n` program for `x` on
`U` is a program for `pairCode x (natCode n)` on `progLenMap U`, so the
length-`n` slice `progSlice U x n` is bounded by the a priori mass of
`progLenMap U` at the pair (`progSlice_le_aprioriMeasure_progLenMap`).

The file follows the four-step template of `lenMap` (`Prefix/CountingBound`)
and `projMap` (`AlgorithmicProbability/PairProjection`):

1. define the machine;
2. characterise `produces` (`produces_progLenMap_iff`);
3. observe that the halting domain is that of `U` in the empty context
   (`domainAt_progLenMap`), so prefix-freeness is inherited for free;
4. conclude that it is a prefix decompressor whenever `U` is
   (`progLenMap_isPrefixDecompressor`).

The one difference from `lenMap` is that the pairing uses the length of the
*program* `p`, not of the *output* `z`. Computability is unaffected: the
program is the first component of the machine's input, and `List.length`,
`natCode` and `pairCode` are all primitive recursive.
-/

namespace Kolmogorov

open scoped ENNReal

/-! ### The machine -/

/-- The **length-pairing machine**: run `U` on the program `p` in the empty
context and return `pairCode z (natCode |p|)`, the output paired with the
program's own length. The context argument is ignored. -/
def progLenMap (U : Map) : Map :=
  fun pr ↦ (U (pr.1, [])).map (fun z ↦ pairCode z (natCode pr.1.length))

/-- Membership characterisation: `progLenMap U` produces `w` from `p` exactly
when `U` produces, in the empty context, some `z` whose pairing with the length
code of `p` is `w`. -/
theorem produces_progLenMap_iff (U : Map) (p y w : BitString) :
    produces (progLenMap U) p y w ↔
      ∃ z, produces U p [] z ∧ pairCode z (natCode p.length) = w := by
  change w ∈ Part.map (fun z ↦ pairCode z (natCode p.length)) (U (p, [])) ↔
    ∃ z, produces U p [] z ∧ pairCode z (natCode p.length) = w
  rw [Part.mem_map_iff]

/-- The halting domain of `progLenMap U` in any context is the halting domain of
`U` in the empty context: `Part.map` does not change definedness. -/
theorem domainAt_progLenMap (U : Map) (y : BitString) :
    domainAt (progLenMap U) y = domainAt U [] := rfl

/-- **The length-pairing machine is a prefix decompressor** whenever `U` is.
Partial recursiveness comes from `Partrec.map` with the primitive-recursive
post-processing `(pr, z) ↦ pairCode z (natCode pr.1.length)`; prefix-freeness is
inherited through `domainAt_progLenMap`. -/
theorem progLenMap_isPrefixDecompressor (U : Map) (hU : IsPrefixDecompressor U) :
    IsPrefixDecompressor (progLenMap U) := by
  refine ⟨?_, ?_⟩
  · have hf : Partrec (fun pr : BitString × BitString ↦ U (pr.1, [])) :=
      hU.isDecompressor.comp (Computable.fst.pair (Computable.const []))
    have hg : Computable₂
        (fun (pr : BitString × BitString) (z : BitString) ↦
          pairCode z (natCode pr.1.length)) :=
      (pairCode_primrec.to_comp.comp Computable.snd
        (natCode_primrec.to_comp.comp
          (Computable.list_length.comp (Computable.fst.comp Computable.fst)))).to₂
    exact (hf.map hg).of_eq (fun pr ↦ rfl)
  · intro y
    rw [domainAt_progLenMap]
    exact hU.isPrefixMachine []

/-! ### Transporting the length-`n` slice through the machine -/

/-- A length-`n` program for `x` on `U` is a program for `pairCode x (natCode n)`
on `progLenMap U`. -/
theorem produces_progLenMap_of_mem_progSet {U : Map} {x p : BitString} {n : ℕ}
    (hp : p ∈ progSet U x n) :
    produces (progLenMap U) p [] (pairCode x (natCode n)) := by
  rw [produces_progLenMap_iff]
  exact ⟨x, produces_of_mem_progSet hp, by rw [length_of_mem_progSet hp]⟩

/-- **The slice is dominated by the machine's a priori mass at the pair.** Every
summand of `progSlice U x n` reappears, with the same weight, in the `tsum`
defining `aprioriMeasure (progLenMap U) (pairCode x (natCode n)) []`; a finite
sub-sum of an `ℝ≥0∞`-valued series is at most the series. -/
theorem progSlice_le_aprioriMeasure_progLenMap (U : Map) (x : BitString) (n : ℕ) :
    progSlice U x n ≤ aprioriMeasure (progLenMap U) (pairCode x (natCode n)) [] := by
  classical
  unfold progSlice aprioriMeasure
  calc (∑ p ∈ progSet U x n, progWeight p)
      = ∑ p ∈ progSet U x n,
          (if produces (progLenMap U) p [] (pairCode x (natCode n))
            then progWeight p else 0) := by
        refine Finset.sum_congr rfl (fun p hp ↦ ?_)
        rw [if_pos (produces_progLenMap_of_mem_progSet hp)]
    _ ≤ ∑' p : BitString,
          (if produces (progLenMap U) p [] (pairCode x (natCode n))
            then progWeight p else 0) :=
        ENNReal.sum_le_tsum _

end Kolmogorov
