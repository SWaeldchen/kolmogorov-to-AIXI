/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.SeqTest
import KolmogorovMathlib.Prefix.OptimalExistence
import KolmogorovMathlib.DescriptionStatistics.PrefixPrependUniversal

/-!
# Oracle machines, relative prefix complexity, exact universality (shared definitions)

Gács' Theorems 3.2.3 and 3.3.1 need two notions that the repository did not have.

## Exact universality

`IsExactUniversal U`: every prefix decompressor `M` is simulated by prepending a tag, **in both
directions**: `U(tag ++ p, y) = M(p, y)`. This is the standard notion of a universal machine
(Gács' "optimal machine `T`"). It is stronger than additive optimality
(`IsOptimalPrefixConditional`) and than the one-directional `IsPrefixPrependUniversal`; it gives
many-one completeness of the halting set. The repository's concrete
`universalPrefixMachine` is exactly universal (`universalPrefixMachine_isExactUniversal`).

## Oracle machines and `K(x ∣ A)`

An oracle `A : ℕ → Bool` is read through its finite prefixes `seqTake A m`.

* `IsOracleMachine V`: `V` is a conditional prefix decompressor whose condition is a finite
  oracle prefix, and which is **monotone in the condition**: a computation that halts on the
  oracle prefix `σ` halts with the same output on every extension `τ ⊒ σ` (it only "used" `σ`).
  Monotonicity is what rules out reading information from the *length* of the prefix.
* `KPrel V A x = inf_m K_V(x ∣ A↾m)`: the complexity of `x` relative to `A`.
* `IsOptimalOracle V`: an oracle machine that is additively optimal among oracle machines,
  uniformly in the oracle. `K(x ∣ A)` is `KPrel V A x` for a fixed optimal `V`.
-/

namespace Kolmogorov.Information.Oracle

open Kolmogorov.Randomness (Seq seqTake length_seqTake seqTake_prefix)

/-! ### Exact universality -/

/-- **Exact universality**: every prefix decompressor is simulated by a tag, in both
directions. -/
def IsExactUniversal (U : Map) : Prop :=
  IsPrefixDecompressor U ∧
    ∀ M : Map, IsPrefixDecompressor M → ∃ tag : BitString, ∀ p y, U (tag ++ p, y) = M (p, y)

theorem IsExactUniversal.isPrefixPrependUniversal {U : Map} (hU : IsExactUniversal U) :
    IsPrefixPrependUniversal U := by
  refine ⟨hU.1, fun M hM ↦ ?_⟩
  obtain ⟨tag, htag⟩ := hU.2 M hM
  exact ⟨⟨tag, fun p y x hp ↦ by change x ∈ U (tag ++ p, y); rw [htag]; exact hp⟩⟩

theorem IsExactUniversal.isOptimalPrefixConditional {U : Map} (hU : IsExactUniversal U) :
    IsOptimalPrefixConditional U :=
  hU.isPrefixPrependUniversal.isOptimalPrefixConditional

/-- **The repository's universal prefix machine is exactly universal.** -/
theorem universalPrefixMachine_isExactUniversal : IsExactUniversal universalPrefixMachine := by
  refine ⟨universalPrefixMachine_isPrefixDecompressor, fun M hM ↦ ?_⟩
  obtain ⟨i, hi⟩ := exists_enumeratedPrefixMachine_eq hM
  refine ⟨natCode i, fun q y ↦ ?_⟩
  have hlt : i < (natCode i ++ q).length := by
    simp only [List.length_append, length_natCode]; omega
  simp only [universalPrefixMachine, taggedUnion, length_takeWhile_natCode_append,
    drop_natCode_append]
  rw [if_pos hlt, hi]

theorem exists_isExactUniversal : ∃ U, IsExactUniversal U :=
  ⟨_, universalPrefixMachine_isExactUniversal⟩

/-! ### Oracle machines -/

/-- **Oracle prefix machine**: a conditional prefix decompressor, monotone in the oracle
prefix supplied as its condition. -/
def IsOracleMachine (V : Map) : Prop :=
  IsPrefixDecompressor V ∧
    ∀ (p σ τ x : BitString), σ <+: τ → produces V p σ x → produces V p τ x

/-- **`K_V(x ∣ A)`**: the complexity of `x` relative to the oracle `A`, through the machine
`V`. -/
noncomputable def KPrel (V : Map) (A : Seq) (x : BitString) : ENat :=
  ⨅ m, KP V x (seqTake A m)

/-- **An optimal oracle machine**: additively optimal among oracle machines, uniformly in the
oracle. -/
def IsOptimalOracle (V : Map) : Prop :=
  IsOracleMachine V ∧
    ∀ W : Map, IsOracleMachine W → ∃ c : ℕ, ∀ (A : Seq) (x : BitString),
      KPrel V A x ≤ KPrel W A x + c

theorem KPrel_le_KP (V : Map) (A : Seq) (x : BitString) (m : ℕ) :
    KPrel V A x ≤ KP V x (seqTake A m) :=
  iInf_le (fun m ↦ KP V x (seqTake A m)) m

/-- For an oracle machine, `K_V(x ∣ A↾m)` is antitone in `m`. -/
theorem IsOracleMachine.KP_antitone {V : Map} (hV : IsOracleMachine V) (A : Seq)
    (x : BitString) {m m' : ℕ} (h : m ≤ m') :
    KP V x (seqTake A m') ≤ KP V x (seqTake A m) := by
  apply sInf_le_sInf
  rintro n ⟨p, hp, rfl⟩
  exact ⟨p, hV.2 p _ _ x (seqTake_prefix h) hp, rfl⟩

end Kolmogorov.Information.Oracle
