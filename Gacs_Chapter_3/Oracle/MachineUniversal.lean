/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Oracle.MachineFilter

/-!
# An optimal oracle machine

`oracleUniversal` is the upstream tagged union (`taggedUnion`, unary tags `natCode i`) of the
monotone prefix-filtered machines `oracleFilterMachine c` of all codes `c`
(`MachineFilter.lean`).

* It is an oracle machine (`oracleUniversal_isOracleMachine`): partial recursive (uniformity
  of the filter in the code), a prefix machine in every condition (upstream gluing lemma), and
  monotone in the condition, because the tag parse does not look at the condition.
* It is optimal (`oracleUniversal_isOptimalOracle`): an oracle machine `W` is computed by some
  code `c`; the filtered machine of `c` attains `K_W(x ∣ A)` (`KPrel_oracleFilterMachine_le`),
  and the tag `natCode (encode c)` costs `encode c + 1` bits.

Hence `exists_isOptimalOracle`. For every optimal oracle machine `V` and prefix decompressor `U`,
`K_V(x ∣ A) ≤ K_U(x) + c` (`IsOptimalOracle.KPrel_le_KP`): the oracle-ignoring machine
`(p, σ) ↦ U(p, [])` is an oracle machine. In particular `K_V(x ∣ A)` is finite
(`IsOptimalOracle.KPrel_ne_top`).
-/

namespace Kolmogorov.Information.Oracle

open Nat.Partrec (Code)
open Kolmogorov.Randomness (Seq seqTake)

/-! ### The enumerated family -/

/-- The `i`-th filtered oracle machine. -/
def oracleEnum (i : ℕ) : Map :=
  match Encodable.decode i with
  | some c => oracleFilterMachine c
  | none => fun _ ↦ Part.none

theorem oracleEnum_isOracleMachine (i : ℕ) : IsOracleMachine (oracleEnum i) := by
  unfold oracleEnum
  cases (Encodable.decode i : Option Code) with
  | none =>
    exact ⟨⟨Partrec.none, fun _ _ hp _ _ _ ↦ False.elim hp⟩,
      fun _ _ _ x _ hx ↦ False.elim (Part.notMem_none x hx)⟩
  | some c => exact oracleFilterMachine_isOracleMachine c

theorem oracleEnum_encode (c : Code) :
    oracleEnum (Encodable.encode c) = oracleFilterMachine c := by
  unfold oracleEnum; rw [Encodable.encodek]

theorem oracleEnum_eq_bind (i : ℕ) (z : BitString × BitString) :
    oracleEnum i z =
      (Part.ofOption (Encodable.decode i : Option Code)).bind
        (fun c ↦ oracleFilterMachine c z) := by
  unfold oracleEnum
  cases (Encodable.decode i : Option Code) with
  | none => simp
  | some c => simp

theorem oracleEnum_uniform_partrec :
    Partrec (fun t : ℕ × BitString × BitString ↦ oracleEnum t.1 t.2) := by
  have hrw : (fun t : ℕ × BitString × BitString ↦ oracleEnum t.1 t.2)
      = fun t ↦ (Part.ofOption (Encodable.decode t.1 : Option Code)).bind
          (fun c ↦ oracleFilterMachine c t.2) :=
    funext fun t ↦ oracleEnum_eq_bind t.1 t.2
  rw [hrw]
  apply Partrec.bind
  · exact Computable.ofOption (Computable.decode.comp Computable.fst)
  · have hmap : Computable (fun s : (ℕ × BitString × BitString) × Code ↦
        ((s.2, s.1.2) : Code × BitString × BitString)) :=
      Computable.snd.pair (Computable.snd.comp Computable.fst)
    exact (oracleFilterMachine_uniform_partrec.comp hmap).of_eq (fun _ ↦ rfl)

/-! ### The universal oracle machine -/

/-- **The universal oracle machine.** -/
def oracleUniversal : Map := taggedUnion oracleEnum

/-- A tagged union of oracle machines is monotone in the condition. -/
theorem taggedUnion_oracle_mono {M : ℕ → Map} (hM : ∀ i, IsOracleMachine (M i))
    (p σ τ x : BitString) (h : σ <+: τ) (hx : produces (taggedUnion M) p σ x) :
    produces (taggedUnion M) p τ x := by
  change x ∈ taggedUnion M (p, τ)
  change x ∈ taggedUnion M (p, σ) at hx
  unfold taggedUnion at hx ⊢
  dsimp only at hx ⊢
  split_ifs at hx ⊢ with hg
  · exact (hM _).2 _ _ _ _ h hx
  · exact hx

theorem oracleUniversal_isOracleMachine : IsOracleMachine oracleUniversal :=
  ⟨⟨taggedUnion_isDecompressor_of_uniform oracleEnum_uniform_partrec,
    taggedUnion_isPrefixMachine fun i ↦ (oracleEnum_isOracleMachine i).1.isPrefixMachine⟩,
    taggedUnion_oracle_mono oracleEnum_isOracleMachine⟩

/-- The tag costs `i + 1` bits, also relative to an oracle. -/
theorem KPrel_taggedUnion_le (M : ℕ → Map) (i : ℕ) (A : Seq) (x : BitString) :
    KPrel (taggedUnion M) A x ≤ KPrel (M i) A x + ((i + 1 : ℕ) : ENat) := by
  unfold KPrel
  rw [ENat.iInf_add]
  exact iInf_mono fun m ↦ taggedUnion_KP_le M i x (seqTake A m)

/-- **The universal oracle machine is optimal.** -/
theorem oracleUniversal_isOptimalOracle : IsOptimalOracle oracleUniversal := by
  refine ⟨oracleUniversal_isOracleMachine, fun W hW ↦ ?_⟩
  obtain ⟨c, hc⟩ := existsCodeOfIsDecompressor W hW.1.isDecompressor
  refine ⟨Encodable.encode c + 1, fun A x ↦ ?_⟩
  have h1 := KPrel_taggedUnion_le oracleEnum (Encodable.encode c) A x
  rw [oracleEnum_encode] at h1
  have h2 := KPrel_oracleFilterMachine_le hW (c := c) (fun q σ ↦ hc q σ) A x
  calc KPrel oracleUniversal A x
      ≤ KPrel (oracleFilterMachine c) A x + ((Encodable.encode c + 1 : ℕ) : ENat) := h1
    _ ≤ KPrel W A x + ((Encodable.encode c + 1 : ℕ) : ENat) := by gcongr

/-- **There is an optimal oracle machine.** -/
theorem exists_isOptimalOracle : ∃ V, IsOptimalOracle V :=
  ⟨oracleUniversal, oracleUniversal_isOptimalOracle⟩

/-! ### Comparison with unrelativized complexity -/

/-- The oracle-ignoring machine `(p, σ) ↦ U(p, [])`. -/
def ignoreOracle (U : Map) : Map := fun pr ↦ U (pr.1, [])

theorem ignoreOracle_isOracleMachine {U : Map} (hU : IsPrefixDecompressor U) :
    IsOracleMachine (ignoreOracle U) := by
  refine ⟨⟨?_, fun _ _ hp _ hq hpre ↦ hU.isPrefixMachine [] hp hq hpre⟩,
    fun _ _ _ _ _ hx ↦ hx⟩
  have h := hU.isDecompressor.comp (Computable.pair
    (Computable.fst (α := BitString) (β := BitString)) (Computable.const ([] : BitString)))
  exact h

theorem KP_ignoreOracle (U : Map) (x σ : BitString) :
    KP (ignoreOracle U) x σ = KP U x [] := by
  apply le_antisymm
  · apply sInf_le_sInf
    rintro n ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩
  · apply sInf_le_sInf
    rintro n ⟨p, hp, rfl⟩
    exact ⟨p, hp, rfl⟩

theorem KPrel_ignoreOracle (U : Map) (A : Seq) (x : BitString) :
    KPrel (ignoreOracle U) A x = KP U x [] := by
  unfold KPrel
  simp only [KP_ignoreOracle, iInf_const]

/-- **`K(x ∣ A) ≤ K(x) + c`** for an optimal oracle machine and any prefix decompressor. -/
theorem IsOptimalOracle.KPrel_le_KP {V U : Map} (hV : IsOptimalOracle V)
    (hU : IsPrefixDecompressor U) : ∃ c : ℕ, ∀ (A : Seq) (x : BitString),
      KPrel V A x ≤ KP U x [] + c := by
  obtain ⟨c, hc⟩ := hV.2 _ (ignoreOracle_isOracleMachine hU)
  exact ⟨c, fun A x ↦ by simpa [KPrel_ignoreOracle] using hc A x⟩

/-- For an optimal oracle machine, relative complexity is finite. -/
theorem IsOptimalOracle.KPrel_ne_top {V : Map} (hV : IsOptimalOracle V) (A : Seq)
    (x : BitString) : KPrel V A x ≠ ⊤ := by
  obtain ⟨U, hU⟩ := exists_isOptimalPrefixConditional
  obtain ⟨c, hc⟩ := hV.KPrel_le_KP hU.isPrefixDecompressor
  have hfin := KP_ne_top_of_optimal U hU x []
  intro htop
  have := hc A x
  rw [htop, top_le_iff] at this
  exact (WithTop.add_ne_top.mpr ⟨hfin, ENat.coe_ne_top c⟩) this

/-- For an optimal oracle machine `V` and an oracle machine `W`, the relative complexities are
comparable (the invariance theorem for relative complexity). -/
theorem IsOptimalOracle.KPrel_le {V W : Map} (hV : IsOptimalOracle V) (hW : IsOracleMachine W) :
    ∃ c : ℕ, ∀ (A : Seq) (x : BitString), KPrel V A x ≤ KPrel W A x + c :=
  hV.2 W hW

end Kolmogorov.Information.Oracle
