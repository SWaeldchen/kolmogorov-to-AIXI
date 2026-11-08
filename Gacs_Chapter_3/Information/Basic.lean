/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_2.Randomness.Descriptions
import KolmogorovMathlib.Prefix.ConditionalSymmetry
import KolmogorovMathlib.DescriptionStatistics.ShortestDescriptions
import KolmogorovMathlib.DescriptionStatistics.FuelComplexity
import KolmogorovMathlib.AlgorithmicStatistics.NormalizedCodedFiniteDistribution

/-!
# Algorithmic information: the basic toolkit (Gács §3.1.1)

For an optimal prefix machine `U` every conditional complexity is finite, so we work with
natural numbers:

* `Kc U x y = K(x ∣ y)`, `Ku U x = K(x)`, and `xk U x = ⟨x, K(x)⟩` (the pair code of `x` and
  the unary code of `K(x)`, the context the upstream addition theorem uses).
* `AddLE f g` / `AddEq f g`: `f ≤ g` / `f = g` up to an additive constant (Gács' `≤⁺`, `=⁺`),
  for integer-valued functions of a parameter.

Toolkit (each "`∃ c, ∀ …`"):

* transport: `Kc_map` (computable map of the object), `Kc_cond_map` (more information in
  the condition), `Kc_le_Ku`, `Kc_self`;
* `Ku_le_add_Kc`: `K(v) ≤ K(u) + K(v ∣ u) + c`;
* `Kc_triangle`: `K(z ∣ x) ≤ K(y ∣ x) + K(z ∣ y) + c`;
* **Theorem 3.1.4 (addition)** `addition`: `K(x, y) =⁺ K(x) + K(y ∣ x, K(x))`, and
  **Theorem 3.1.7** `condAddition`: `K(x, y ∣ z) =⁺ K(x ∣ z) + K(y ∣ z, x, K(x ∣ z))` —
  both assembled from the upstream `KPPair_chain_*`, `KPCondPair_chain_*`;
* `condCoding_trim`: the conditional coding theorem for an arbitrary jointly lower
  semicomputable `f`, at every condition where `f(·, ctx)` is a semimeasure;
* **`x*`** (`xStar`), a shortest description of `x`, and `xStar_equiv`:
  `K(⟨x, K(x)⟩ ∣ x*) ≤ c` and `K(x* ∣ ⟨x, K(x)⟩) ≤ c`, i.e. `x* ≍ ⟨x, K(x)⟩`. The second bound
  uses Corollary 1.7.1 (boundedly many shortest descriptions) through `condCoding_trim`
  applied to the uniform distribution on the shortest descriptions.
-/

namespace Kolmogorov.Information

open scoped ENNReal
open Kolmogorov.Randomness (fuelHalts fuelHalts_primrec fuelHalts_mono fuelHalts_sound
  fuelHalts_complete dyadicValue_two_pow_sub natPow_primrec dyadicValue_zero)

/-! ### Additive comparisons -/

/-- `f ≤⁺ g`: `f ≤ g` up to an additive constant. -/
def AddLE {ι : Type*} (f g : ι → ℤ) : Prop := ∃ c : ℕ, ∀ i, f i ≤ g i + c

/-- `f =⁺ g`: equality up to an additive constant. -/
def AddEq {ι : Type*} (f g : ι → ℤ) : Prop := AddLE f g ∧ AddLE g f

section Add

variable {ι κ : Type*} {f g h : ι → ℤ}

theorem AddLE.of_le (hfg : ∀ i, f i ≤ g i) : AddLE f g := ⟨0, fun i ↦ by simpa using hfg i⟩

theorem AddLE.refl (f : ι → ℤ) : AddLE f f := AddLE.of_le fun _ ↦ le_rfl

theorem AddLE.trans (h₁ : AddLE f g) (h₂ : AddLE g h) : AddLE f h := by
  obtain ⟨c₁, h₁⟩ := h₁; obtain ⟨c₂, h₂⟩ := h₂
  exact ⟨c₁ + c₂, fun i ↦ by have := h₁ i; have := h₂ i; push_cast; omega⟩

theorem AddLE.comp (hfg : AddLE f g) (φ : κ → ι) : AddLE (fun k ↦ f (φ k)) (fun k ↦ g (φ k)) := by
  obtain ⟨c, hc⟩ := hfg; exact ⟨c, fun k ↦ hc (φ k)⟩

theorem AddEq.symm (hfg : AddEq f g) : AddEq g f := ⟨hfg.2, hfg.1⟩

theorem AddEq.trans (h₁ : AddEq f g) (h₂ : AddEq g h) : AddEq f h :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem AddEq.comp (hfg : AddEq f g) (φ : κ → ι) : AddEq (fun k ↦ f (φ k)) (fun k ↦ g (φ k)) :=
  ⟨hfg.1.comp φ, hfg.2.comp φ⟩

end Add

/-! ### Complexities as natural numbers -/

variable (U : Map)

/-- `K(x ∣ y)` as a natural number. -/
noncomputable def Kc (x y : BitString) : ℕ := (KP U x y).toNat

/-- `K(x)` as a natural number. -/
noncomputable def Ku (x : BitString) : ℕ := Kc U x []

/-- `⟨x, K(x)⟩`, in the encoding of the upstream addition theorem. -/
noncomputable def xk (x : BitString) : BitString := pairCode x (natCode (Ku U x))

variable {U}

theorem KP_eq_Kc (hU : IsOptimalPrefixConditional U) (x y : BitString) :
    KP U x y = (Kc U x y : ENat) := (ENat.coe_toNat (KP_ne_top_of_optimal U hU x y)).symm

theorem KPPlain_eq_Ku (hU : IsOptimalPrefixConditional U) (x : BitString) :
    KPPlain U x = (Ku U x : ENat) := KP_eq_Kc hU x []

theorem complexityWeight_KP (hU : IsOptimalPrefixConditional U) (x y : BitString) :
    complexityWeight (KP U x y) = 2⁻¹ ^ Kc U x y := by
  rw [KP_eq_Kc hU, complexityWeight_coe]

/-- From `2^{-m} ≤ 2^{-k}` to `k ≤ m`. -/
theorem le_of_inv_two_pow_le {m k : ℕ} (h : (2 : ℝ≥0∞)⁻¹ ^ m ≤ 2⁻¹ ^ k) : k ≤ m := by
  rw [← ENNReal.inv_pow, ← ENNReal.inv_pow, ENNReal.inv_le_inv] at h
  have hcast : ∀ j : ℕ, (2 : ℝ≥0∞) ^ j = ((2 ^ j : ℕ) : ℝ≥0∞) := fun j ↦ by push_cast; rfl
  rw [hcast, hcast, Nat.cast_le] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h

/-! ### Transport lemmas -/

/-- Computable maps of the object cost a constant: `K(g x ∣ y) ≤ K(x ∣ y) + c`. -/
theorem Kc_map (hU : IsOptimalPrefixConditional U) {g : BitString → BitString}
    (hg : Computable g) : ∃ c : ℕ, ∀ x y, Kc U (g x) y ≤ Kc U x y + c := by
  obtain ⟨c, hc⟩ := KP_cond_first_map_le U hU (fun _ x ↦ g x) (hg.comp Computable.snd)
  refine ⟨c, fun x y ↦ ?_⟩
  have h := hc x y
  rw [KP_eq_Kc hU, KP_eq_Kc hU] at h
  exact_mod_cast h

/-- Partial computable maps, possibly reading the condition. -/
theorem Kc_map_partrec (hU : IsOptimalPrefixConditional U)
    (f : BitString → BitString →. BitString)
    (hf : Partrec (fun p : BitString × BitString ↦ f p.2 p.1)) :
    ∃ c : ℕ, ∀ x w y, w ∈ f y x → Kc U w y ≤ Kc U x y + c := by
  obtain ⟨c, hc⟩ := KP_partrec_cond_first_map_le U hU f hf
  refine ⟨c, fun x w y hw ↦ ?_⟩
  have h := hc x w y hw
  rw [KP_eq_Kc hU, KP_eq_Kc hU] at h
  exact_mod_cast h

/-- More information in the condition does not hurt: `K(x ∣ y) ≤ K(x ∣ g y) + c`. -/
theorem Kc_cond_map (hU : IsOptimalPrefixConditional U) {g : BitString → BitString}
    (hg : Computable g) : ∃ c : ℕ, ∀ x y, Kc U x y ≤ Kc U x (g y) + c := by
  obtain ⟨c, hc⟩ := KP_cond_map_le U hU g hg
  refine ⟨c, fun x y ↦ ?_⟩
  have h := hc x y
  rw [KP_eq_Kc hU, KP_eq_Kc hU] at h
  exact_mod_cast h

/-- `K(x ∣ y) ≤ K(x) + c`. -/
theorem Kc_le_Ku (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, Kc U x y ≤ Ku U x + c := by
  obtain ⟨c, hc⟩ := KP_le_KPPlain U hU
  refine ⟨c, fun x y ↦ ?_⟩
  have h := hc x y
  rw [KP_eq_Kc hU, KPPlain_eq_Ku hU] at h
  exact_mod_cast h

/-- `K(x ∣ x) ≤ c`. -/
theorem Kc_self (hU : IsOptimalPrefixConditional U) : ∃ c : ℕ, ∀ x, Kc U x x ≤ c := by
  obtain ⟨c, hc⟩ := KP_self_le U hU
  refine ⟨c, fun x ↦ ?_⟩
  have h := hc x
  rw [KP_eq_Kc hU] at h
  exact_mod_cast h

/-- `K(⟨u, v⟩) ≤ K(u) + K(v ∣ u) + c`. -/
theorem Ku_pair_le (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ u v, Ku U (pairCode u v) ≤ Ku U u + Kc U v u + c := by
  obtain ⟨c, hc⟩ := KPPair_le_KPPlain_add_KP U hU
  refine ⟨c, fun u v ↦ ?_⟩
  have h := hc u v
  unfold KPPair at h
  rw [KP_eq_Kc hU, KPPlain_eq_Ku hU, KP_eq_Kc hU] at h
  exact_mod_cast h

/-- `K(v) ≤ K(u) + K(v ∣ u) + c`. -/
theorem Ku_le_add_Kc (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ u v, Ku U v ≤ Ku U u + Kc U v u + c := by
  obtain ⟨c₁, h₁⟩ := Ku_pair_le hU
  obtain ⟨c₂, h₂⟩ := Kc_map hU decodeSecond_computable
  refine ⟨c₁ + c₂, fun u v ↦ ?_⟩
  have a := h₁ u v
  have b := h₂ (pairCode u v) []
  rw [decodeSecond_pairCode] at b
  unfold Ku at a ⊢
  omega

/-! ### The addition theorems (Gács Theorems 3.1.4 and 3.1.7) -/

/-- **Gács Theorem 3.1.4 (addition).** `K(x, y) =⁺ K(x) + K(y ∣ x, K(x))`. -/
theorem addition (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, Ku U (pairCode x y) ≤ Ku U x + Kc U y (xk U x) + c ∧
      Ku U x + Kc U y (xk U x) ≤ Ku U (pairCode x y) + c := by
  obtain ⟨c₁, h₁⟩ := KPPair_chain_upper U hU
  obtain ⟨c₂, h₂⟩ := KPPair_chain_lower U hU
  refine ⟨c₁ + c₂, fun x y ↦ ?_⟩
  have hk : HasPrefixComplexityValue U x (Ku U x) := (KPPlain_eq_Ku hU x).symm
  have a := h₁ x y (Ku U x) hk
  have b := h₂ x y (Ku U x) hk
  unfold KPPair at a b
  rw [prefixComplexityContext_eq_pairCode] at a b
  rw [KP_eq_Kc hU, KPPlain_eq_Ku hU, KP_eq_Kc hU] at a
  rw [KP_eq_Kc hU, KPPlain_eq_Ku hU, KP_eq_Kc hU] at b
  have a' : Kc U (pairCode x y) [] ≤ Ku U x + Kc U y (pairCode x (natCode (Ku U x))) + c₁ := by
    exact_mod_cast a
  have b' : Ku U x + Kc U y (pairCode x (natCode (Ku U x))) ≤ Kc U (pairCode x y) [] + c₂ := by
    exact_mod_cast b
  unfold xk Ku at *
  constructor <;> omega

/-- The context `⟨z, x, K(x ∣ z)⟩` of the conditional addition theorem. -/
noncomputable def condCtx (U : Map) (z x : BitString) : BitString :=
  prefixCondComplexityContext z x (Kc U x z)

/-- **Gács Theorem 3.1.7 (conditional addition).**
`K(x, y ∣ z) =⁺ K(x ∣ z) + K(y ∣ z, x, K(x ∣ z))`. -/
theorem condAddition (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y z, Kc U (pairCode x y) z ≤ Kc U x z + Kc U y (condCtx U z x) + c ∧
      Kc U x z + Kc U y (condCtx U z x) ≤ Kc U (pairCode x y) z + c := by
  obtain ⟨c₁, h₁⟩ := KPCondPair_chain_upper U hU
  obtain ⟨c₂, h₂⟩ := KPCondPair_chain_lower U hU
  refine ⟨c₁ + c₂, fun x y z ↦ ?_⟩
  have hk : HasCondPrefixComplexityValue U x z (Kc U x z) := (KP_eq_Kc hU x z).symm
  have a := h₁ x y z (Kc U x z) hk
  have b := h₂ x y z (Kc U x z) hk
  unfold KPCondPair at a b
  rw [KP_eq_Kc hU, KP_eq_Kc hU, KP_eq_Kc hU] at a b
  have a' : Kc U (pairCode x y) z ≤ Kc U x z + Kc U y (condCtx U z x) + c₁ := by
    unfold condCtx; exact_mod_cast a
  have b' : Kc U x z + Kc U y (condCtx U z x) ≤ Kc U (pairCode x y) z + c₂ := by
    unfold condCtx; exact_mod_cast b
  constructor <;> omega

/-- `K(z ∣ x) ≤ K(y ∣ x) + K(z ∣ y) + c` (the triangle inequality behind Theorem 3.1.8). -/
theorem Kc_triangle (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y z, Kc U z x ≤ Kc U y x + Kc U z y + c := by
  obtain ⟨c₁, h₁⟩ := condAddition hU
  -- the middle component of `⟨x, y, k⟩` is `y`
  have hg : Computable (fun w : BitString ↦ decodeFirst (decodeSecond w)) :=
    decodeFirst_computable.comp decodeSecond_computable
  obtain ⟨c₂, h₂⟩ := Kc_cond_map hU hg
  obtain ⟨c₃, h₃⟩ := Kc_map hU decodeSecond_computable
  refine ⟨c₁ + c₂ + c₃, fun x y z ↦ ?_⟩
  have a := (h₁ y z x).1
  have b := h₂ z (condCtx U x y)
  have hdec : decodeFirst (decodeSecond (condCtx U x y)) = y := by
    simp [condCtx, prefixCondComplexityContext, decodeFirst_pairCode, decodeSecond_pairCode]
  rw [hdec] at b
  have d := h₃ (pairCode y z) x
  rw [decodeSecond_pairCode] at d
  omega

/-! ### The conditional coding theorem with trimming -/

/-- **Conditional coding theorem**, for an arbitrary jointly lower semicomputable `f`, at every
condition at which `f(·, ctx)` is a semimeasure. -/
theorem condCoding_trim (hU : IsOptimalPrefixConditional U) {f : BitString → BitString → ℝ≥0∞}
    (hf : IsLSC f) : ∃ c : ℕ, ∀ ctx, (∑' x, f x ctx ≤ 1) →
      ∀ x, 2⁻¹ ^ c * f x ctx ≤ complexityWeight (KP U x ctx) := by
  obtain ⟨a, hmono, hsup, hcomp⟩ := hf
  have hT : IsLSC (truncG a 0) := ⟨truncGapprox a 0,
    fun S out ctx ↦ truncGapprox_mono 0 S out ctx, fun _ _ ↦ rfl, truncGapprox_computable hcomp 0⟩
  obtain ⟨M, hM, c₀, hreal⟩ := kraftChaitin_realization_bound hT 0 (fun ctx ↦ tsum_truncG_le 0 ctx)
  obtain ⟨c, hc⟩ := complexityWeight_dominates_of_prefix_realization hU hM hreal
  refine ⟨c, fun ctx hctx x ↦ ?_⟩
  rw [← truncG_eq_f_of_le hmono hsup 0 ctx (by simpa using hctx) x]
  exact hc x ctx

/-! ### Indicators of r.e. relations are lower semicomputable -/

open Classical in
/-- `2^{-a}` on an r.e. relation, `0` off it. -/
noncomputable def reInd (R : BitString → BitString → Prop) (a : ℕ) (x ctx : BitString) :
    ℝ≥0∞ :=
  if R x ctx then 2⁻¹ ^ a else 0

theorem reInd_isLSC {R : BitString → BitString → Prop}
    (hR : IsRE (fun q : BitString × BitString ↦ R q.1 q.2)) (a : ℕ) : IsLSC (reInd R a) := by
  classical
  obtain ⟨f, hf, hdom⟩ := hR
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨fun s x ctx ↦ if fuelHalts c s (x, ctx) = true ∧ a ≤ s then 2 ^ (s - a) else 0,
    fun s x ctx ↦ ?_, fun x ctx ↦ ?_, ?_⟩
  · dsimp only
    by_cases h : fuelHalts c s (x, ctx) = true ∧ a ≤ s
    · have h' : fuelHalts c (s + 1) (x, ctx) = true ∧ a ≤ s + 1 :=
        ⟨fuelHalts_mono c (Nat.le_succ s) h.1, by omega⟩
      rw [if_pos h, if_pos h', dyadicValue_two_pow_sub h.2, dyadicValue_two_pow_sub h'.2]
    · rw [if_neg h, dyadicValue_zero]; exact zero_le
  · dsimp only
    unfold reInd
    by_cases hRx : R x ctx
    · rw [if_pos hRx]
      obtain ⟨k, hk⟩ := fuelHalts_complete hc ((hdom (x, ctx)).mpr hRx)
      apply le_antisymm
      · refine iSup_le fun s ↦ ?_
        split_ifs with h
        · rw [dyadicValue_two_pow_sub h.2]
        · rw [dyadicValue_zero]; exact zero_le
      · refine le_iSup_of_le (max k a) ?_
        rw [if_pos ⟨fuelHalts_mono c (le_max_left _ _) hk, le_max_right _ _⟩,
          dyadicValue_two_pow_sub (le_max_right _ _)]
    · rw [if_neg hRx]
      refine le_antisymm (iSup_le fun s ↦ ?_) zero_le
      rw [if_neg (fun h ↦ hRx ((hdom (x, ctx)).mp (fuelHalts_sound hc h.1))), dyadicValue_zero]
  · have h1 : Primrec (fun p : ℕ × BitString × BitString ↦ fuelHalts c p.1 (p.2.1, p.2.2)) :=
      (fuelHalts_primrec c).comp (Primrec.pair Primrec.fst
        (Primrec.pair (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)))
    have h2 : Primrec (fun p : ℕ × BitString × BitString ↦ decide (a ≤ p.1)) :=
      Kolmogorov.Randomness.natLe_primrec.comp (Primrec.pair (Primrec.const a) Primrec.fst)
    have h3 := Primrec.cond (Primrec.and.comp h1 h2)
      (natPow_primrec.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.fst (Primrec.const a)))
      (Primrec.const 0)
    refine h3.to_comp.of_eq fun p ↦ ?_
    rcases Bool.eq_false_or_eq_true (fuelHalts c p.1 (p.2.1, p.2.2)) with h | h <;>
      by_cases ha : a ≤ p.1 <;> simp [h, ha]

/-! ### `x*` and `x* ≍ ⟨x, K(x)⟩` -/

variable (U) in
open Classical in
/-- **`x*`**: a shortest description of `x` (Gács: "the first shortest description"; any
choice works below). -/
noncomputable def xStar (x : BitString) : BitString :=
  if h : ∃ p, produces U p [] x ∧ p.length = Ku U x then h.choose else []

theorem xStar_spec (hU : IsOptimalPrefixConditional U) (x : BitString) :
    produces U (xStar U x) [] x ∧ (xStar U x).length = Ku U x := by
  have hex : ∃ p, produces U p [] x ∧ p.length = Ku U x := by
    obtain ⟨p, hp, hlen⟩ := exists_program_of_KP_ne_top (KP_ne_top_of_optimal U hU x [])
    refine ⟨p, hp, ?_⟩
    rw [KP_eq_Kc hU] at hlen
    exact_mod_cast hlen
  unfold xStar
  rw [dif_pos hex]
  exact hex.choose_spec

/-- `K(⟨x, K(x)⟩ ∣ x*) ≤ c`: `x` and `K(x)` are read off `x*`. -/
theorem xk_le_xStar (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, Kc U (xk U x) (xStar U x) ≤ c := by
  have hU' : Partrec (fun p : BitString × BitString ↦ U (p.1, ([] : BitString))) :=
    hU.isDecompressor.comp (Computable.pair Computable.fst (Computable.const []))
  have hg : Computable (fun q : (BitString × BitString) × BitString ↦
      pairCode q.2 (natCode q.1.1.length)) := by
    have h := pairCode_computable.comp (Computable.pair Computable.snd
      (natCode_computable.comp (Computable.list_length.comp
        (Computable.fst.comp (Computable.fst (α := BitString × BitString) (β := BitString))))))
    exact h.of_eq fun _ ↦ rfl
  have hf := Partrec.map hU' hg.to₂
  obtain ⟨c₁, h₁⟩ := Kc_map_partrec hU
    (fun _ q ↦ (U (q, [])).map (fun out ↦ pairCode out (natCode q.length))) hf
  obtain ⟨c₂, h₂⟩ := Kc_self hU
  refine ⟨c₂ + c₁, fun x ↦ ?_⟩
  have hmem : xk U x ∈ (fun (_ q : BitString) ↦
      (U (q, [])).map (fun out ↦ pairCode out (natCode q.length))) (xStar U x) (xStar U x) := by
    obtain ⟨hp, hlen⟩ := xStar_spec hU x
    exact (Part.mem_map_iff _).mpr ⟨x, hp, by rw [hlen]; rfl⟩
  have := h₁ (xStar U x) (xk U x) (xStar U x) hmem
  have := h₂ (xStar U x)
  omega

/-- Decoder of the unary number code `natCode`. -/
def decNat (z : BitString) : ℕ := (z.takeWhile id).length

@[simp] theorem decNat_natCode (n : ℕ) : decNat (natCode n) = n := by
  simp [decNat, natCode]

theorem decNat_primrec : Primrec decNat :=
  (Primrec.list_findIdx Primrec.id (Primrec.not.comp Primrec.snd).to₂).of_eq
    (fun z ↦ (takeWhile_id_length_eq_findIdx z).symm)

/-- The relation "`p` is a description of length `k` of `x`", read off a context `⟨x, k⟩`. -/
def ShortDesc (U : Map) (p ctx : BitString) : Prop :=
  p.length = decNat (decodeSecond ctx) ∧ produces U p [] (decodeFirst ctx)

theorem shortDesc_isRE (hU : IsOptimalPrefixConditional U) :
    IsRE (fun q : BitString × BitString ↦ ShortDesc U q.1 q.2) := by
  have hprod : IsRE (fun q : BitString × BitString ↦ produces U q.1 [] (decodeFirst q.2)) :=
    (producesIsRe U hU.isDecompressor).comp
      (g := fun q : BitString × BitString ↦ ((decodeFirst q.2, ([] : BitString), 0), q.1))
      (Computable.pair (Computable.pair (decodeFirst_computable.comp Computable.snd)
        (Computable.pair (Computable.const []) (Computable.const 0))) Computable.fst)
  have hdec : Computable (fun q : BitString × BitString ↦ decNat (decodeSecond q.2)) :=
    decNat_primrec.to_comp.comp (decodeSecond_computable.comp Computable.snd)
  have heq : Computable (fun q : BitString × BitString ↦
      decide (q.1.length = decNat (decodeSecond q.2))) :=
    natEq_primrec.to_comp.comp (Computable.pair (Computable.list_length.comp Computable.fst) hdec)
  exact (hprod.inter_decidable _ heq).congr fun q ↦ Iff.rfl

/-- `K(x* ∣ ⟨x, K(x)⟩) ≤ c`: there are boundedly many shortest descriptions (Cor. 1.7.1). -/
theorem xStar_le_xk (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, Kc U (xStar U x) (xk U x) ≤ c := by
  classical
  obtain ⟨C, hC⟩ := progCount_shortest_le U hU
  obtain ⟨c, hc⟩ := condCoding_trim hU (reInd_isLSC (shortDesc_isRE hU) C)
  have hR : ∀ x p, ShortDesc U p (xk U x) ↔ p ∈ progSet U x (Ku U x) := fun x p ↦ by
    rw [mem_progSet]
    simp [ShortDesc, xk, decodeFirst_pairCode, decodeSecond_pairCode]
  have hsum : ∀ x, ∑' p, reInd (ShortDesc U) C p (xk U x) ≤ 1 := fun x ↦ by
    have hzero : ∀ p ∉ progSet U x (Ku U x), reInd (ShortDesc U) C p (xk U x) = 0 :=
      fun p hp ↦ by rw [reInd, if_neg (fun h ↦ hp ((hR x p).mp h))]
    rw [tsum_eq_sum hzero]
    calc ∑ p ∈ progSet U x (Ku U x), reInd (ShortDesc U) C p (xk U x)
        = ∑ _p ∈ progSet U x (Ku U x), (2 : ℝ≥0∞)⁻¹ ^ C :=
          Finset.sum_congr rfl fun p hp ↦ by rw [reInd, if_pos ((hR x p).mpr hp)]
      _ = (progCount U x (Ku U x) : ℝ≥0∞) * 2⁻¹ ^ C := by
          rw [Finset.sum_const, nsmul_eq_mul]; rfl
      _ ≤ (2 ^ C : ℝ≥0∞) * 2⁻¹ ^ C := by
          refine mul_le_mul' ?_ le_rfl
          have h1 : progCount U x (Ku U x) ≤ C := hC x (Ku U x) (KPPlain_eq_Ku hU x).symm
          have h2 : C ≤ 2 ^ C := (Nat.lt_two_pow_self).le
          exact_mod_cast h1.trans h2
      _ = 1 := by
          rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel (by positivity) (by simp)]
  refine ⟨c + C, fun x ↦ ?_⟩
  have h := hc (xk U x) (hsum x) (xStar U x)
  have hmem : ShortDesc U (xStar U x) (xk U x) := by
    rw [hR]; obtain ⟨hp, hlen⟩ := xStar_spec hU x
    exact mem_progSet.mpr ⟨hlen, hp⟩
  rw [reInd, if_pos hmem, ← pow_add, complexityWeight_KP hU] at h
  exact le_of_inv_two_pow_le h

/-- **`x* ≍ ⟨x, K(x)⟩`** (Gács, after Definition 3.1.6). -/
theorem xStar_equiv (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, Kc U (xk U x) (xStar U x) ≤ c ∧ Kc U (xStar U x) (xk U x) ≤ c := by
  obtain ⟨c₁, h₁⟩ := xk_le_xStar hU
  obtain ⟨c₂, h₂⟩ := xStar_le_xk hU
  exact ⟨c₁ + c₂, fun x ↦ ⟨(h₁ x).trans (by omega), (h₂ x).trans (by omega)⟩⟩

end Kolmogorov.Information
