/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Information.Basic

/-!
# Algorithmic information identities (Gács §3.1.1, after the addition theorem)

All statements are "`=⁺`" / "`≤⁺`" (`AddEq`, `AddLE`) of integer-valued functions of the
strings involved, with constants depending only on the optimal machine `U`.

| Gács | Lean |
|---|---|
| `x* ≍ ⟨x, K(x)⟩`, also as a condition | `xStar_equiv`, `Kc_xk_xStar` |
| (3.1.x) `K(x,y) − K(x) =⁺ K(y ∣ x*)` | `addition_star` |
| Corollary 3.1.5, `K(x*, y) =⁺ K(x, y)` | `Ku_xStar_pair` |
| Definition 3.1.6, `f ⪯ g mod h`, `≍` | `InfoLE`, `InfoLEMod`, `InfoEquiv` (`.cond`, `.obj`) |
| Definition 3.1.7, `K*(y ∣ x) = K(y ∣ x*)`, its addition law | `Kstar`, `Kstar_addition` |
| Definitions 3.1.8, 3.1.9: `I(x:y)`, `I*(x:y)` | `Info`, `InfoStar` |
| `I*(x:y) =⁺ I(x*:y) =⁺ I(y*:x)` | `infoStar_eq_info_xStar`, `infoStar_eq_info_yStar` |
| Corollary 3.1.12, defects | `additivity_defect(_le)`, `info_asymmetry` |
| Theorem 3.1.8, simple triangle inequality | `simple_triangle` |
| Definition 3.1.14, `I*(x:y ∣ z)`, two forms | `CondInfoStar`, `condInfoStar_eq_left/right` |
| Theorem 3.1.9, algorithmic data processing identity | `data_processing` |
| Corollary 3.1.15, monotonicity of `I*` | `infoStar_mono` |
| Theorem 3.1.10, starry triangle inequality | `starry_triangle` |
-/

namespace Kolmogorov.Information

open scoped ENNReal

variable {U : Map}

/-! ### Pair rearrangements -/

/-- `⟨x, y⟩ ↦ ⟨y, x⟩`. -/
def pswap (w : BitString) : BitString := pairCode (decodeSecond w) (decodeFirst w)

theorem pswap_pairCode (x y : BitString) : pswap (pairCode x y) = pairCode y x := by
  simp [pswap, decodeFirst_pairCode, decodeSecond_pairCode]

theorem pswap_computable : Computable pswap := by
  have h := pairCode_computable.comp
    (Computable.pair decodeSecond_computable decodeFirst_computable)
  exact h.of_eq fun _ ↦ rfl

/-- `⟨z, ⟨x, y⟩⟩ ↦ ⟨x, ⟨z, y⟩⟩`. -/
def prot (w : BitString) : BitString :=
  pairCode (decodeFirst (decodeSecond w)) (pairCode (decodeFirst w) (decodeSecond (decodeSecond w)))

theorem prot_pairCode (z x y : BitString) :
    prot (pairCode z (pairCode x y)) = pairCode x (pairCode z y) := by
  simp [prot, decodeFirst_pairCode, decodeSecond_pairCode]

theorem prot_computable : Computable prot := by
  have h1 := pairCode_computable.comp (Computable.pair decodeFirst_computable
    (decodeSecond_computable.comp decodeSecond_computable))
  have h2 := pairCode_computable.comp (Computable.pair
    (decodeFirst_computable.comp decodeSecond_computable) h1)
  exact h2.of_eq fun _ ↦ rfl

/-- `K(⟨x, y⟩ ∣ z) =⁺ K(⟨y, x⟩ ∣ z)`. -/
theorem Kc_pair_swap (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y z, Kc U (pairCode x y) z ≤ Kc U (pairCode y x) z + c := by
  obtain ⟨c, hc⟩ := Kc_map hU pswap_computable
  exact ⟨c, fun x y z ↦ by simpa [pswap_pairCode] using hc (pairCode y x) z⟩

/-- `K(⟨z, ⟨x, y⟩⟩) =⁺ K(⟨x, ⟨z, y⟩⟩)`. -/
theorem Kc_prot (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y z w, Kc U (pairCode z (pairCode x y)) w ≤
      Kc U (pairCode x (pairCode z y)) w + c := by
  obtain ⟨c, hc⟩ := Kc_map hU prot_computable
  exact ⟨c, fun x y z w ↦ by simpa [prot_pairCode] using hc (pairCode x (pairCode z y)) w⟩

/-- Projections: `K(x ∣ w) ≤ K(⟨x, y⟩ ∣ w) + c` and `K(y ∣ w) ≤ K(⟨x, y⟩ ∣ w) + c`. -/
theorem Kc_proj (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y w, Kc U x w ≤ Kc U (pairCode x y) w + c ∧
      Kc U y w ≤ Kc U (pairCode x y) w + c := by
  obtain ⟨c₁, h₁⟩ := Kc_map hU decodeFirst_computable
  obtain ⟨c₂, h₂⟩ := Kc_map hU decodeSecond_computable
  refine ⟨c₁ + c₂, fun x y w ↦ ⟨?_, ?_⟩⟩
  · have := h₁ (pairCode x y) w; rw [decodeFirst_pairCode] at this; omega
  · have := h₂ (pairCode x y) w; rw [decodeSecond_pairCode] at this; omega

/-- Subadditivity: `K(⟨x, y⟩ ∣ w) ≤ K(x ∣ w) + K(y ∣ w) + c`. -/
theorem Kc_pair_subadd (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y w, Kc U (pairCode x y) w ≤ Kc U x w + Kc U y w + c := by
  obtain ⟨c₁, h₁⟩ := condAddition hU
  obtain ⟨c₂, h₂⟩ := Kc_cond_map hU decodeFirst_computable
  refine ⟨c₁ + c₂, fun x y w ↦ ?_⟩
  have a := (h₁ x y w).1
  have b := h₂ y (condCtx U w x)
  have hdec : decodeFirst (condCtx U w x) = w := by
    simp [condCtx, prefixCondComplexityContext, decodeFirst_pairCode]
  rw [hdec] at b
  omega

/-- The middle of `condCtx w x = ⟨w, ⟨x, k⟩⟩` is recovered: `K(y ∣ condCtx w x) ≤ K(y ∣ x) + c`;
and the first component: `K(y ∣ condCtx w x) ≤ K(y ∣ w) + c`. -/
theorem Kc_condCtx_drop (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ y w x, Kc U y (condCtx U w x) ≤ Kc U y x + c ∧
      Kc U y (condCtx U w x) ≤ Kc U y w + c := by
  obtain ⟨c₁, h₁⟩ := Kc_cond_map hU (decodeFirst_computable.comp decodeSecond_computable)
  obtain ⟨c₂, h₂⟩ := Kc_cond_map hU decodeFirst_computable
  refine ⟨c₁ + c₂, fun y w x ↦ ⟨?_, ?_⟩⟩
  · have := h₁ y (condCtx U w x)
    simp only [condCtx, prefixCondComplexityContext, decodeFirst_pairCode,
      decodeSecond_pairCode] at this
    unfold condCtx prefixCondComplexityContext; omega
  · have := h₂ y (condCtx U w x)
    simp only [condCtx, prefixCondComplexityContext, decodeFirst_pairCode] at this
    unfold condCtx prefixCondComplexityContext; omega

/-! ### `x*` as a condition, and the starred addition theorem -/

/-- **Definition 3.1.6**, without and with a modulus: `f ⪯ g` iff `K(f ∣ g) ≤ c`. -/
def InfoLE (U : Map) {ι : Type*} (f g : ι → BitString) : Prop :=
  ∃ c : ℕ, ∀ i, Kc U (f i) (g i) ≤ c

/-- `f ⪯ g mod h` iff `K(f ∣ g, h) ≤ c`. -/
def InfoLEMod (U : Map) {ι : Type*} (f g h : ι → BitString) : Prop :=
  ∃ c : ℕ, ∀ i, Kc U (f i) (pairCode (g i) (h i)) ≤ c

/-- `f ≍ g`: the two hold essentially the same information. -/
def InfoEquiv (U : Map) {ι : Type*} (f g : ι → BitString) : Prop :=
  InfoLE U f g ∧ InfoLE U g f

/-- Equivalent objects can be exchanged in conditions. -/
theorem InfoEquiv.cond (hU : IsOptimalPrefixConditional U) {ι : Type*} {f g : ι → BitString}
    (h : InfoEquiv U f g) : ∃ c : ℕ, ∀ y i, Kc U y (f i) ≤ Kc U y (g i) + c ∧
      Kc U y (g i) ≤ Kc U y (f i) + c := by
  obtain ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ := h
  obtain ⟨ct, ht⟩ := Kc_triangle hU
  refine ⟨c₁ + c₂ + ct, fun y i ↦ ⟨?_, ?_⟩⟩
  · have := ht (f i) (g i) y; have := h₂ i; omega
  · have := ht (g i) (f i) y; have := h₁ i; omega

/-- Equivalent objects have the same complexities in any condition. -/
theorem InfoEquiv.obj (hU : IsOptimalPrefixConditional U) {ι : Type*} {f g : ι → BitString}
    (h : InfoEquiv U f g) : ∃ c : ℕ, ∀ y i, Kc U (f i) y ≤ Kc U (g i) y + c ∧
      Kc U (g i) y ≤ Kc U (f i) y + c := by
  obtain ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩ := h
  obtain ⟨ct, ht⟩ := Kc_triangle hU
  refine ⟨c₁ + c₂ + ct, fun y i ↦ ⟨?_, ?_⟩⟩
  · have := ht y (g i) (f i); have := h₁ i; omega
  · have := ht y (f i) (g i); have := h₂ i; omega

theorem xStar_infoEquiv (hU : IsOptimalPrefixConditional U) :
    InfoEquiv U (xStar U) (xk U) := by
  obtain ⟨c, hc⟩ := xStar_equiv hU
  exact ⟨⟨c, fun x ↦ (hc x).2⟩, ⟨c, fun x ↦ (hc x).1⟩⟩

/-- `K(y ∣ x, K(x)) =⁺ K(y ∣ x*)`. -/
theorem Kc_xk_xStar (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, Kc U y (xk U x) ≤ Kc U y (xStar U x) + c ∧
      Kc U y (xStar U x) ≤ Kc U y (xk U x) + c := by
  obtain ⟨c, hc⟩ := (xStar_infoEquiv hU).cond hU
  exact ⟨c, fun x y ↦ ⟨(hc y x).2, (hc y x).1⟩⟩

/-- `K(⟨x, K(x)⟩) =⁺ K(x)` and `K(x*) =⁺ K(x)`. -/
theorem Ku_xk_xStar (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, Ku U (xk U x) ≤ Ku U x + c ∧ Ku U x ≤ Ku U (xk U x) + c ∧
      Ku U (xStar U x) ≤ Ku U x + c ∧ Ku U x ≤ Ku U (xStar U x) + c := by
  obtain ⟨c₁, h₁⟩ := KPPair_natCode_self_eq_KPPlain U hU
  obtain ⟨c₂, h₂⟩ := (xStar_infoEquiv hU).obj hU
  refine ⟨c₁ + c₂, fun x ↦ ?_⟩
  have hk : HasPrefixComplexityValue U x (Ku U x) := (KPPlain_eq_Ku hU x).symm
  obtain ⟨a, b⟩ := h₁ x (Ku U x) hk
  unfold KPPair at a b
  rw [KPPlain_eq_Ku hU, KP_eq_Kc hU] at a b
  have a' : Ku U x ≤ Kc U (pairCode x (natCode (Ku U x))) [] + c₁ := by exact_mod_cast a
  have b' : Kc U (pairCode x (natCode (Ku U x))) [] ≤ Ku U x + c₁ := by exact_mod_cast b
  obtain ⟨e1, e2⟩ := h₂ [] x
  unfold xk Ku at *
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- **`K(x, y) =⁺ K(x) + K(y ∣ x*)`** (Gács' (3.1.x) after Definition 3.1.6). -/
theorem addition_star (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, Ku U (pairCode x y) ≤ Ku U x + Kc U y (xStar U x) + c ∧
      Ku U x + Kc U y (xStar U x) ≤ Ku U (pairCode x y) + c := by
  obtain ⟨c₁, h₁⟩ := addition hU
  obtain ⟨c₂, h₂⟩ := Kc_xk_xStar hU
  refine ⟨c₁ + c₂, fun x y ↦ ?_⟩
  have a := h₁ x y; have b := h₂ x y
  omega

/-- **Gács Corollary 3.1.5.** `K(x*, y) =⁺ K(x, y)`. -/
theorem Ku_xStar_pair (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, Ku U (pairCode (xStar U x) y) ≤ Ku U (pairCode x y) + c ∧
      Ku U (pairCode x y) ≤ Ku U (pairCode (xStar U x) y) + c := by
  -- `⟨x*, y⟩ ↦ ⟨x, y⟩` is partial computable
  have hU' : Partrec (fun p : BitString × BitString ↦ U (decodeFirst p.1, ([] : BitString))) :=
    hU.isDecompressor.comp (Computable.pair (decodeFirst_computable.comp Computable.fst)
      (Computable.const []))
  have hg : Computable (fun q : (BitString × BitString) × BitString ↦
      pairCode q.2 (decodeSecond q.1.1)) := by
    have h := pairCode_computable.comp (Computable.pair Computable.snd
      (decodeSecond_computable.comp
        (Computable.fst.comp (Computable.fst (α := BitString × BitString) (β := BitString)))))
    exact h.of_eq fun _ ↦ rfl
  obtain ⟨c₁, h₁⟩ := Kc_map_partrec hU
    (fun _ w ↦ (U (decodeFirst w, [])).map (fun out ↦ pairCode out (decodeSecond w)))
    (Partrec.map hU' hg.to₂)
  obtain ⟨c₂, h₂⟩ := Ku_pair_le hU
  obtain ⟨c₃, h₃⟩ := Ku_xk_xStar hU
  obtain ⟨c₄, h₄⟩ := addition_star hU
  refine ⟨c₁ + c₂ + c₃ + c₄, fun x y ↦ ⟨?_, ?_⟩⟩
  · have a := h₂ (xStar U x) y
    have b := (h₃ x).2.2.1
    have d := (h₄ x y).2
    omega
  · have hmem : pairCode x y ∈ (fun (_ w : BitString) ↦
        (U (decodeFirst w, [])).map (fun out ↦ pairCode out (decodeSecond w)))
        [] (pairCode (xStar U x) y) := by
      refine (Part.mem_map_iff _).mpr ⟨x, ?_, by rw [decodeSecond_pairCode]⟩
      rw [decodeFirst_pairCode]; exact (xStar_spec hU x).1
    have := h₁ (pairCode (xStar U x) y) (pairCode x y) [] hmem
    unfold Ku; omega

/-! ### `K*`, `I`, `I*` (Definitions 3.1.7–3.1.9) -/

variable (U) in
/-- **Definition 3.1.7.** `K*(y ∣ x) = K(y ∣ x*)`. -/
noncomputable def Kstar (y x : BitString) : ℕ := Kc U y (xStar U x)

variable (U) in
/-- **Definition 3.1.8.** `I(x : y) = K(y) − K(y ∣ x)`. -/
noncomputable def Info (x y : BitString) : ℤ := Ku U y - Kc U y x

variable (U) in
/-- **Definition 3.1.9.** `I*(x : y) = K(x) + K(y) − K(x, y)`. -/
noncomputable def InfoStar (x y : BitString) : ℤ := Ku U x + Ku U y - Ku U (pairCode x y)

/-- `K*(x, y) =⁺ K*(x) + K*(y ∣ x)` (Chaitin's notation; `K*(x) = K(x)`). -/
theorem Kstar_addition (hU : IsOptimalPrefixConditional U) :
    AddEq (fun p : BitString × BitString ↦ (Ku U (pairCode p.1 p.2) : ℤ))
      (fun p ↦ (Ku U p.1 : ℤ) + Kstar U p.2 p.1) := by
  obtain ⟨c, hc⟩ := addition_star hU
  refine ⟨⟨c, fun p ↦ ?_⟩, ⟨c, fun p ↦ ?_⟩⟩ <;> dsimp only <;> have := hc p.1 p.2 <;>
    unfold Kstar <;> omega

/-- `I*(x : y) =⁺ K(y) − K(y ∣ x*)`, i.e. `I*(x:y) =⁺ I(x* : y)`. -/
theorem infoStar_eq_info_xStar (hU : IsOptimalPrefixConditional U) :
    AddEq (fun p : BitString × BitString ↦ InfoStar U p.1 p.2)
      (fun p ↦ Info U (xStar U p.1) p.2) := by
  obtain ⟨c, hc⟩ := addition_star hU
  refine ⟨⟨c, fun p ↦ ?_⟩, ⟨c, fun p ↦ ?_⟩⟩ <;> dsimp only <;> have := hc p.1 p.2 <;>
    unfold InfoStar Info <;> omega

/-- `I*(x : y) =⁺ I(y* : x)`. -/
theorem infoStar_eq_info_yStar (hU : IsOptimalPrefixConditional U) :
    AddEq (fun p : BitString × BitString ↦ InfoStar U p.1 p.2)
      (fun p ↦ Info U (xStar U p.2) p.1) := by
  obtain ⟨c₁, h₁⟩ := addition_star hU
  obtain ⟨c₂, h₂⟩ := Kc_pair_swap hU
  refine ⟨⟨c₁ + c₂, fun p ↦ ?_⟩, ⟨c₁ + c₂, fun p ↦ ?_⟩⟩ <;> dsimp only <;>
    have := h₁ p.2 p.1 <;> have := h₂ p.1 p.2 [] <;> have := h₂ p.2 p.1 [] <;>
    unfold InfoStar Info Ku at * <;> omega

/-! ### Corollary 3.1.12: the defects of additivity and symmetry -/

variable (U) in
/-- `I(u : v ∣ w) = K(v ∣ w) − K(v ∣ w, u)`. -/
noncomputable def CondInfo (u v w : BitString) : ℤ := Kc U v w - Kc U v (pairCode w u)

/-- **Corollary 3.1.12 (a).** `K(x) + K(y ∣ x) − K(x, y) =⁺ I(K(x) : y ∣ x)`. -/
theorem additivity_defect (hU : IsOptimalPrefixConditional U) :
    AddEq (fun p : BitString × BitString ↦
        (Ku U p.1 : ℤ) + Kc U p.2 p.1 - Ku U (pairCode p.1 p.2))
      (fun p ↦ CondInfo U (natCode (Ku U p.1)) p.2 p.1) := by
  obtain ⟨c, hc⟩ := addition hU
  refine ⟨⟨c, fun p ↦ ?_⟩, ⟨c, fun p ↦ ?_⟩⟩ <;> dsimp only <;> have := hc p.1 p.2 <;>
    unfold CondInfo <;> unfold xk at this <;> omega

/-- **Corollary 3.1.12 (a), second part.** `I(K(x) : y ∣ x) ≤⁺ K(K(x) ∣ x)`. -/
theorem additivity_defect_le (hU : IsOptimalPrefixConditional U) :
    AddLE (fun p : BitString × BitString ↦ CondInfo U (natCode (Ku U p.1)) p.2 p.1)
      (fun p ↦ (Kc U (natCode (Ku U p.1)) p.1 : ℤ)) := by
  obtain ⟨ct, ht⟩ := Kc_triangle hU
  -- `⟨x, k⟩` is computed from the condition `x` and the object `k`
  obtain ⟨cm, hm⟩ := Kc_map_partrec hU (fun y q ↦ Part.some (pairCode y q))
    (pairCode_computable.comp (Computable.pair Computable.snd Computable.fst)).partrec
  refine ⟨ct + cm, fun p ↦ ?_⟩
  have a := ht p.1 (pairCode p.1 (natCode (Ku U p.1))) p.2
  have b := hm (natCode (Ku U p.1)) (pairCode p.1 (natCode (Ku U p.1))) p.1 (Part.mem_some _)
  dsimp only; unfold CondInfo; push_cast; omega

/-- **Corollary 3.1.12 (b), information asymmetry.**
`I(x : y) − I(y : x) =⁺ I(K(y) : x ∣ y) − I(K(x) : y ∣ x)`. -/
theorem info_asymmetry (hU : IsOptimalPrefixConditional U) :
    AddEq (fun p : BitString × BitString ↦ Info U p.1 p.2 - Info U p.2 p.1)
      (fun p ↦ CondInfo U (natCode (Ku U p.2)) p.1 p.2 -
        CondInfo U (natCode (Ku U p.1)) p.2 p.1) := by
  obtain ⟨c₁, h₁⟩ := addition hU
  obtain ⟨c₂, h₂⟩ := Kc_pair_swap hU
  refine ⟨⟨2 * c₁ + c₂, fun p ↦ ?_⟩, ⟨2 * c₁ + c₂, fun p ↦ ?_⟩⟩ <;> dsimp only <;>
    have := h₁ p.1 p.2 <;> have := h₁ p.2 p.1 <;> have := h₂ p.1 p.2 [] <;>
    have := h₂ p.2 p.1 [] <;> unfold Info CondInfo xk Ku at * <;> push_cast <;> omega

/-! ### Theorem 3.1.8 and the conditional mutual information -/

/-- **Gács Theorem 3.1.8 (simple triangle inequality).**
`K(z ∣ x) ≤⁺ K(y, z ∣ x) ≤⁺ K(y ∣ x) + K(z ∣ y)`. -/
theorem simple_triangle (hU : IsOptimalPrefixConditional U) :
    AddLE (fun p : BitString × BitString × BitString ↦ (Kc U p.2.2 p.1 : ℤ))
        (fun p ↦ (Kc U (pairCode p.2.1 p.2.2) p.1 : ℤ)) ∧
      AddLE (fun p : BitString × BitString × BitString ↦ (Kc U (pairCode p.2.1 p.2.2) p.1 : ℤ))
        (fun p ↦ (Kc U p.2.1 p.1 : ℤ) + Kc U p.2.2 p.2.1) := by
  obtain ⟨c₁, h₁⟩ := Kc_proj hU
  obtain ⟨c₂, h₂⟩ := condAddition hU
  obtain ⟨c₃, h₃⟩ := Kc_condCtx_drop hU
  refine ⟨⟨c₁, fun p ↦ ?_⟩, ⟨c₂ + c₃, fun p ↦ ?_⟩⟩
  · dsimp only; have := (h₁ p.2.1 p.2.2 p.1).2; omega
  · dsimp only; have := (h₂ p.2.1 p.2.2 p.1).1; have := (h₃ p.2.2 p.1 p.2.1).1; omega

variable (U) in
/-- **Definition 3.1.14.** `I*(x : y ∣ z) = K(x ∣ z) + K(y ∣ z) − K(x, y ∣ z)`. -/
noncomputable def CondInfoStar (x y z : BitString) : ℤ :=
  Kc U x z + Kc U y z - Kc U (pairCode x y) z

/-- `I*(x : y ∣ z) =⁺ K(y ∣ z) − K(y ∣ z, x, K(x ∣ z))`. -/
theorem condInfoStar_eq_left (hU : IsOptimalPrefixConditional U) :
    AddEq (fun p : BitString × BitString × BitString ↦ CondInfoStar U p.1 p.2.1 p.2.2)
      (fun p ↦ (Kc U p.2.1 p.2.2 : ℤ) - Kc U p.2.1 (condCtx U p.2.2 p.1)) := by
  obtain ⟨c, hc⟩ := condAddition hU
  refine ⟨⟨c, fun p ↦ ?_⟩, ⟨c, fun p ↦ ?_⟩⟩ <;> dsimp only <;> have := hc p.1 p.2.1 p.2.2 <;>
    unfold CondInfoStar <;> omega

/-- `I*(x : y ∣ z) =⁺ K(x ∣ z) − K(x ∣ z, y, K(y ∣ z))`. -/
theorem condInfoStar_eq_right (hU : IsOptimalPrefixConditional U) :
    AddEq (fun p : BitString × BitString × BitString ↦ CondInfoStar U p.1 p.2.1 p.2.2)
      (fun p ↦ (Kc U p.1 p.2.2 : ℤ) - Kc U p.1 (condCtx U p.2.2 p.2.1)) := by
  obtain ⟨c₁, h₁⟩ := condAddition hU
  obtain ⟨c₂, h₂⟩ := Kc_pair_swap hU
  refine ⟨⟨c₁ + c₂, fun p ↦ ?_⟩, ⟨c₁ + c₂, fun p ↦ ?_⟩⟩ <;> dsimp only <;>
    have := h₁ p.2.1 p.1 p.2.2 <;> have := h₂ p.1 p.2.1 p.2.2 <;>
    have := h₂ p.2.1 p.1 p.2.2 <;> unfold CondInfoStar <;> omega

/-! ### Theorem 3.1.9: the algorithmic data processing identity -/

/-- **Gács Theorem 3.1.9 (algorithmic data processing identity).**
`I*(z : (x, y)) =⁺ I*(z : x) + I*(z : y ∣ x*)`. Variables `p = (z, x, y)`. -/
theorem data_processing (hU : IsOptimalPrefixConditional U) :
    AddEq (fun p : BitString × BitString × BitString ↦
        InfoStar U p.1 (pairCode p.2.1 p.2.2))
      (fun p ↦ InfoStar U p.1 p.2.1 + CondInfoStar U p.1 p.2.2 (xStar U p.2.1)) := by
  obtain ⟨c₁, h₁⟩ := addition_star hU
  obtain ⟨c₂, h₂⟩ := Kc_pair_swap hU
  obtain ⟨c₃, h₃⟩ := Kc_prot hU
  refine ⟨⟨3 * c₁ + 2 * c₂ + 2 * c₃, fun p ↦ ?_⟩, ⟨3 * c₁ + 2 * c₂ + 2 * c₃, fun p ↦ ?_⟩⟩ <;>
  · obtain ⟨z, x, y⟩ := p
    dsimp only
    have a1 := h₁ x z
    have a2 := h₁ x y
    have a3 := h₁ x (pairCode z y)
    have s1 := h₂ z x []
    have s2 := h₂ x z []
    have r1 := h₃ x y z []
    have r2 := h₃ z y x []
    unfold InfoStar CondInfoStar Ku at *
    push_cast
    omega

/-- **Gács Corollary 3.1.15 (monotonicity).** `I*(x : (y, z)) ≥⁺ I*(x : y)`. -/
theorem infoStar_mono (hU : IsOptimalPrefixConditional U) :
    AddLE (fun p : BitString × BitString × BitString ↦ InfoStar U p.1 p.2.1)
      (fun p ↦ InfoStar U p.1 (pairCode p.2.1 p.2.2)) := by
  obtain ⟨⟨c₁, -⟩, ⟨c₂, h₂⟩⟩ := data_processing hU
  obtain ⟨c₃, h₃⟩ := Kc_pair_subadd hU
  refine ⟨c₂ + c₃, fun p ↦ ?_⟩
  have a := h₂ p
  have b := h₃ p.1 p.2.2 (xStar U p.2.1)
  dsimp only at a ⊢
  unfold CondInfoStar at a
  omega

/-! ### Theorem 3.1.10: the starry triangle inequality -/

/-- `I*(x : y) =⁺ K(y) − K(y ∣ x*)`, in the unfolded form used below. -/
theorem infoStar_eq_sub (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x y, InfoStar U x y ≤ (Ku U y : ℤ) - Kc U y (xStar U x) + c ∧
      (Ku U y : ℤ) - Kc U y (xStar U x) ≤ InfoStar U x y + c := by
  obtain ⟨c, hc⟩ := addition_star hU
  exact ⟨c, fun x y ↦ by have := hc x y; unfold InfoStar; constructor <;> omega⟩

/-- **Gács Theorem 3.1.10 (starry triangle inequality).**
`K(x ∣ y*) ≤⁺ K(x, z ∣ y*) ≤⁺ K(z ∣ y*) + K(x ∣ z*)`. Variables `p = (x, y, z)`. -/
theorem starry_triangle (hU : IsOptimalPrefixConditional U) :
    AddLE (fun p : BitString × BitString × BitString ↦ (Kc U p.1 (xStar U p.2.1) : ℤ))
        (fun p ↦ (Kc U (pairCode p.1 p.2.2) (xStar U p.2.1) : ℤ)) ∧
      AddLE (fun p : BitString × BitString × BitString ↦
          (Kc U (pairCode p.1 p.2.2) (xStar U p.2.1) : ℤ))
        (fun p ↦ (Kc U p.2.2 (xStar U p.2.1) : ℤ) + Kc U p.1 (xStar U p.2.2)) := by
  obtain ⟨cp, hp⟩ := Kc_proj hU
  refine ⟨⟨cp, fun p ↦ by dsimp only; have := (hp p.1 p.2.2 (xStar U p.2.1)).1; omega⟩, ?_⟩
  -- data processing with `(z, x, y) := (y, z, x)`, in the `≥` direction
  obtain ⟨-, ⟨cd, hd⟩⟩ := data_processing hU
  obtain ⟨ce, he⟩ := infoStar_eq_sub hU
  obtain ⟨-, ⟨cr, hr⟩⟩ := condInfoStar_eq_left hU
  obtain ⟨cs, hs⟩ := Kc_pair_swap hU
  obtain ⟨cq, hq⟩ := Kc_condCtx_drop hU
  obtain ⟨ca, ha⟩ := addition_star hU
  refine ⟨cd + 2 * ce + cr + cs + cq + ca, fun p ↦ ?_⟩
  obtain ⟨x, y, z⟩ := p
  dsimp only
  have d := hd (y, z, x)
  have e1 := he y (pairCode z x)
  have e2 := he y z
  have r := hr (y, x, xStar U z)
  have s := hs x z (xStar U y)
  have q := (hq x (xStar U z) y).2
  have a := ha z x
  simp only at d r
  unfold CondInfoStar InfoStar at *
  push_cast
  omega

end Kolmogorov.Information
