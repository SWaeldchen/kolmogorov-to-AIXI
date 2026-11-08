/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Oracle.RarelyComplex
import Gacs_Chapter_3.Classical.ExpectedComplexity

/-!
# Gács Theorem 3.3.1: the main argument

See `RarelyComplex.lean` for the overview. This file proves that the request stream reads the
true `K(x)`, `f(x)` and `K(f(x))` along `χ` (`kVal_eq`, `readyB_spec`, `eventually_readyB`),
that its Kraft mass along `χ` is at most one (`tsum_lenStar_le`, via the sharp Lemma 3.3.2), and
assembles **Theorem 3.3.1** in the sharp form `K(x ∣ χ) + f(x) ≤ K(x) + 2 K(f(x)) + c`
(`rarely_complex`, and the information form `rarely_complex_info`).
-/

namespace Kolmogorov.Information.Oracle

open scoped ENNReal
open Kolmogorov.Information (Kc Ku KP_eq_Kc Kc_le_Ku Kc_map Ku_xk_xStar xStar_spec)
open Kolmogorov.Information.Halting (IsCodeOf chi bitLen bitLen_eq_size
  complexityOfComplexity aprioriMeasure_complexityOfComplexity_le exists_isCodeOf)
open Kolmogorov.Information.Classical (tsum_inv_two_pow_KP_le_one)
open Kolmogorov.Randomness (Seq seqTake length_seqTake seqTake_prefix
  two_pow_ne_zero' two_pow_ne_top')
open Nat.Partrec (Code)

variable {U : Map}

/-- **`f(x) = K(K(x) ∣ x)`** as a natural number. -/
noncomputable def fcc (U : Map) (x : BitString) : ℕ := Kc U (natCode (Ku U x)) x

theorem complexityOfComplexity_eq (hU : IsOptimalPrefixConditional U) (x : BitString) :
    complexityOfComplexity U x = (fcc U x : ENat) := KP_eq_Kc hU _ _

/-- Admissible constants for `U`. -/
structure RCValid (U : Map) (P : RCParams) : Prop where
  code : IsCodeOf U P.code
  tag : ∀ x q, U (P.tag ++ pairCode x q, []) = U (q, x)
  hK : ∀ x, Ku U x ≤ boundK P x
  hF : ∀ x, fcc U x ≤ boundF P (Ku U x)
  hle : ∀ x, fcc U x ≤ Ku U x + P.c₀

/-! ### Reading `K` and `f` off `χ` -/

/-- `minHit` computes `K(y ∣ z)` when the wrapped programs are programs for `U(·, z)`. -/
theorem minHit_eq_Kc (hU : IsOptimalPrefixConditional U) {c : Code} (hc : IsCodeOf U c)
    {σ : BitString} (hσ : IsChiPrefix U σ) {w : BitString → BitString} {y z : BitString} {B : ℕ}
    (hw : ∀ q, U (w q, []) = U (q, z)) (hall : allKnown c σ w B = true) (hB : Kc U y z ≤ B) :
    minHit c σ w (Encodable.encode y) B = Kc U y z := by
  classical
  obtain ⟨q₀, hq₀, hm₀⟩ := exists_short_program hU y z
  have hex : ∃ q : BitString, q.length ≤ B ∧ y ∈ U (w q, []) :=
    ⟨q₀, le_trans hq₀ hB, by rw [hw]; exact hm₀⟩
  rw [minHit_eq hc hσ hall hex]
  apply le_antisymm
  · exact Nat.find_le ⟨q₀, hq₀, by rw [hw]; exact hm₀⟩
  · obtain ⟨q, hq, hmem⟩ := Nat.find_spec
      (⟨B, hex⟩ : ∃ L, ∃ q : BitString, q.length ≤ L ∧ y ∈ U (w q, []))
    rw [hw] at hmem
    have h := KP_le_programLength_of_produces (M := U) (p := q) (x := y) (y := z) hmem
    rw [KP_eq_Kc hU] at h
    have : Kc U y z ≤ q.length := by exact_mod_cast h
    omega

variable {P : RCParams}

theorem kVal_eq (hU : IsOptimalPrefixConditional U) (hP : RCValid U P) {σ x : BitString}
    (hσ : IsChiPrefix U σ) (hall : allKnown P.code σ id (boundK P x) = true) :
    kVal P σ x = Ku U x := by
  rw [kVal]
  exact minHit_eq_Kc hU hP.code hσ (fun q ↦ rfl) hall (hP.hK x)

theorem fVal_eq (hU : IsOptimalPrefixConditional U) (hP : RCValid U P) {σ x : BitString}
    (hσ : IsChiPrefix U σ) (h1 : allKnown P.code σ id (boundK P x) = true)
    (h2 : allKnown P.code σ (wrapC P x) (boundF P (kVal P σ x)) = true) :
    fVal P σ x = fcc U x := by
  have hk := kVal_eq hU hP hσ h1
  rw [hk] at h2
  rw [fVal, hk]
  exact minHit_eq_Kc hU hP.code hσ (fun q ↦ hP.tag x q) h2 (hP.hF x)

/-- On a ready prefix of `χ`, the readers return `K(x)`, `f(x)` and `K(f(x))`. -/
theorem readyB_spec (hU : IsOptimalPrefixConditional U) (hP : RCValid U P) {σ x : BitString}
    (hσ : IsChiPrefix U σ) (hr : readyB P σ x = true) :
    kVal P σ x = Ku U x ∧ fVal P σ x = fcc U x ∧
      kVal P σ (natCode (fVal P σ x)) = Ku U (natCode (fcc U x)) := by
  rw [readyB, Bool.and_eq_true, Bool.and_eq_true] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  have hf := fVal_eq hU hP hσ h1 h2
  exact ⟨kVal_eq hU hP hσ h1, hf, by rw [kVal_eq hU hP hσ h3, hf]⟩

/-- The true requested length. -/
noncomputable def lenStar (U : Map) (P : RCParams) (x : BitString) : ℕ :=
  Ku U x + P.c₀ + 2 * Ku U (natCode (fcc U x)) - fcc U x

theorem lenReq_eq (hU : IsOptimalPrefixConditional U) (hP : RCValid U P) {σ x : BitString}
    (hσ : IsChiPrefix U σ) (hr : readyB P σ x = true) : lenReq P σ x = lenStar U P x := by
  obtain ⟨hk, hf, hkf⟩ := readyB_spec hU hP hσ hr
  rw [lenReq, hk, hkf, hf, lenStar]

theorem eventually_readyB (hU : IsOptimalPrefixConditional U) (hP : RCValid U P) (x : BitString) :
    ∃ m₀, ∀ m, m₀ ≤ m → readyB P (seqTake (chi U) m) x = true := by
  obtain ⟨m₁, h₁⟩ := knownOut_eventually_list hP.code (boundedPrograms (boundK P x))
  obtain ⟨m₂, h₂⟩ := knownOut_eventually_list hP.code
    ((boundedPrograms (boundF P (Ku U x))).map (wrapC P x))
  obtain ⟨m₃, h₃⟩ := knownOut_eventually_list hP.code
    (boundedPrograms (boundK P (natCode (fcc U x))))
  refine ⟨m₁ + m₂ + m₃, fun m hm ↦ ?_⟩
  have hσ := isChiPrefix_seqTake U m
  have hall1 : allKnown P.code (seqTake (chi U) m) id (boundK P x) = true :=
    allKnown_iff.mpr fun q hq ↦ h₁ m (by omega) q ((mem_boundedPrograms_iff q _).mpr hq)
  have hk := kVal_eq hU hP hσ hall1
  have hall2 : allKnown P.code (seqTake (chi U) m) (wrapC P x)
      (boundF P (kVal P (seqTake (chi U) m) x)) = true := by
    rw [hk]
    exact allKnown_iff.mpr fun q hq ↦ h₂ m (by omega) _
      (List.mem_map.mpr ⟨q, (mem_boundedPrograms_iff q _).mpr hq, rfl⟩)
  have hf := fVal_eq hU hP hσ hall1 hall2
  have hall3 : allKnown P.code (seqTake (chi U) m) id
      (boundK P (natCode (fVal P (seqTake (chi U) m) x))) = true := by
    rw [hf]
    exact allKnown_iff.mpr fun q hq ↦ h₃ m (by omega) q ((mem_boundedPrograms_iff q _).mpr hq)
  rw [readyB, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨hall1, hall2⟩, hall3⟩

theorem eventually_readyB_upto (hU : IsOptimalPrefixConditional U) (hP : RCValid U P) (n : ℕ) :
    ∃ m₀, ∀ m, m₀ ≤ m → ∀ i ≤ n, readyB P (seqTake (chi U) m) (strEnum i) = true := by
  induction n with
  | zero =>
    obtain ⟨m₀, h⟩ := eventually_readyB hU hP (strEnum 0)
    refine ⟨m₀, fun m hm i hi ↦ ?_⟩
    obtain rfl : i = 0 := by omega
    exact h m hm
  | succ n ih =>
    obtain ⟨m₁, h₁⟩ := ih
    obtain ⟨m₂, h₂⟩ := eventually_readyB hU hP (strEnum (n + 1))
    refine ⟨max m₁ m₂, fun m hm i hi ↦ ?_⟩
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact h₁ m (le_trans (le_max_left _ _) hm) i (by omega)
    · obtain rfl : i = n + 1 := by omega
      exact h₂ m (le_trans (le_max_right _ _) hm)

/-! ### The Kraft bound (Gács Lemma 3.3.2) -/

theorem two_pow_mul_inv_pow (j : ℕ) : (2 : ℝ≥0∞) ^ j * 2⁻¹ ^ j = 1 := by
  rw [← ENNReal.inv_pow, ENNReal.mul_inv_cancel (two_pow_ne_zero' _) (two_pow_ne_top' _)]

/-- **The requests have Kraft mass at most one** (the sharp Lemma 3.3.2 in action):
`∑ₓ 2^{-K(x) + f(x) - 2K(f(x)) - c₀} ≤ C 2^{-c₀} ∑ₙ 2^{-K(n)} ≤ 1`. -/
theorem tsum_lenStar_le (hU : IsOptimalPrefixConditional U) {C : ℕ}
    (hC : ∀ n : ℕ, ∑' x, (if complexityOfComplexity U x = n then aprioriMeasure U x []
      else 0) ≤ (C : ℝ≥0∞) * 2 ^ Ku U (natCode n) * 2⁻¹ ^ n)
    (hc₀ : C ≤ 2 ^ P.c₀) (hle : ∀ x, fcc U x ≤ Ku U x + P.c₀) :
    ∑' x, (2 : ℝ≥0∞)⁻¹ ^ lenStar U P x ≤ 1 := by
  set G : ℕ → ℝ≥0∞ := fun n ↦
    2 ^ n * (2⁻¹ ^ P.c₀ * (2⁻¹ ^ Ku U (natCode n) * 2⁻¹ ^ Ku U (natCode n))) with hG
  -- termwise: `2^{-lenStar} ≤ G (f x) · m(x)`
  have hterm : ∀ x, (2 : ℝ≥0∞)⁻¹ ^ lenStar U P x ≤ G (fcc U x) * aprioriMeasure U x [] := by
    intro x
    have hm : (2 : ℝ≥0∞)⁻¹ ^ Ku U x ≤ aprioriMeasure U x [] := by
      have := complexityWeight_KP_le_aprioriMeasure U x []
      rwa [Kolmogorov.Information.complexityWeight_KP hU] at this
    have hsplit : lenStar U P x + fcc U x = Ku U x +
        (P.c₀ + (Ku U (natCode (fcc U x)) + Ku U (natCode (fcc U x)))) := by
      unfold lenStar; have := hle x; omega
    calc (2 : ℝ≥0∞)⁻¹ ^ lenStar U P x
        = 2 ^ fcc U x * 2⁻¹ ^ (lenStar U P x + fcc U x) := by
          rw [pow_add, ← mul_assoc, mul_comm (2 ^ fcc U x), mul_assoc,
            two_pow_mul_inv_pow, mul_one]
      _ = G (fcc U x) * 2⁻¹ ^ Ku U x := by
          rw [hsplit, hG]; simp only; rw [pow_add, pow_add, pow_add]; ring
      _ ≤ G (fcc U x) * aprioriMeasure U x [] := mul_le_mul' le_rfl hm
  -- regroup by the value of `f`
  have hgroup : ∑' x, G (fcc U x) * aprioriMeasure U x [] =
      ∑' n, G n * ∑' x, (if complexityOfComplexity U x = n then aprioriMeasure U x [] else 0) := by
    have h1 : ∀ x, G (fcc U x) * aprioriMeasure U x [] =
        ∑' n, (if n = fcc U x then G n * aprioriMeasure U x [] else 0) := fun x ↦ by
      rw [tsum_ite_eq (fcc U x)]
    simp_rw [h1]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun n ↦ ?_
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun x ↦ ?_
    by_cases h : fcc U x = n
    · subst h; simp [complexityOfComplexity_eq hU]
    · have h' : ¬ n = fcc U x := fun e ↦ h e.symm
      have h'' : complexityOfComplexity U x ≠ n := by
        rw [complexityOfComplexity_eq hU]; exact_mod_cast h
      simp [h', h'']
  -- Kraft: `∑ₙ 2^{-K(n)} ≤ 1`
  have hkraft : ∑' n, (2 : ℝ≥0∞)⁻¹ ^ Ku U (natCode n) ≤ 1 :=
    (ENNReal.tsum_comp_le_tsum_of_injective natCode_injective
      (fun s ↦ (2 : ℝ≥0∞)⁻¹ ^ Ku U s)).trans (tsum_inv_two_pow_KP_le_one U hU)
  calc ∑' x, (2 : ℝ≥0∞)⁻¹ ^ lenStar U P x
      ≤ ∑' x, G (fcc U x) * aprioriMeasure U x [] := ENNReal.tsum_le_tsum hterm
    _ = ∑' n, G n * ∑' x, (if complexityOfComplexity U x = n then aprioriMeasure U x []
          else 0) := hgroup
    _ ≤ ∑' n, G n * ((C : ℝ≥0∞) * 2 ^ Ku U (natCode n) * 2⁻¹ ^ n) :=
        ENNReal.tsum_le_tsum fun n ↦ mul_le_mul' le_rfl (hC n)
    _ = ∑' n, (C : ℝ≥0∞) * 2⁻¹ ^ P.c₀ * 2⁻¹ ^ Ku U (natCode n) := by
        refine tsum_congr fun n ↦ ?_
        rw [hG]
        simp only
        calc (2 : ℝ≥0∞) ^ n * (2⁻¹ ^ P.c₀ *
              (2⁻¹ ^ Ku U (natCode n) * 2⁻¹ ^ Ku U (natCode n))) *
              (↑C * 2 ^ Ku U (natCode n) * 2⁻¹ ^ n)
            = (2 ^ n * 2⁻¹ ^ n) * (2 ^ Ku U (natCode n) * 2⁻¹ ^ Ku U (natCode n)) *
                (↑C * 2⁻¹ ^ P.c₀ * 2⁻¹ ^ Ku U (natCode n)) := by ring
          _ = _ := by rw [two_pow_mul_inv_pow, two_pow_mul_inv_pow, one_mul, one_mul]
    _ = (C : ℝ≥0∞) * 2⁻¹ ^ P.c₀ * ∑' n, (2 : ℝ≥0∞)⁻¹ ^ Ku U (natCode n) :=
        ENNReal.tsum_mul_left
    _ ≤ (C : ℝ≥0∞) * 2⁻¹ ^ P.c₀ * 1 := mul_le_mul' le_rfl hkraft
    _ ≤ 1 := by
        rw [mul_one]
        calc (C : ℝ≥0∞) * 2⁻¹ ^ P.c₀ ≤ 2 ^ P.c₀ * 2⁻¹ ^ P.c₀ :=
              mul_le_mul' (by exact_mod_cast hc₀) le_rfl
          _ = 1 := two_pow_mul_inv_pow _

/-- Along `χ`, the requests have Kraft mass at most one. -/
theorem kraft_reqRC (hU : IsOptimalPrefixConditional U) (hP : RCValid U P)
    (hkraft : ∑' x, (2 : ℝ≥0∞)⁻¹ ^ lenStar U P x ≤ 1) (m : ℕ) :
    ∑' n, (match reqRC P (seqTake (chi U) m) n with
      | some r => (2 : ℝ≥0∞)⁻¹ ^ r.2 | none => 0) ≤ 1 := by
  have hterm : ∀ n, (match reqRC P (seqTake (chi U) m) n with
      | some r => (2 : ℝ≥0∞)⁻¹ ^ r.2 | none => 0) ≤ (2 : ℝ≥0∞)⁻¹ ^ lenStar U P (strEnum n) := by
    intro n
    rcases h : reqRC P (seqTake (chi U) m) n with _ | r
    · exact zero_le
    · obtain ⟨hall, rfl⟩ := (reqRC_eq_some_iff P).mp h
      simp only
      rw [lenReq_eq hU hP (isChiPrefix_seqTake U m) (hall n le_rfl)]
  calc ∑' n, (match reqRC P (seqTake (chi U) m) n with
        | some r => (2 : ℝ≥0∞)⁻¹ ^ r.2 | none => 0)
      ≤ ∑' n, (2 : ℝ≥0∞)⁻¹ ^ lenStar U P (strEnum n) := ENNReal.tsum_le_tsum hterm
    _ ≤ ∑' x, (2 : ℝ≥0∞)⁻¹ ^ lenStar U P x :=
        ENNReal.tsum_comp_le_tsum_of_injective strEnum_injective _
    _ ≤ 1 := hkraft

/-! ### Theorem 3.3.1 -/

/-- Admissible constants exist for an exactly universal machine. -/
theorem exists_rcValid (hU : IsExactUniversal U) :
    ∃ P : RCParams, RCValid U P ∧ ∑' x, (2 : ℝ≥0∞)⁻¹ ^ lenStar U P x ≤ 1 := by
  have hUo := hU.isOptimalPrefixConditional
  obtain ⟨c, hc⟩ := exists_isCodeOf hUo.isDecompressor
  obtain ⟨t, ht⟩ := exists_tag_cond hU
  obtain ⟨cK, hcK⟩ := KPPlain_le_length_add_log U hUo
  obtain ⟨c₁, hc₁⟩ := Kc_le_Ku hUo
  have hg : Computable (fun q : BitString ↦ natCode q.length) :=
    natCode_computable.comp Computable.list_length
  obtain ⟨c₂, hc₂⟩ := Kc_map hUo hg
  obtain ⟨c₃, hc₃⟩ := Ku_xk_xStar hUo
  obtain ⟨C, hC⟩ := aprioriMeasure_complexityOfComplexity_le hUo
  -- `K(z) ≤ |z| + 2 size |z| + cK`
  have hKb : ∀ z, Ku U z ≤ z.length + 2 * bitLen z.length + cK := fun z ↦ by
    have h := hcK z
    rw [KPPlain_eq_Ku hUo, Nat.size_eq_bits_len, ← bitLen_eq_size] at h
    exact_mod_cast h
  -- `f(x) ≤ K(K(x)) + c₁ ≤ K(x) + c₁ + c₂ + c₃`
  have hf1 : ∀ x, fcc U x ≤ Ku U (natCode (Ku U x)) + c₁ := fun x ↦ hc₁ _ _
  have hf2 : ∀ x, fcc U x ≤ Ku U x + (c₁ + c₂ + c₃) := fun x ↦ by
    have a := hf1 x
    have b := hc₂ (xStar U x) []
    rw [(xStar_spec hUo x).2] at b
    have d := (hc₃ x).2.2.1
    unfold Ku at *
    omega
  let P : RCParams := ⟨c, t, cK, c₁ + cK, c₁ + c₂ + c₃ + C⟩
  have hP : RCValid U P := by
    refine ⟨hc, ht, fun x ↦ hKb x, fun x ↦ ?_, fun x ↦ ?_⟩
    · have a := hf1 x
      have b := hKb (natCode (Ku U x))
      rw [length_natCode] at b
      change fcc U x ≤ Ku U x + 1 + 2 * bitLen (Ku U x + 1) + (c₁ + cK)
      omega
    · change fcc U x ≤ Ku U x + (c₁ + c₂ + c₃ + C)
      have := hf2 x; omega
  refine ⟨P, hP, tsum_lenStar_le hUo (fun n ↦ hC n) ?_ hP.hle⟩
  change C ≤ 2 ^ (c₁ + c₂ + c₃ + C)
  calc C ≤ 2 ^ C := (Nat.lt_two_pow_self).le
    _ ≤ 2 ^ (c₁ + c₂ + c₃ + C) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **Gács Theorem 3.3.1, sharp form.** For an exactly universal `U` with halting sequence `χ`
and an optimal oracle machine `V`: `K(x ∣ χ) + f(x) ≤ K(x) + 2 K(f(x)) + c`, where
`f(x) = K(K(x) ∣ x)`. Equivalently `I(χ : x) = K(x) − K(x ∣ χ) ≥ f(x) − 2 K(f(x)) − c`.
(Gács: `≥ f(x) − 2.4 log f(x) − c`, implied by this since `K(n) ≤ 1.2 log n + O(1)`.) -/
theorem rarely_complex (hU : IsExactUniversal U) {V : Map} (hV : IsOptimalOracle V) :
    ∃ c : ℕ, ∀ x, KPrel V (chi U) x + fcc U x ≤ Ku U x + 2 * Ku U (natCode (fcc U x)) + c := by
  have hUo := hU.isOptimalPrefixConditional
  obtain ⟨P, hP, hkraft⟩ := exists_rcValid hU
  obtain ⟨W, hW, hWreq⟩ := exists_oracleMachine_of_requests (reqRC P)
    (reqRC_primrec P).to_comp (fun σ τ n r h hr ↦ reqRC_mono P h hr)
    (fun σ n m hmn hs ↦ reqRC_init P hmn hs)
  obtain ⟨cV, hcV⟩ := hV.2 W hW
  refine ⟨P.c₀ + cV, fun x ↦ ?_⟩
  obtain ⟨n, rfl⟩ := exists_strEnum_eq x
  obtain ⟨m, hm⟩ := eventually_readyB_upto hUo hP n
  have hreq : reqRC P (seqTake (chi U) m) n =
      some (strEnum n, lenReq P (seqTake (chi U) m) (strEnum n)) :=
    (reqRC_eq_some_iff P).mpr ⟨hm m le_rfl, rfl⟩
  have hW' := hWreq (chi U) (kraft_reqRC hUo hP hkraft) n (strEnum n) _ m hreq
  rw [lenReq_eq hUo hP (isChiPrefix_seqTake U m) (hm m le_rfl n le_rfl)] at hW'
  have hV' := hcV (chi U) (strEnum n)
  have hsplit : lenStar U P (strEnum n) + fcc U (strEnum n) =
      Ku U (strEnum n) + 2 * Ku U (natCode (fcc U (strEnum n))) + P.c₀ := by
    unfold lenStar; have := hP.hle (strEnum n); omega
  calc KPrel V (chi U) (strEnum n) + fcc U (strEnum n)
      ≤ (KPrel W (chi U) (strEnum n) + cV) + fcc U (strEnum n) := add_le_add hV' le_rfl
    _ ≤ ((lenStar U P (strEnum n) : ENat) + cV) + fcc U (strEnum n) :=
        add_le_add (add_le_add hW' le_rfl) le_rfl
    _ = ((lenStar U P (strEnum n) + fcc U (strEnum n) : ℕ) : ENat) + cV := by
        push_cast; ring
    _ = Ku U (strEnum n) + 2 * Ku U (natCode (fcc U (strEnum n))) +
          ((P.c₀ + cV : ℕ) : ENat) := by
        rw [hsplit]; push_cast; ring

/-- **Theorem 3.3.1, information form.** `I(χ : x) ≥ f(x) − 2 K(f(x)) − c`, with
`I(χ : x) = K(x) − K(x ∣ χ)`. -/
theorem rarely_complex_info (hU : IsExactUniversal U) {V : Map} (hV : IsOptimalOracle V) :
    ∃ c : ℕ, ∀ x, (fcc U x : ℤ) - 2 * Ku U (natCode (fcc U x)) - c ≤
      (Ku U x : ℤ) - (KPrel V (chi U) x).toNat := by
  obtain ⟨c, hc⟩ := rarely_complex hU hV
  refine ⟨c, fun x ↦ ?_⟩
  have h := hc x
  have hfin : KPrel V (chi U) x = ((KPrel V (chi U) x).toNat : ENat) :=
    (ENat.coe_toNat (hV.KPrel_ne_top (chi U) x)).symm
  rw [hfin] at h
  have h' : (KPrel V (chi U) x).toNat + fcc U x ≤
      Ku U x + 2 * Ku U (natCode (fcc U x)) + c := by exact_mod_cast h
  omega

end Kolmogorov.Information.Oracle
