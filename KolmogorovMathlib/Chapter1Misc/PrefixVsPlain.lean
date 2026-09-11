/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.PlainInformation.Subadditivity
import KolmogorovMathlib.AlgorithmicStatistics.TwoPart.GapCounting
import KolmogorovMathlib.Prefix.Properties

/-!
# Gács Theorem 1.6.2: `C ≤⁺ K ≤⁺ C + 2 log C`

Plain and prefix complexity differ by at most a logarithmic term. The first
inequality is `plainK_le_KPPlain` in `Prefix/Properties.lean`; this file supplies the
second, in conditional and unconditional form, and packages both.

Gács' proof builds a self-delimiting machine that reads a plain program prefixed by
its length in binary. We do not need to build it: the repository already knows that
`K(w) ≤⁺ |w| + 2 log |w|` for any string `w` (`KPPlain_le_length_add_log`) and that
applying a partial recursive map cannot raise `K` by more than a constant
(`KP_partrec_cond_first_map_le`). Take `w` to be a shortest plain program for `x`;
the map is "run the plain machine on `w`".
-/

namespace Kolmogorov

/-- **Gács Theorem 1.6.2, second half, conditional.** With `k = C_V(x | y)`,
`K_U(x | y) ≤ k + 2 log k + c`, the logarithm realised as the bit-length. -/
theorem KP_le_condK_add_log (U V : Map) (hU : IsOptimalPrefixConditional U)
    (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x y : BitString) (k : ℕ), (k : ENat) = condK V x y →
      KP U x y ≤ ((k + 2 * (Nat.bits k).length + c : ℕ) : ENat) := by
  -- Running the plain machine on a program is a partial recursive map of the program.
  obtain ⟨c₁, hc₁⟩ := KP_partrec_cond_first_map_le U hU (fun y w ↦ V (w, y))
    (hV.1.of_eq (fun p ↦ rfl))
  obtain ⟨c₂, hc₂⟩ := KP_le_KPPlain U hU
  obtain ⟨c₃, hc₃⟩ := KPPlain_le_length_add_log U hU
  refine ⟨c₁ + c₂ + c₃, fun x y k hk ↦ ?_⟩
  obtain ⟨p, hp, hplen⟩ : ∃ p, produces V p y x ∧ (programLength p : ENat) = condK V x y :=
    KP_mem_candidateLengths_of_ne_top (M := V) (x := x) (y := y)
      (by rw [KP_eq_condK]; exact condK_ne_top V hV x y)
  have hpk : p.length = k := by
    have : (p.length : ENat) = (k : ENat) := by rw [hplen, hk]
    exact_mod_cast this
  have h1 : KP U x y ≤ KP U p y + (c₁ : ENat) := hc₁ p x y hp
  have h2 : KP U p y ≤ KPPlain U p + (c₂ : ENat) := hc₂ p y
  have h3 := hc₃ p
  calc KP U x y ≤ KP U p y + (c₁ : ENat) := h1
    _ ≤ (KPPlain U p + (c₂ : ENat)) + (c₁ : ENat) := by gcongr
    _ ≤ ((p.length + 2 * (Nat.bits p.length).length + (c₃ : ENat)) + (c₂ : ENat))
          + (c₁ : ENat) := by gcongr
    _ = ((k + 2 * (Nat.bits k).length + (c₁ + c₂ + c₃) : ℕ) : ENat) := by
        rw [hpk]; push_cast; ring

/-- **Gács Theorem 1.6.2, second half, unconditional.** With `k = C_V(x)`,
`K_U(x) ≤ k + 2 log k + c`. -/
theorem KPPlain_le_plainK_add_log (U V : Map) (hU : IsOptimalPrefixConditional U)
    (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (k : ℕ), (k : ENat) = plainK V x →
      KPPlain U x ≤ ((k + 2 * (Nat.bits k).length + c : ℕ) : ENat) := by
  obtain ⟨c, hc⟩ := KP_le_condK_add_log U V hU hV
  exact ⟨c, fun x k hk ↦ hc x [] k hk⟩

/-- **Gács Theorem 1.6.2.** `C ≤⁺ K ≤⁺ C + 2 log C`: prefix complexity lies between
plain complexity and plain complexity plus a logarithmic term. Both bounds are stated
with one constant, and with `k` the natural-number value of `C_V(x)`. -/
theorem plainK_le_KPPlain_le_plainK_add_log (U V : Map) (hU : IsOptimalPrefixConditional U)
    (hV : isOptimalConditional V) :
    ∃ c : ℕ, ∀ (x : BitString) (k : ℕ), (k : ENat) = plainK V x →
      plainK V x ≤ KPPlain U x + (c : ENat) ∧
      KPPlain U x ≤ ((k + 2 * (Nat.bits k).length + c : ℕ) : ENat) := by
  obtain ⟨c₁, h₁⟩ := plainK_le_KPPlain V U hV hU.isPrefixDecompressor
  obtain ⟨c₂, h₂⟩ := KPPlain_le_plainK_add_log U V hU hV
  refine ⟨c₁ + c₂, fun x k hk ↦ ⟨?_, ?_⟩⟩
  · exact (h₁ x).trans (by gcongr; exact_mod_cast Nat.le_add_right c₁ c₂)
  · exact (h₂ x k hk).trans (by exact_mod_cast Nat.add_le_add_left (Nat.le_add_left c₂ c₁) _)

end Kolmogorov
