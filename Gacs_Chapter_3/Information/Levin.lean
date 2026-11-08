/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Information.Identities
import Gacs_Chapter_3.CompComp.SometimesComplex

/-!
# Gács Theorem 3.1.6 (Levin): `I(x : y)` is not even asymptotically symmetric

Write `k = K(x)` (as the string `natCode k`) and `asym(u, v) = I(u : v) − I(v : u)`.

* `info_xStar_K`: `I(x* : K(x)) ≥ K(K(x)) − c`, since `K(x)` is the length of `x*`;
* `info_K_xStar`: `I(K(x) : x*) =⁺ I(K(x) : x)`, since `x* ≍ ⟨x, K(x)⟩`;
* with Theorem 3.1.5 (`CompComp.exists_KK_ge`) choose `x` of length `n` with
  `K(K(x) ∣ x) ≥ log n − log log n − c`, so `I(x : K(x)) ≤ K(K(x)) − log n + log log n + c`.

Hence `asym(x*, K(x)) − asym(x, K(x)) ≥ log n − log log n − c` (`asym_gap`), and therefore
**one of the two pairs `(x, K(x))`, `(x*, K(x))` has asymmetry at least
`(log n − log log n − c) / 2`** (`levin_asymmetry`): symmetry fails by an amount that grows
with `n`, on objects of size about `n`.
-/

namespace Kolmogorov.Information

variable {U : Map}

/-- `I(x* : K(x)) ≥ K(K(x)) − c`: `K(K(x) ∣ x*) ≤ c`. -/
theorem Kc_K_xStar (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, Kc U (natCode (Ku U x)) (xStar U x) ≤ c := by
  have hg : Computable (fun q : BitString ↦ natCode q.length) :=
    natCode_computable.comp Computable.list_length
  obtain ⟨c₁, h₁⟩ := Kc_map hU hg
  obtain ⟨c₂, h₂⟩ := Kc_self hU
  refine ⟨c₁ + c₂, fun x ↦ ?_⟩
  have a := h₁ (xStar U x) (xStar U x)
  have b := h₂ (xStar U x)
  rw [(xStar_spec hU x).2] at a
  omega

/-- `I(K(x) : x*) =⁺ I(K(x) : x)`. -/
theorem info_K_xStar (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ x, Info U (natCode (Ku U x)) (xStar U x) ≤ Info U (natCode (Ku U x)) x + c ∧
      Info U (natCode (Ku U x)) x ≤ Info U (natCode (Ku U x)) (xStar U x) + c := by
  obtain ⟨c₁, h₁⟩ := Ku_xk_xStar hU
  -- `K(x ∣ k) ≤ K(x* ∣ k) + c`: run `U` on `x*`
  have hU' : Partrec (fun p : BitString × BitString ↦ U (p.1, ([] : BitString))) :=
    hU.isDecompressor.comp (Computable.pair Computable.fst (Computable.const []))
  obtain ⟨c₂, h₂⟩ := Kc_map_partrec hU (fun _ q ↦ U (q, [])) hU'
  -- `K(x* ∣ k) ≤ K(x ∣ k) + c`: `K(⟨x, k⟩ ∣ k) ≤ K(x ∣ k) + c`, then `x*` from `⟨x, k⟩`
  obtain ⟨c₃, h₃⟩ := Kc_map_partrec hU (fun y q ↦ Part.some (pairCode q y))
    (pairCode_computable.comp (Computable.pair Computable.fst Computable.snd)).partrec
  obtain ⟨c₄, h₄⟩ := xStar_le_xk hU
  obtain ⟨c₅, h₅⟩ := Kc_triangle hU
  refine ⟨c₁ + c₂ + c₃ + c₄ + c₅, fun x ↦ ?_⟩
  set k := natCode (Ku U x) with hk
  have a := h₁ x
  have b := h₂ (xStar U x) x k (xStar_spec hU x).1
  have d := h₃ x (pairCode x k) k (Part.mem_some _)
  have e := h₄ x
  have f := h₅ k (pairCode x k) (xStar U x)
  unfold xk at e
  rw [← hk] at e
  unfold Info
  obtain ⟨a1, a2, a3, a4⟩ := a
  constructor <;> push_cast <;> omega

/-- The two asymmetries differ by about `log n − log log n` on the strings of Theorem 3.1.5:
`asym(x*, K(x)) − asym(x, K(x)) ≥ log n − log log n − c`. -/
theorem asym_gap (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ x : BitString, x.length = n ∧
      (Nat.log 2 n : ℤ) - Nat.log 2 (Nat.log 2 n) - c ≤
        (Info U (xStar U x) (natCode (Ku U x)) - Info U (natCode (Ku U x)) (xStar U x)) -
          (Info U x (natCode (Ku U x)) - Info U (natCode (Ku U x)) x) := by
  obtain ⟨c₀, h₀⟩ := CompComp.exists_KK_ge hU
  obtain ⟨c₁, h₁⟩ := Kc_K_xStar hU
  obtain ⟨c₂, h₂⟩ := info_K_xStar hU
  refine ⟨c₀ + c₁ + c₂, fun n ↦ ?_⟩
  obtain ⟨x, hx, hK⟩ := h₀ n
  refine ⟨x, hx, ?_⟩
  have a := h₁ x
  have b := (h₂ x).1
  have hK' : (Nat.log 2 n : ℤ) - Nat.log 2 (Nat.log 2 n) - c₀ ≤ Kc U (natCode (Ku U x)) x := hK
  unfold Info at b ⊢
  push_cast
  omega

/-- **Gács Theorem 3.1.6 (Levin).** `I(x : y)` is not even asymptotically symmetric: for every
`n` there is `x` of length `n` such that the pair `(x, K(x))` or the pair `(x*, K(x))` has
`|I(u : v) − I(v : u)| ≥ (log n − log log n − c) / 2`. -/
theorem levin_asymmetry (hU : IsOptimalPrefixConditional U) :
    ∃ c : ℕ, ∀ n : ℕ, ∃ x : BitString, x.length = n ∧
      (Nat.log 2 n : ℤ) - Nat.log 2 (Nat.log 2 n) - c ≤
        2 * max |Info U x (natCode (Ku U x)) - Info U (natCode (Ku U x)) x|
          |Info U (xStar U x) (natCode (Ku U x)) - Info U (natCode (Ku U x)) (xStar U x)| := by
  obtain ⟨c, hc⟩ := asym_gap hU
  refine ⟨c, fun n ↦ ?_⟩
  obtain ⟨x, hx, h⟩ := hc n
  refine ⟨x, hx, ?_⟩
  set A := Info U (xStar U x) (natCode (Ku U x)) - Info U (natCode (Ku U x)) (xStar U x)
  set B := Info U x (natCode (Ku U x)) - Info U (natCode (Ku U x)) x
  have hA := le_abs_self A
  have hB := neg_abs_le B
  have h1 := le_max_left |B| |A|
  have h2 := le_max_right |B| |A|
  linarith

end Kolmogorov.Information
