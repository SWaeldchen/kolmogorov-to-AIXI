/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.ComplexityLevels
import KolmogorovMathlib.AlgorithmicStatistics.CodedComputability
import KolmogorovMathlib.AlgorithmicStatistics.Selector
import KolmogorovMathlib.Foundation.UnboundedSearch

/-!
# Fuel-bounded evaluation, fuel-bounded complexity, and the certificate machine

Theorem 1.7.4 (Solovay) needs a *computable* stand-in for `K`. Gács uses
time-bounded complexity `K(n; t)` over a Turing machine with linear simulation
overhead. Here "time" is the fuel of `Code.evaln`, and no overhead assumption is
needed: a search horizon only has to be *computable*, which `Computable.natFind`
supplies whenever the searched predicate is decidable and always satisfiable.

## Contents

* `evalFuel c k p` — the output of the code `c` for `U` on program `p` within fuel `k`,
  decoded; with soundness, completeness and monotonicity in `k` against `produces`.
* `trivBound c₀ z = 3·|z| + c₀` — a computable upper bound on `K(z)`, valid once `c₀`
  is chosen from `KPPlain_le_length_add_log`.
* `KFuel c₀ c (k, z)` — the least length of a program producing `z` within fuel `k`,
  or `trivBound c₀ z` if none is found. Computable; always `≥ K(z)`; `≤ |p|` for any
  program `p` found within the fuel.
* `haltFuel c p` — the least fuel at which `U` halts on `p`, as a `Part ℕ`.
* `certMap c U` — the **certificate machine**: on `p` it outputs
  `pairCode (U p) (natCode (haltFuel c p))`, the output together with the stage at
  which the program halted. It is a prefix decompressor whenever `U` is.

The code `c` for `U` and the hypothesis `hc` tying `c.eval` to `U` are exactly those
produced by `Code.exists_code`, as in `PaddingMachineComputable`.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-! ### Fuel-bounded evaluation -/

/-- The decoded output of `c` on `(p, [])` within fuel `k`, if any. -/
def evalFuel (c : Code) (k : ℕ) (p : BitString) : Option BitString :=
  (Code.evaln k c (Encodable.encode (p, ([] : BitString)))).bind
    (fun e ↦ (Encodable.decode e : Option BitString))

/-- `evalFuel` is primitive recursive in `(k, p)`. -/
theorem evalFuel_primrec (c : Code) :
    Primrec (fun q : ℕ × BitString ↦ evalFuel c q.1 q.2) := by
  have h1 : Primrec (fun q : ℕ × BitString ↦
      Code.evaln q.1 c (Encodable.encode (q.2, ([] : BitString)))) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair Primrec.fst (Primrec.const c))
        (Primrec.encode.comp (Primrec.pair Primrec.snd (Primrec.const ([] : BitString)))))
  have h2 : Primrec₂ (fun (_ : ℕ × BitString) (e : ℕ) ↦ (Encodable.decode e : Option BitString)) :=
    (Primrec.decode.comp Primrec.snd).to₂
  exact (Primrec.option_bind h1 h2).of_eq (fun q ↦ rfl)

/-- **Soundness.** A fuel-bounded output is a genuine output of `U`. -/
theorem evalFuel_sound {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {k : ℕ} {p z : BitString} (h : evalFuel c k p = some z) : produces U p [] z := by
  unfold evalFuel at h
  rw [Option.bind_eq_some_iff] at h
  obtain ⟨e, he, hdec⟩ := h
  have hev : e ∈ c.eval (Encodable.encode (p, ([] : BitString))) :=
    Nat.Partrec.Code.evaln_sound he
  rw [hc, Part.mem_bind_iff] at hev
  obtain ⟨a, ha, hea⟩ := hev
  rw [Part.mem_ofOption, Encodable.encodek] at ha
  have ha' := Option.some_inj.mp (Option.mem_def.mp ha)
  subst ha'
  obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).mp hea
  rw [Encodable.encodek] at hdec
  have hbz := Option.some_inj.mp hdec
  subst hbz
  exact hb

/-- **Completeness.** Every genuine output appears at some fuel. -/
theorem evalFuel_complete {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {p z : BitString} (h : produces U p [] z) : ∃ k, evalFuel c k p = some z := by
  have hmem : Encodable.encode z ∈ c.eval (Encodable.encode (p, ([] : BitString))) := by
    rw [hc]; simp only [Part.mem_bind_iff]
    exact ⟨(p, ([] : BitString)), by simp [Encodable.encodek],
      Part.mem_map Encodable.encode h⟩
  obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hmem
  refine ⟨k, ?_⟩
  unfold evalFuel
  rw [Option.mem_def.mp hk]
  simp [Encodable.encodek]

/-- **Monotonicity in the fuel.** -/
theorem evalFuel_mono (c : Code) {k k' : ℕ} (hk : k ≤ k') {p z : BitString}
    (h : evalFuel c k p = some z) : evalFuel c k' p = some z := by
  unfold evalFuel at h ⊢
  rw [Option.bind_eq_some_iff] at h ⊢
  obtain ⟨e, he, hdec⟩ := h
  exact ⟨e, Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hk (Option.mem_def.mpr he)), hdec⟩

/-- A fuel-bounded output, if it exists, is the unique output of `U`. -/
theorem evalFuel_eq_some_of_isSome {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {k : ℕ} {p x : BitString} (hx : produces U p [] x)
    (h : (evalFuel c k p).isSome = true) : evalFuel c k p = some x := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp h
  have := evalFuel_sound hc hz
  rw [hz, Part.mem_unique this hx]

/-- Fuel-bounded halting is genuine halting. -/
theorem dom_of_evalFuel_isSome {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {k : ℕ} {p : BitString} (h : (evalFuel c k p).isSome = true) : (U (p, [])).Dom := by
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.mp h
  exact Part.dom_iff_mem.mpr ⟨z, evalFuel_sound hc hz⟩

/-- Genuine halting appears at some fuel. -/
theorem exists_evalFuel_isSome_of_dom {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {p : BitString} (h : (U (p, [])).Dom) : ∃ k, (evalFuel c k p).isSome = true := by
  obtain ⟨z, hz⟩ := Part.dom_iff_mem.mp h
  obtain ⟨k, hk⟩ := evalFuel_complete hc hz
  exact ⟨k, by rw [hk]; rfl⟩

/-! ### Enumerating all strings up to a length -/

/-- All strings of length at most `B`. -/
def allUpTo (B : ℕ) : List BitString := ((List.range (B + 1)).map allStrings).flatten

/-- Membership in `allUpTo B` is having length at most `B`. -/
theorem mem_allUpTo {B : ℕ} {p : BitString} : p ∈ allUpTo B ↔ p.length ≤ B := by
  unfold allUpTo
  simp only [List.mem_flatten, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨l, ⟨n, hn, rfl⟩, hp⟩
    rw [(mem_allStrings _ _).mp hp]; omega
  · intro h
    exact ⟨allStrings p.length, ⟨p.length, by omega, rfl⟩, (mem_allStrings _ _).mpr rfl⟩

/-- `allUpTo` is primitive recursive. -/
theorem allUpTo_primrec : Primrec allUpTo := by
  have h : Primrec (fun B : ℕ ↦ (List.range (B + 1)).map allStrings) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.succ)
      (CodedFiniteDistribution.allStrings_primrec.comp Primrec.snd).to₂
  exact (Primrec.list_flatten.comp h).of_eq (fun B ↦ rfl)

/-! ### Decidable equality as a primitive recursive predicate -/

/-- Equality on `ℕ`, as a `Bool`, is primitive recursive. -/
theorem natEq_primrec : Primrec (fun p : ℕ × ℕ ↦ decide (p.1 = p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.eq : PrimrecRel (@Eq ℕ))
  exact Primrec.of_eq h (fun p ↦ by congr)

/-- Equality on `Option BitString`, as a `Bool`, is primitive recursive. -/
theorem optBitStringEq_primrec :
    Primrec (fun p : Option BitString × Option BitString ↦ decide (p.1 = p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.eq : PrimrecRel (@Eq (Option BitString)))
  exact Primrec.of_eq h (fun p ↦ by congr)

/-! ### A computable upper bound on `K` -/

/-- The trivial bound `3·|z| + c₀`. -/
def trivBound (c₀ : ℕ) (z : BitString) : ℕ := 3 * z.length + c₀

/-- `trivBound` is primitive recursive. -/
theorem trivBound_primrec (c₀ : ℕ) : Primrec (trivBound c₀) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 3) Primrec.list_length)
    (Primrec.const c₀)

/-- The bit-length of a number is at most the number. -/
theorem bits_length_le (n : ℕ) : (Nat.bits n).length ≤ n := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr Nat.lt_two_pow_self

/-- `K(z) ≤ trivBound c₀ z`, once `c₀` is the constant of `KPPlain_le_length_add_log`. -/
theorem KPPlain_le_trivBound (U : Map) (hU : IsOptimalPrefixConditional U) :
    ∃ c₀ : ℕ, ∀ z : BitString, KPPlain U z ≤ (trivBound c₀ z : ENat) := by
  obtain ⟨c₀, hc₀⟩ := KPPlain_le_length_add_log U hU
  refine ⟨c₀, fun z ↦ ?_⟩
  have h1 := hc₀ z
  have h2 : z.length + 2 * (Nat.bits z.length).length + c₀ ≤ trivBound c₀ z := by
    unfold trivBound
    have := bits_length_le z.length
    omega
  calc KPPlain U z ≤ ((z.length + 2 * (Nat.bits z.length).length + c₀ : ℕ) : ENat) := by
        exact_mod_cast h1
    _ ≤ (trivBound c₀ z : ENat) := by exact_mod_cast h2

/-! ### Fuel-bounded complexity -/

/-- The search predicate for `KFuel`: either `ℓ` is the fallback bound, or some program
of length `ℓ` produces `z` within fuel `k`. -/
def kfuelPred (c₀ : ℕ) (c : Code) (q : ℕ × BitString) (ℓ : ℕ) : Bool :=
  decide (ℓ = trivBound c₀ q.2) ||
    (allStrings ℓ).any (fun p ↦ decide (evalFuel c q.1 p = some q.2))

/-- The search always succeeds, at the fallback bound. -/
theorem kfuel_exists (c₀ : ℕ) (c : Code) (q : ℕ × BitString) :
    ∃ ℓ, kfuelPred c₀ c q ℓ = true :=
  ⟨trivBound c₀ q.2, by simp [kfuelPred]⟩

/-- **Fuel-bounded complexity**: the least program length producing `z` within fuel
`k`, or `trivBound c₀ z` if none. -/
def KFuel (c₀ : ℕ) (c : Code) (q : ℕ × BitString) : ℕ := Nat.find (kfuel_exists c₀ c q)

/-- The search predicate is primitive recursive. -/
theorem kfuelPred_primrec (c₀ : ℕ) (c : Code) :
    Primrec (fun r : (ℕ × BitString) × ℕ ↦ kfuelPred c₀ c r.1 r.2) := by
  have hA : Primrec (fun r : (ℕ × BitString) × ℕ ↦ decide (r.2 = trivBound c₀ r.1.2)) :=
    (natEq_primrec.comp (Primrec.pair Primrec.snd
      ((trivBound_primrec c₀).comp (Primrec.snd.comp Primrec.fst)))).of_eq (fun r ↦ rfl)
  have hB : Primrec (fun r : (ℕ × BitString) × ℕ ↦
      (allStrings r.2).any (fun p ↦ decide (evalFuel c r.1.1 p = some r.1.2))) := by
    refine list_any_primrec (f := fun r : (ℕ × BitString) × ℕ ↦ allStrings r.2)
      (p := fun r q ↦ decide (evalFuel c r.1.1 q = some r.1.2))
      (CodedFiniteDistribution.allStrings_primrec.comp Primrec.snd) ?_
    have : Primrec (fun a : ((ℕ × BitString) × ℕ) × BitString ↦
        decide (evalFuel c a.1.1.1 a.2 = some a.1.1.2)) :=
      (optBitStringEq_primrec.comp (Primrec.pair
        ((evalFuel_primrec c).comp
          (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
        (Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))).of_eq
        (fun a ↦ rfl)
    exact this.to₂
  exact (Primrec.cond hA (Primrec.const true) hB).of_eq (fun r ↦ by
    unfold kfuelPred
    cases decide (r.2 = trivBound c₀ r.1.2) <;> rfl)

/-- **`KFuel` is computable.** -/
theorem KFuel_computable (c₀ : ℕ) (c : Code) : Computable (KFuel c₀ c) := by
  have hP : Computable (fun p : (ℕ × BitString) × ℕ ↦ decide (kfuelPred c₀ c p.1 p.2 = true)) :=
    ((kfuelPred_primrec c₀ c).to_comp).of_eq (fun p ↦ by simp)
  exact Computable.natFind (P := fun q ℓ ↦ kfuelPred c₀ c q ℓ = true) hP (kfuel_exists c₀ c)

/-- `KFuel` never exceeds the fallback bound. -/
theorem KFuel_le_trivBound (c₀ : ℕ) (c : Code) (q : ℕ × BitString) :
    KFuel c₀ c q ≤ trivBound c₀ q.2 :=
  Nat.find_min' _ (by simp [kfuelPred])

/-- **`K ≤ KFuel`.** The fuel-bounded complexity is the length of a genuine program
or the fallback bound, either of which dominates `K`. -/
theorem KPPlain_le_KFuel (U : Map) {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {c₀ : ℕ} (hbound : ∀ z, KPPlain U z ≤ (trivBound c₀ z : ENat))
    (q : ℕ × BitString) : KPPlain U q.2 ≤ (KFuel c₀ c q : ENat) := by
  have hspec : kfuelPred c₀ c q (KFuel c₀ c q) = true := Nat.find_spec (kfuel_exists c₀ c q)
  unfold kfuelPred at hspec
  rw [Bool.or_eq_true_iff, decide_eq_true_eq, List.any_eq_true] at hspec
  rcases hspec with h | ⟨p, hp, hpz⟩
  · rw [h]; exact hbound q.2
  · rw [decide_eq_true_eq] at hpz
    have hprod := evalFuel_sound hc hpz
    have hlen := (mem_allStrings _ _).mp hp
    calc KPPlain U q.2 ≤ (p.length : ENat) := KP_le_programLength_of_produces hprod
      _ = (KFuel c₀ c q : ENat) := by rw [hlen]

/-- **A found program bounds `KFuel`.** -/
theorem KFuel_le_of_evalFuel (c₀ : ℕ) (c : Code) {k : ℕ} {p z : BitString}
    (h : evalFuel c k p = some z) : KFuel c₀ c (k, z) ≤ p.length := by
  apply Nat.find_min'
  unfold kfuelPred
  rw [Bool.or_eq_true_iff, List.any_eq_true]
  exact Or.inr ⟨p, (mem_allStrings _ _).mpr rfl, by simp [h]⟩

/-! ### The least halting fuel and the certificate machine -/

/-- The least fuel at which `U` halts on `p`, as a partial value. -/
def haltFuel (c : Code) (p : BitString) : Part ℕ :=
  Nat.rfind (fun k ↦ Part.some (evalFuel c k p).isSome)

/-- `haltFuel` halts exactly when `U` does. -/
theorem haltFuel_dom_iff {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    (p : BitString) : (haltFuel c p).Dom ↔ (U (p, [])).Dom := by
  unfold haltFuel
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨k, hk, -⟩
    rw [Part.mem_some_iff] at hk
    exact dom_of_evalFuel_isSome hc hk.symm
  · intro h
    obtain ⟨k, hk⟩ := exists_evalFuel_isSome_of_dom hc h
    exact ⟨k, by rw [Part.mem_some_iff, hk], fun {m} _ ↦ Part.some_dom _⟩

/-- `haltFuel` is partial recursive in `p`. -/
theorem haltFuel_partrec (c : Code) : Partrec (haltFuel c) := by
  have hp : Partrec₂ (fun (p : BitString) (k : ℕ) ↦
      (Part.some (evalFuel c k p).isSome : Part Bool)) := by
    have : Computable (fun q : BitString × ℕ ↦ (evalFuel c q.2 q.1).isSome) :=
      (Primrec.option_isSome.comp
        ((evalFuel_primrec c).comp (Primrec.pair Primrec.snd Primrec.fst))).to_comp
    exact this
  exact (Partrec.rfind hp).of_eq (fun p ↦ rfl)

/-- **The certificate machine.** Run `U` on the program; if it halts at least fuel `k`
with output `z`, output the pair `⟨z, k⟩`. -/
def certMap (c : Code) (U : Map) : Map := fun pr ↦
  (haltFuel c pr.1).bind (fun k ↦ (U (pr.1, [])).map (fun z ↦ pairCode z (natCode k)))

/-- Membership characterisation of the certificate machine. -/
theorem produces_certMap_iff (c : Code) (U : Map) (p y w : BitString) :
    produces (certMap c U) p y w ↔
      ∃ k z, k ∈ haltFuel c p ∧ produces U p [] z ∧ pairCode z (natCode k) = w := by
  change w ∈ (haltFuel c p).bind (fun k ↦ (U (p, [])).map (fun z ↦ pairCode z (natCode k))) ↔ _
  rw [Part.mem_bind_iff]
  constructor
  · rintro ⟨k, hk, hw⟩
    obtain ⟨z, hz, rfl⟩ := (Part.mem_map_iff _).mp hw
    exact ⟨k, z, hk, hz, rfl⟩
  · rintro ⟨k, z, hk, hz, rfl⟩
    exact ⟨k, hk, Part.mem_map _ hz⟩

/-- The certificate machine halts exactly when `U` does (in the empty context). -/
theorem domainAt_certMap {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    (y : BitString) : domainAt (certMap c U) y = domainAt U [] := by
  ext p
  simp only [domainAt, Set.mem_setOf_eq, certMap]
  rw [Part.bind_dom]
  constructor
  · rintro ⟨hk, -⟩
    exact (haltFuel_dom_iff hc p).mp hk
  · intro h
    exact ⟨(haltFuel_dom_iff hc p).mpr h, h⟩

/-- **The certificate machine is a prefix decompressor** whenever `U` is. -/
theorem certMap_isPrefixDecompressor {U : Map} (hU : IsPrefixDecompressor U) {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a))) :
    IsPrefixDecompressor (certMap c U) := by
  refine ⟨?_, ?_⟩
  · have hf : Partrec (fun pr : BitString × BitString ↦ haltFuel c pr.1) :=
      (haltFuel_partrec c).comp Computable.fst
    have hg : Partrec₂ (fun (pr : BitString × BitString) (k : ℕ) ↦
        (U (pr.1, [])).map (fun z ↦ pairCode z (natCode k))) := by
      have hU' : Partrec (fun r : (BitString × BitString) × ℕ ↦ U (r.1.1, [])) :=
        hU.isDecompressor.comp
          (Computable.pair (Computable.fst.comp Computable.fst) (Computable.const []))
      have hpost : Computable₂ (fun (r : (BitString × BitString) × ℕ) (z : BitString) ↦
          pairCode z (natCode r.2)) :=
        (pairCode_primrec.comp Primrec.snd
          (natCode_primrec.comp (Primrec.snd.comp Primrec.fst))).to_comp.to₂
      exact (hU'.map hpost).of_eq (fun r ↦ rfl)
    exact (Partrec.bind hf hg).of_eq (fun pr ↦ rfl)
  · intro y
    rw [domainAt_certMap hc]
    exact hU.isPrefixMachine []

end Kolmogorov
