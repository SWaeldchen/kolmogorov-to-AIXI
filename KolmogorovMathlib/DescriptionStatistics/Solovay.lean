/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import KolmogorovMathlib.DescriptionStatistics.FuelComplexity

/-!
# Theorem 1.7.4 (Solovay): a computable upper bound on `K` that is exact infinitely often

There is a computable `G` with `K ≤ G` everywhere and `G = K` infinitely often.

## The idea

Fix a code `c` for `U`. For an object `x` with shortest program `p`, let `s` be the
least fuel at which `p` halts. The **certificate pair** `⟨x, s⟩` carries its own
verification: knowing `s`, one can compute a fuel `fuelBound (x, s)` by which every
program for `x` that halts within fuel `s`, once tagged for the certificate machine,
has itself halted. Searching for programs of `⟨x, s⟩` up to that fuel finds the tagged
`p`, of length `K(x) + |tag|`, so the fuel-bounded complexity of `⟨x, s⟩` is within a
constant of the true `K(⟨x, s⟩)`. Off the certificate pairs the estimate is still an
upper bound. That is `solovayF`.

A pigeonhole then finishes: the difference `F − K` takes some value `d₀` infinitely
often; subtract the least such `d₀` and repair the finitely many points where the
difference was smaller.

## Why no machine-model assumption is needed

Gács bounds the search by `c₀ · t` and needs a universal machine with linear time
overhead to know that bound is computable. Here the bound is `fuelBound`, computable by
`Computable.natFind` because each candidate program halts and there are finitely many.
Nothing about how fuel relates across machines is used.
-/

namespace Kolmogorov

open Nat.Partrec (Code)

/-! ### A uniform bound over a finite list -/

/-- A monotone family of properties, each eventually true on every element of a list, is
uniformly true on the list from some index on. -/
theorem exists_uniform_bound {β : Type*} (L : List β) (ψ : ℕ → β → Prop)
    (hmono : ∀ K K' b, K ≤ K' → ψ K b → ψ K' b)
    (h : ∀ b ∈ L, ∃ K, ψ K b) : ∃ K, ∀ b ∈ L, ψ K b := by
  induction L with
  | nil => exact ⟨0, fun b hb ↦ by simp at hb⟩
  | cons a L ih =>
    obtain ⟨K₁, hK₁⟩ := h a (by simp)
    obtain ⟨K₂, hK₂⟩ := ih (fun b hb ↦ h b (by simp [hb]))
    refine ⟨max K₁ K₂, fun b hb ↦ ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hmono _ _ _ (le_max_left _ _) hK₁
    · exact hmono _ _ _ (le_max_right _ _) (hK₂ b hb)

/-! ### The fuel bound -/

/-- The failure test: some program of length at most `trivBound c₀ x` that produces `x`
within fuel `s` has, after tagging, *not* yet halted within fuel `K`. -/
def fbBad (c₀ : ℕ) (c : Code) (tag : BitString) (a : BitString × ℕ) (K : ℕ) : Bool :=
  (allUpTo (trivBound c₀ a.1)).any
    (fun p ↦ decide (evalFuel c a.2 p = some a.1) && !(evalFuel c K (tag ++ p)).isSome)

/-- The failure test is `false` exactly when every relevant tagged program has halted. -/
theorem fbBad_eq_false_iff {c₀ : ℕ} {c : Code} {tag : BitString} {a : BitString × ℕ} {K : ℕ} :
    fbBad c₀ c tag a K = false ↔
      ∀ p ∈ allUpTo (trivBound c₀ a.1),
        evalFuel c a.2 p = some a.1 → (evalFuel c K (tag ++ p)).isSome = true := by
  unfold fbBad
  rw [List.any_eq_false]
  constructor
  · intro h p hp hev
    have := h p hp
    exact Option.isSome_iff_ne_none.mpr (by simpa [hev] using this)
  · intro h p hp
    by_cases hev : evalFuel c a.2 p = some a.1
    · simp [hev, h p hp hev]
    · simp [hev]

/-- **The uniform fuel exists.** Every candidate program halts on `U`, so its tagged
version halts too, at some fuel; take the largest over the finitely many candidates. -/
theorem fbBad_exists_false {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    (s : PrefixPrependSimulation U (certMap c U)) (c₀ : ℕ) (a : BitString × ℕ) :
    ∃ K, fbBad c₀ c s.tag a K = false := by
  have hψ : ∃ K, ∀ p ∈ allUpTo (trivBound c₀ a.1),
      (evalFuel c a.2 p = some a.1 → (evalFuel c K (s.tag ++ p)).isSome = true) := by
    apply exists_uniform_bound
    · intro K K' p hKK' hψ hev
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (hψ hev)
      rw [evalFuel_mono c hKK' hw]; rfl
    · intro p _
      by_cases hev : evalFuel c a.2 p = some a.1
      · have hdom : (U (p, [])).Dom := Part.dom_iff_mem.mpr ⟨_, evalFuel_sound hc hev⟩
        have hcert : (certMap c U (p, [])).Dom := by
          change p ∈ domainAt (certMap c U) []
          rw [domainAt_certMap hc]
          exact hdom
        obtain ⟨w, hw⟩ := Part.dom_iff_mem.mp hcert
        have hsim : produces U (s.tag ++ p) [] w := s.simulates p [] w hw
        obtain ⟨K, hK⟩ := exists_evalFuel_isSome_of_dom hc (Part.dom_iff_mem.mpr ⟨w, hsim⟩)
        exact ⟨K, fun _ ↦ hK⟩
      · exact ⟨0, fun h ↦ absurd h hev⟩
  obtain ⟨K, hK⟩ := hψ
  exact ⟨K, fbBad_eq_false_iff.mpr hK⟩

/-- **The computable fuel bound.** -/
def fuelBound (c₀ : ℕ) (c : Code) (tag : BitString)
    (hex : ∀ a, ∃ K, fbBad c₀ c tag a K = false) (a : BitString × ℕ) : ℕ :=
  Nat.find (hex a)

/-- At the fuel bound, every relevant tagged program has halted. -/
theorem fuelBound_spec (c₀ : ℕ) (c : Code) (tag : BitString)
    (hex : ∀ a, ∃ K, fbBad c₀ c tag a K = false) (a : BitString × ℕ) :
    ∀ p ∈ allUpTo (trivBound c₀ a.1), evalFuel c a.2 p = some a.1 →
      (evalFuel c (fuelBound c₀ c tag hex a) (tag ++ p)).isSome = true :=
  fbBad_eq_false_iff.mp (Nat.find_spec (hex a))

/-- The failure test is primitive recursive. -/
theorem fbBad_primrec (c₀ : ℕ) (c : Code) (tag : BitString) :
    Primrec (fun r : (BitString × ℕ) × ℕ ↦ fbBad c₀ c tag r.1 r.2) := by
  refine list_any_primrec (f := fun r : (BitString × ℕ) × ℕ ↦ allUpTo (trivBound c₀ r.1.1))
    (p := fun r q ↦
      decide (evalFuel c r.1.2 q = some r.1.1) && !(evalFuel c r.2 (tag ++ q)).isSome)
    (allUpTo_primrec.comp ((trivBound_primrec c₀).comp (Primrec.fst.comp Primrec.fst))) ?_
  have hA : Primrec (fun a : ((BitString × ℕ) × ℕ) × BitString ↦
      decide (evalFuel c a.1.1.2 a.2 = some a.1.1.1)) :=
    (optBitStringEq_primrec.comp (Primrec.pair
      ((evalFuel_primrec c).comp
        (Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
      (Primrec.option_some.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))))).of_eq
      (fun a ↦ rfl)
  have hB : Primrec (fun a : ((BitString × ℕ) × ℕ) × BitString ↦
      !(evalFuel c a.1.2 (tag ++ a.2)).isSome) :=
    Primrec.not.comp (Primrec.option_isSome.comp ((evalFuel_primrec c).comp
      (Primrec.pair (Primrec.snd.comp Primrec.fst)
        (Primrec.list_append.comp (Primrec.const tag) Primrec.snd))))
  have hbc : ∀ x y : Bool, cond x y false = (x && y) := by decide
  exact ((Primrec.cond hA hB (Primrec.const false)).of_eq (fun a ↦ hbc _ _)).to₂

/-- **The fuel bound is computable.** -/
theorem fuelBound_computable (c₀ : ℕ) (c : Code) (tag : BitString)
    (hex : ∀ a, ∃ K, fbBad c₀ c tag a K = false) :
    Computable (fuelBound c₀ c tag hex) := by
  have hP : Computable (fun p : (BitString × ℕ) × ℕ ↦ decide (fbBad c₀ c tag p.1 p.2 = false)) :=
    ((Primrec.not.comp (fbBad_primrec c₀ c tag)).to_comp).of_eq (fun p ↦ by
      cases fbBad c₀ c tag p.1 p.2 <;> simp)
  exact Computable.natFind (P := fun a K ↦ fbBad c₀ c tag a K = false) hP hex

/-! ### The computable estimate -/

/-- Read the stage off the second component of a pair (unary code). -/
def stageOf (z : BitString) : ℕ := (decodeSecond z).length - 1

/-- On a certificate pair, `stageOf` returns the stage. -/
theorem stageOf_pairCode (x : BitString) (s : ℕ) : stageOf (pairCode x (natCode s)) = s := by
  unfold stageOf
  rw [decodeSecond_pairCode, length_natCode]
  omega

/-- `stageOf` is computable. -/
theorem stageOf_computable : Computable stageOf :=
  (Primrec.nat_sub.comp Primrec.list_length (Primrec.const 1)).to_comp.comp decodeSecond_computable

/-- **Solovay's estimate.** On `z`, read off the putative pair `(x, s)` and return the
fuel-bounded complexity of `z` at fuel `fuelBound (x, s)`. -/
def solovayF (c₀ : ℕ) (c : Code) (tag : BitString)
    (hex : ∀ a, ∃ K, fbBad c₀ c tag a K = false) (z : BitString) : ℕ :=
  KFuel c₀ c (fuelBound c₀ c tag hex (decodeFirst z, stageOf z), z)

/-- Solovay's estimate is computable. -/
theorem solovayF_computable (c₀ : ℕ) (c : Code) (tag : BitString)
    (hex : ∀ a, ∃ K, fbBad c₀ c tag a K = false) :
    Computable (solovayF c₀ c tag hex) :=
  (KFuel_computable c₀ c).comp (Computable.pair
    ((fuelBound_computable c₀ c tag hex).comp
      (Computable.pair decodeFirst_computable stageOf_computable))
    Computable.id)

/-- Solovay's estimate dominates `K` everywhere. -/
theorem KPPlain_le_solovayF (U : Map) {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {c₀ : ℕ} (hbound : ∀ z, KPPlain U z ≤ (trivBound c₀ z : ENat))
    (tag : BitString) (hex : ∀ a, ∃ K, fbBad c₀ c tag a K = false) (z : BitString) :
    KPPlain U z ≤ (solovayF c₀ c tag hex z : ENat) :=
  KPPlain_le_KFuel U hc hbound _

/-! ### The certificate pairs -/

/-- The shortest program of `x` halts at some fuel. -/
theorem settle_exists {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {x : BitString} (hx : KP U x [] ≠ ⊤) :
    ∃ k, (evalFuel c k (shortestProg U x)).isSome = true :=
  exists_evalFuel_isSome_of_dom hc (Part.dom_iff_mem.mpr ⟨x, (shortestProg_spec U hx).1⟩)

/-- **The settling stage** of `x`: the least fuel at which its shortest program halts. -/
noncomputable def settle {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {x : BitString} (hx : KP U x [] ≠ ⊤) : ℕ :=
  Nat.find (settle_exists hc hx)

/-- The settling stage is the value of `haltFuel` on the shortest program. -/
theorem settle_mem_haltFuel {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    {x : BitString} (hx : KP U x [] ≠ ⊤) :
    settle hc hx ∈ haltFuel c (shortestProg U x) := by
  unfold haltFuel
  rw [Nat.mem_rfind]
  refine ⟨?_, fun {m} hm ↦ ?_⟩
  · rw [Part.mem_some_iff]
    exact (Nat.find_spec (settle_exists hc hx)).symm
  · rw [Part.mem_some_iff]
    have h := Nat.find_min (settle_exists hc hx) hm
    have h' : (evalFuel c m (shortestProg U x)).isSome = false := by
      cases hh : (evalFuel c m (shortestProg U x)).isSome
      · rfl
      · exact absurd hh h
    exact h'.symm

/-- **The certificate pair** `⟨x, settle x⟩`. -/
noncomputable def certPair {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    (hfin : ∀ x : BitString, KP U x [] ≠ ⊤) (x : BitString) : BitString :=
  pairCode x (natCode (settle hc (hfin x)))

/-- Certificate pairs of distinct objects are distinct. -/
theorem certPair_injective {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    (hfin : ∀ x : BitString, KP U x [] ≠ ⊤) : Function.Injective (certPair hc hfin) := by
  intro x x' h
  have := congrArg decodeFirst h
  unfold certPair at this
  rwa [decodeFirst_pairCode, decodeFirst_pairCode] at this

/-- The tagged shortest program of `x` is a `U`-program for the certificate pair. -/
theorem produces_tag_shortestProg_certPair {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    (hfin : ∀ x : BitString, KP U x [] ≠ ⊤)
    (s : PrefixPrependSimulation U (certMap c U)) (x : BitString) :
    produces U (s.tag ++ shortestProg U x) [] (certPair hc hfin x) := by
  apply s.simulates
  rw [produces_certMap_iff]
  exact ⟨settle hc (hfin x), x, settle_mem_haltFuel hc (hfin x),
    (shortestProg_spec U (hfin x)).1, rfl⟩

/-- **The estimate is tight on certificate pairs**, up to the tag length:
`solovayF (certPair x) ≤ |tag| + K(x)`. -/
theorem solovayF_certPair_le {U : Map} {c : Code}
    (hc : c.eval = fun n ↦
      (Part.ofOption (Encodable.decode (α := BitString × BitString) n)).bind
        (fun a ↦ Part.map Encodable.encode (U a)))
    (hfin : ∀ x : BitString, KP U x [] ≠ ⊤)
    {c₀ : ℕ} (hbound : ∀ z, KPPlain U z ≤ (trivBound c₀ z : ENat))
    (s : PrefixPrependSimulation U (certMap c U))
    (hex : ∀ a, ∃ K, fbBad c₀ c s.tag a K = false) (x : BitString) :
    ((solovayF c₀ c s.tag hex (certPair hc hfin x) : ℕ) : ENat)
      ≤ (s.tag.length : ENat) + KPPlain U x := by
  set st := settle hc (hfin x) with hst
  set p := shortestProg U x with hp
  obtain ⟨hprod, hlen⟩ := shortestProg_spec U (hfin x)
  -- The shortest program is a candidate: short enough, and halting within fuel `st`.
  have hcand : p ∈ allUpTo (trivBound c₀ x) := by
    rw [mem_allUpTo]
    have h1 : (p.length : ENat) ≤ (trivBound c₀ x : ENat) := by
      rw [hlen]; exact hbound x
    exact_mod_cast h1
  have hev : evalFuel c st p = some x :=
    evalFuel_eq_some_of_isSome hc hprod (Nat.find_spec (settle_exists hc (hfin x)))
  -- So the tagged program has halted by the fuel bound, with the certificate pair as output.
  have hsome := fuelBound_spec c₀ c s.tag hex (x, st) p hcand hev
  have htag : evalFuel c (fuelBound c₀ c s.tag hex (x, st)) (s.tag ++ p)
      = some (certPair hc hfin x) :=
    evalFuel_eq_some_of_isSome hc (produces_tag_shortestProg_certPair hc hfin s x) hsome
  -- Hence the fuel-bounded complexity of the pair is at most `|tag ++ p|`.
  have hK : KFuel c₀ c (fuelBound c₀ c s.tag hex (x, st), certPair hc hfin x)
      ≤ (s.tag ++ p).length :=
    KFuel_le_of_evalFuel c₀ c htag
  have hF : solovayF c₀ c s.tag hex (certPair hc hfin x)
      = KFuel c₀ c (fuelBound c₀ c s.tag hex (x, st), certPair hc hfin x) := by
    unfold solovayF certPair
    rw [decodeFirst_pairCode, stageOf_pairCode]
  rw [hF]
  calc ((KFuel c₀ c (fuelBound c₀ c s.tag hex (x, st), certPair hc hfin x) : ℕ) : ENat)
      ≤ ((s.tag ++ p).length : ENat) := by exact_mod_cast hK
    _ = (s.tag.length : ENat) + (p.length : ENat) := by
        rw [List.length_append]; push_cast; rfl
    _ = (s.tag.length : ENat) + KPPlain U x := by rw [hlen]; rfl

/-! ### Theorem 1.7.4 -/

/-- Equality on `BitString`, as a `Bool`, is primitive recursive. -/
theorem bitStringEq_primrec : Primrec (fun p : BitString × BitString ↦ decide (p.1 = p.2)) := by
  obtain ⟨_, h⟩ := (Primrec.eq : PrimrecRel (@Eq BitString))
  exact Primrec.of_eq h (fun p ↦ by congr)

/-- **Theorem 1.7.4 (Solovay).** For a prefix-prepend universal `U` there is a
computable `G : BitString → ℕ` with `K(z) ≤ G(z)` for every `z` and `G(z) = K(z)` for
infinitely many `z`. -/
theorem exists_computable_upper_bound_eq_infinitely_often (U : Map)
    (hU : IsPrefixPrependUniversal U) :
    ∃ G : BitString → ℕ, Computable G ∧ (∀ z, KPPlain U z ≤ (G z : ENat)) ∧
      {z | (G z : ENat) = KPPlain U z}.Infinite := by
  classical
  have hUo := hU.isOptimalPrefixConditional
  have hUd := hU.isPrefixDecompressor
  obtain ⟨c, hc⟩ := Code.exists_code.mp hUd.isDecompressor
  obtain ⟨c₀, hbound⟩ := KPPlain_le_trivBound U hUo
  have hfin : ∀ x : BitString, KP U x [] ≠ ⊤ := fun x ↦
    ne_top_of_le_ne_top (ENat.coe_ne_top _) (hbound x)
  obtain ⟨s⟩ := hU.2 (certMap c U) (certMap_isPrefixDecompressor hUd hc)
  have hex := fbBad_exists_false hc s c₀
  -- Work with natural-number complexities.
  set kNat : BitString → ℕ := fun z ↦ (KPPlain U z).toNat with hkNat
  have hk : ∀ z, (kNat z : ENat) = KPPlain U z := fun z ↦ ENat.coe_toNat (hfin z)
  set F := solovayF c₀ c s.tag hex with hFdef
  have hFc : Computable F := solovayF_computable c₀ c s.tag hex
  have hF_ge : ∀ z, kNat z ≤ F z := fun z ↦ by
    have := KPPlain_le_solovayF U hc hbound s.tag hex z
    rw [← hk] at this; exact_mod_cast this
  -- On certificate pairs the estimate is within `C := |tag| + c₂` of the truth.
  obtain ⟨c₂, hc₂⟩ := KPPlain_left_le_KPPair U hUo
  set C := s.tag.length + c₂ with hC
  have hclose : ∀ x, F (certPair hc hfin x) ≤ kNat (certPair hc hfin x) + C := fun x ↦ by
    have h1 := solovayF_certPair_le hc hfin hbound s hex x
    have h2 : KPPlain U x ≤ KPPlain U (certPair hc hfin x) + (c₂ : ENat) := hc₂ x _
    have h3 : ((F (certPair hc hfin x) : ℕ) : ENat)
        ≤ KPPlain U (certPair hc hfin x) + ((C : ℕ) : ENat) := by
      calc ((F (certPair hc hfin x) : ℕ) : ENat)
          ≤ (s.tag.length : ENat) + KPPlain U x := h1
        _ ≤ (s.tag.length : ENat) + (KPPlain U (certPair hc hfin x) + (c₂ : ENat)) := by gcongr
        _ = KPPlain U (certPair hc hfin x) + ((s.tag.length : ENat) + (c₂ : ENat)) := by ring
        _ = KPPlain U (certPair hc hfin x) + ((C : ℕ) : ENat) := by rw [hC]; push_cast; rfl
    have h4 : ((F (certPair hc hfin x) : ℕ) : ENat)
        ≤ ((kNat (certPair hc hfin x) + C : ℕ) : ENat) := by
      rw [Nat.cast_add, hk]; exact h3
    exact_mod_cast h4
  -- The set where the estimate is within `C` is infinite.
  have hinfC : {z | F z ≤ kNat z + C}.Infinite :=
    Set.infinite_of_injective_forall_mem (certPair_injective hc hfin) hclose
  -- Pigeonhole: some exact difference `d ≤ C` occurs infinitely often.
  set S : ℕ → Set BitString := fun d ↦ {z | F z = kNat z + d} with hS
  have hcover : {z | F z ≤ kNat z + C} ⊆ ⋃ d ∈ (↑(Finset.range (C + 1)) : Set ℕ), S d := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range, hS, Set.mem_setOf_eq]
    exact ⟨F z - kNat z, by have := hF_ge z; omega, by have := hF_ge z; omega⟩
  have hexd : ∃ d, (S d).Infinite := by
    by_contra hcon
    have hall : ∀ d, (S d).Finite := fun d ↦ Set.not_infinite.mp (fun h ↦ hcon ⟨d, h⟩)
    have hfinU : (⋃ d ∈ (↑(Finset.range (C + 1)) : Set ℕ), S d).Finite :=
      Set.Finite.biUnion (Finset.finite_toSet _) (fun d _ ↦ hall d)
    exact hinfC (hfinU.subset hcover)
  set d₀ := Nat.find hexd with hd₀
  have hd₀inf : (S d₀).Infinite := Nat.find_spec hexd
  have hd₀min : ∀ d < d₀, (S d).Finite := fun d hd ↦
    Set.not_infinite.mp (Nat.find_min hexd hd)
  -- The finitely many points below `d₀`, as a list.
  have hbadfin : (⋃ d ∈ (↑(Finset.range d₀) : Set ℕ), S d).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) (fun d hd ↦ hd₀min d (Finset.mem_range.mp hd))
  set badList := hbadfin.toFinset.toList with hbadList
  have hmem_bad : ∀ z, z ∈ badList ↔ F z - kNat z < d₀ := by
    intro z
    rw [hbadList, Finset.mem_toList, Set.Finite.mem_toFinset]
    simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_range, hS, Set.mem_setOf_eq]
    constructor
    · rintro ⟨d, hd, hz⟩; omega
    · intro h; exact ⟨F z - kNat z, h, by have := hF_ge z; omega⟩
  -- The repaired function.
  set G : BitString → ℕ := fun z ↦
    bif badList.any (fun b ↦ decide (b = z)) then F z else F z - d₀ with hG
  refine ⟨G, ?_, ?_, ?_⟩
  · -- Computable: a `cond` over a fixed finite list, `F`, and `F − d₀`.
    have hmem : Computable (fun z : BitString ↦ badList.any (fun b ↦ decide (b = z))) :=
      (list_any_primrec (f := fun _ : BitString ↦ badList) (p := fun z b ↦ decide (b = z))
        (Primrec.const badList)
        ((bitStringEq_primrec.comp (Primrec.pair Primrec.snd Primrec.fst)).of_eq
          (fun a ↦ rfl)).to₂).to_comp
    have hsub : Computable (fun z ↦ F z - d₀) :=
      Primrec.nat_sub.to_comp.comp hFc (Computable.const d₀)
    exact Computable.cond hmem hFc hsub
  · -- Upper bound everywhere.
    intro z
    rw [← hk z]
    by_cases hz : badList.any (fun b ↦ decide (b = z)) = true
    · have : G z = F z := by simp [hG, hz]
      rw [this]; exact_mod_cast hF_ge z
    · have hzf : badList.any (fun b ↦ decide (b = z)) = false := by
        cases h : badList.any (fun b ↦ decide (b = z)) <;> simp_all
      have : G z = F z - d₀ := by simp [hG, hzf]
      rw [this]
      have hnotbad : ¬ (F z - kNat z < d₀) := by
        intro hlt
        have hmemz := (hmem_bad z).mpr hlt
        have : badList.any (fun b ↦ decide (b = z)) = true :=
          List.any_eq_true.mpr ⟨z, hmemz, by simp⟩
        exact hz this
      have := hF_ge z
      exact_mod_cast (by omega : kNat z ≤ F z - d₀)
  · -- Exact infinitely often: on `S d₀`.
    apply hd₀inf.mono
    intro z hz
    simp only [hS, Set.mem_setOf_eq] at hz
    simp only [Set.mem_setOf_eq]
    have hzf : badList.any (fun b ↦ decide (b = z)) = false := by
      rw [List.any_eq_false]
      intro b hb hbz
      have hbz' : b = z := by simpa using hbz
      subst hbz'
      have := (hmem_bad b).mp hb
      omega
    have : G z = F z - d₀ := by simp [hG, hzf]
    rw [this, ← hk z]
    exact_mod_cast (by omega : F z - d₀ = kNat z)

end Kolmogorov
