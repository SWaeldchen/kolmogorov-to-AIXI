/-
Copyright (c) 2026 Iliad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: stephan@iliad.ac
-/

import Gacs_Chapter_3.Oracle.Defs
import KolmogorovMathlib.AlgorithmicProbability.KraftChaitinAllocator

/-!
# The Kraft–Chaitin theorem relative to an oracle

Requests `(x_n, ℓ_n)` are produced along an oracle: `g σ n` is the `n`-th request as known from
the finite oracle prefix `σ`. They are **stable** (`g σ n = some r` persists on extensions of
`σ`) and form an **initial segment** (if request `n` is known, so are all earlier ones). If the
Kraft mass of the requests along the oracle `A` is at most `1`, the oracle machine
`oracleKCMachine g` gives every requested `x_n` complexity `K(x_n ∣ A) ≤ ℓ_n`
(`exists_oracleMachine_of_requests`).

## Construction

The repository's online Kraft–Chaitin allocator (`KraftChaitin.allocFun`) is run on the request
stream `n ↦ g σ n` read off the oracle prefix `σ`:

  `V(p, σ) = x`  iff  some `n` has `allocFun (g σ) n = some p` and `g σ n = some (x, ℓ)`.

* **Online**: `allocFun req n` only reads `req 0, …, req n` (`reqKC_allocFun_congr`). With
  stability and the initial-segment property, the streams of `σ ⊑ τ` agree up to every index
  known from `σ`, so `V` is **monotone in the oracle prefix** (`oracleKCMachine_mono`).
* **Prefix-free for every `σ`**: allocated codewords of distinct requests are incomparable
  (`KraftChaitin.allocFun_prefixFree`), whether or not the Kraft inequality holds.
* **Success**: if the Kraft mass along `A↾m` is `≤ 1`, request `n` gets a codeword of length
  exactly `ℓ_n` (`KraftChaitin.allocFun_success`).
* **Partial recursive**: `V` is an unbounded search for the request index, uniformly in `σ`
  (`KraftChaitin.allocFun_computable`).
-/

namespace Kolmogorov.Information.Oracle

open scoped ENNReal
open Kolmogorov.KraftChaitin (allocatorState allocFun allocFun_prefixFree allocFun_success
  allocFun_computable)
open Kolmogorov.Randomness (Seq seqTake)

/-! ### The allocator is online -/

/-- The allocator state after `n` steps only depends on the first `n` requests. -/
theorem reqKC_allocatorState_congr {req req' : ℕ → Option (BitString × ℕ)} :
    ∀ n, (∀ k < n, req k = req' k) → allocatorState req n = allocatorState req' n
  | 0, _ => rfl
  | n + 1, h => by
      have ih := reqKC_allocatorState_congr n (fun k hk ↦ h k (by omega))
      simp only [allocatorState, ih, h n (Nat.lt_succ_self n)]

/-- The `n`-th codeword only depends on the first `n + 1` requests. -/
theorem reqKC_allocFun_congr {req req' : ℕ → Option (BitString × ℕ)} (n : ℕ)
    (h : ∀ k ≤ n, req k = req' k) : allocFun req n = allocFun req' n := by
  simp only [allocFun, reqKC_allocatorState_congr n (fun k hk ↦ h k hk.le), h n le_rfl]

/-! ### The machine -/

variable (g : BitString → ℕ → Option (BitString × ℕ))

/-- Is `p` the `n`-th codeword allocated along `σ`? -/
def oracleKCHit (p σ : BitString) (n : ℕ) : Bool := decide (allocFun (g σ) n = some p)

/-- **The oracle Kraft–Chaitin machine**: on program `p` and oracle prefix `σ`, find the request
whose codeword is `p` and output its string. -/
def oracleKCMachine : Map := fun pr ↦
  (Nat.rfind (fun n ↦ Part.some (oracleKCHit g pr.1 pr.2 n))).bind
    (fun n ↦ ((g pr.2 n).map Prod.fst : Part BitString))

/-- Distinct requests get distinct codewords. -/
theorem reqKC_index_unique {σ p : BitString} {n m : ℕ} (hn : allocFun (g σ) n = some p)
    (hm : allocFun (g σ) m = some p) : n = m := by
  by_contra hne
  exact allocFun_prefixFree (g σ) n m p p hn hm hne List.prefix_rfl

theorem mem_oracleKCMachine {p σ x : BitString} :
    x ∈ oracleKCMachine g (p, σ) ↔
      ∃ n ℓ, allocFun (g σ) n = some p ∧ g σ n = some (x, ℓ) := by
  constructor
  · intro hx
    obtain ⟨n, hn, hxn⟩ := (Part.mem_bind_iff).mp hx
    have hhit : oracleKCHit g p σ n = true := by
      have := Nat.rfind_spec hn
      simpa using this
    have hpn : allocFun (g σ) n = some p := by simpa [oracleKCHit] using hhit
    rw [Part.mem_ofOption, Option.mem_def, Option.map_eq_some_iff] at hxn
    obtain ⟨⟨x', ℓ⟩, hr, rfl⟩ := hxn
    exact ⟨n, ℓ, hpn, hr⟩
  · rintro ⟨n, ℓ, hpn, hr⟩
    have hhit : oracleKCHit g p σ n = true := by simp [oracleKCHit, hpn]
    obtain ⟨n', hn', -⟩ := Nat.rfind_min' (p := fun k ↦ oracleKCHit g p σ k) hhit
    have hhit' : oracleKCHit g p σ n' = true := by
      have := Nat.rfind_spec hn'
      simpa using this
    have hpn' : allocFun (g σ) n' = some p := by simpa [oracleKCHit] using hhit'
    have he : n' = n := reqKC_index_unique g hpn' hpn
    subst he
    refine (Part.mem_bind_iff).mpr ⟨n', hn', ?_⟩
    rw [Part.mem_ofOption, Option.mem_def, hr]
    rfl

/-! ### Properties -/

theorem oracleKCMachine_isPrefixMachine : IsPrefixMachine (oracleKCMachine g) := by
  intro σ p hp q hq hpq
  obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp hp
  obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp hq
  obtain ⟨n, -, hpn, -⟩ := (mem_oracleKCMachine g).mp hx
  obtain ⟨m, -, hqm, -⟩ := (mem_oracleKCMachine g).mp hy
  by_cases hnm : n = m
  · subst hnm
    rw [hpn] at hqm
    exact Option.some_injective _ hqm
  · exact absurd hpq (allocFun_prefixFree (g σ) n m p q hpn hqm hnm)

theorem oracleKCMachine_partrec (hg : Computable (fun p : BitString × ℕ ↦ g p.1 p.2)) :
    isDecompressor (oracleKCMachine g) := by
  have halloc := allocFun_computable g hg
  have hpair : Computable (fun q : (BitString × BitString) × ℕ ↦
      (allocFun (g q.1.2) q.2, some q.1.1)) :=
    Computable.pair
      (halloc.comp (Computable.pair (Computable.snd.comp Computable.fst) Computable.snd))
      (Computable.option_some.comp (Computable.fst.comp Computable.fst))
  have heq : Primrec (fun q : Option BitString × Option BitString ↦ decide (q.1 = q.2)) :=
    PrimrecPred.decide (Primrec.eq.comp Primrec.fst Primrec.snd)
  have hhit : Computable (fun q : (BitString × BitString) × ℕ ↦
      oracleKCHit g q.1.1 q.1.2 q.2) :=
    (heq.to_comp.comp hpair).of_eq fun _ ↦ rfl
  have hrf : Partrec (fun pr : BitString × BitString ↦
      Nat.rfind (fun n ↦ Part.some (oracleKCHit g pr.1 pr.2 n))) :=
    Partrec.rfind hhit.partrec
  have hout : Computable (fun q : (BitString × BitString) × ℕ ↦ (g q.1.2 q.2).map Prod.fst) :=
    Computable.option_map (hg.comp (Computable.pair (Computable.snd.comp Computable.fst)
      Computable.snd)) (Computable.fst.comp Computable.snd).to₂
  exact Partrec.bind hrf hout.ofOption

/-- **Monotonicity in the oracle prefix.** -/
theorem oracleKCMachine_mono
    (hmono : ∀ σ τ n r, σ <+: τ → g σ n = some r → g τ n = some r)
    (hinit : ∀ σ n m, m ≤ n → (g σ n).isSome → (g σ m).isSome)
    (p σ τ x : BitString) (hστ : σ <+: τ) (hx : produces (oracleKCMachine g) p σ x) :
    produces (oracleKCMachine g) p τ x := by
  obtain ⟨n, ℓ, hpn, hr⟩ := (mem_oracleKCMachine g).mp hx
  have hagree : ∀ k ≤ n, g σ k = g τ k := fun k hk ↦ by
    obtain ⟨r, hr'⟩ := Option.isSome_iff_exists.mp
      (hinit σ n k hk (by rw [hr]; rfl))
    rw [hr', hmono σ τ k r hστ hr']
  have hpn' : allocFun (g τ) n = some p := by rw [← reqKC_allocFun_congr n hagree, hpn]
  exact (mem_oracleKCMachine g).mpr ⟨n, ℓ, hpn', by rw [← hagree n le_rfl, hr]⟩

/-- **The relativized Kraft–Chaitin theorem.** Stable requests, forming an initial segment, with
Kraft mass at most `1` along the oracle `A`, are realized by one oracle machine: every requested
`x` has `K(x ∣ A) ≤ ℓ`. The machine does not depend on `A`. -/
theorem exists_oracleMachine_of_requests
    (hg : Computable (fun p : BitString × ℕ ↦ g p.1 p.2))
    (hmono : ∀ σ τ n r, σ <+: τ → g σ n = some r → g τ n = some r)
    (hinit : ∀ σ n m, m ≤ n → (g σ n).isSome → (g σ m).isSome) :
    ∃ V, IsOracleMachine V ∧ ∀ A : Seq,
      (∀ m, ∑' n, (match g (seqTake A m) n with
        | some r => (2 : ℝ≥0∞)⁻¹ ^ r.2 | none => 0) ≤ 1) →
      ∀ n x ℓ m, g (seqTake A m) n = some (x, ℓ) → KPrel V A x ≤ ℓ := by
  refine ⟨oracleKCMachine g, ⟨⟨oracleKCMachine_partrec g hg,
    oracleKCMachine_isPrefixMachine g⟩, oracleKCMachine_mono g hmono hinit⟩, ?_⟩
  intro A hkraft n x ℓ m hr
  have hw : (∑' i, match g (seqTake A m) i with
      | some (_, l) => (2 : ℝ≥0∞)⁻¹ ^ l | none => 0) ≤ 1 := by
    refine le_trans (le_of_eq (tsum_congr fun i ↦ ?_)) (hkraft m)
    rcases g (seqTake A m) i with _ | ⟨_, _⟩ <;> rfl
  obtain ⟨c, hc, hlen⟩ := allocFun_success (g (seqTake A m)) n x ℓ hr hw
  have hprod : produces (oracleKCMachine g) c (seqTake A m) x :=
    (mem_oracleKCMachine g).mpr ⟨n, ℓ, hc, hr⟩
  calc KPrel (oracleKCMachine g) A x ≤ KP (oracleKCMachine g) x (seqTake A m) :=
        KPrel_le_KP _ A x m
    _ ≤ (programLength c : ENat) := KP_le_programLength_of_produces hprod
    _ = ℓ := by rw [programLength, hlen]

end Kolmogorov.Information.Oracle
