# Strategy — Formalizing Gács Chapter 3, "Information"

Companion to `../Gacs_Chapter_2/strategy.md`. Same conventions: numbering as in the compiled
PDF (verified against the `.aux`), every stage closed with an axiom check and a warning sweep,
nothing under `KolmogorovMathlib/` is edited. New Lean files go in `Gacs_Chapter_3/` and are
built as the Lake library `Gacs_Chapter_3`.

Status (2026-11-07, late): **Chapter 3 completely formalized**: every numbered theorem,
lemma, proposition and corollary of §§3.1–3.3, including Theorems 3.2.3 (`Ω ≡_T χ`) and 3.3.1
(complexity is rarely complex), which required new oracle infrastructure. 25 files, 7783 lines,
no `sorry`, zero warnings after a forced rebuild; all 52 main theorems depend only on
`[propext, Classical.choice, Quot.sound]`. Not formalized: Remark 3.1.13 and the aside that `K*` is
not semicomputable (informal). See §6 for the log and the deviations.

## 1. What the chapter contains

Source: tex lines 3757–4870 (PDF pp. 63–81).

| § | Content |
|---|---|
| 3.1.1 | classical entropy, Csiszár's log-sum inequality, Shannon's coding bound; entropy ≈ expected complexity; conditional entropy, additivity, mutual information; the **addition theorem** `K(x,y) =⁺ K(x) + K(y ∣ x, K(x))`; `x*`, `I(x:y)`, `I*(x:y)`; expected `I*` ≈ classical `I`; defects of additivity and symmetry; Levin's asymmetry theorem; conditional addition; simple and starry triangle inequalities; the algorithmic data-processing identity |
| 3.1.2 | information non-increase: `∑_y m(y) 2^{I(x:y)} ≲ 1`; deterministic and randomized processing |
| 3.2 | decision complexity `C(x; n)`; decidable ⇔ `C(ω; n) ≤⁺ 0`; Barzdin's theorem; the halting set `E`, `χ`, Chaitin's `Ω`; `Ω ≡_T χ`; `K(Ω(1:n)) ≥⁺ n` |
| 3.3 | `K(K(x) ∣ x) ≥ log n − log log n − c` for some `x` of each length `n`; it is rarely large: `I(χ : x) ≥⁺ f(x) − 2.4 log f(x)` |

### Numbering key (compiled PDF)

§3.1: Def 3.1.1 entropy · Thm 3.1.1 Csiszár · Thm 3.1.2 Shannon · Thm 3.1.3 entropy vs
expected complexity · Def 3.1.2 conditional entropy · Def 3.1.3 information · Prop 3.1.4
`I ≥ 0`, `= 0` iff independent · **Thm 3.1.4 addition** · Cor 3.1.5 `K(x*,y) =⁺ K(x,y)` ·
Thm 3.1.5 `K(K(x)∣x)` large (proved in §3.3) · Def 3.1.6 `f ⪯ g mod h` · Def 3.1.7 `K*` ·
Def 3.1.8 `I(x:y)` · Def 3.1.9 `I*(x:y)` · Lemma 3.1.10 expected `I*` · Remark 3.1.11
`I* =⁺ log m(x,y)/(m(x)m(y))` · Cor 3.1.12 defects · Thm 3.1.6 Levin (asymmetry) · Thm 3.1.7
conditional addition · Remark 3.1.13 · Thm 3.1.8 simple triangle · Def 3.1.14 `I*(x:y∣z)` ·
Thm 3.1.9 data processing · Cor 3.1.15 monotonicity · Thm 3.1.10 starry triangle ·
Thm 3.1.11 deterministic non-increase · Thm 3.1.12 randomized non-increase · Remarks 3.1.16,
3.1.17.

§3.2: Def 3.2.1 decision complexity · Remark 3.2.2 · Thm 3.2.1 decidable ⇔ bounded ·
Thm 3.2.2 Barzdin (a), (b) · Def 3.2.3 `E^t`, `E`, `χ` · Def 3.2.4 `Ω^t`, `Ω` · Thm 3.2.3
`Ω ≡_T χ` · Thm 3.2.4 `K(Ω(1:n)) ≥⁺ n`.

§3.3: Thm 3.3.1 `I(χ:x) ≥⁺ f(x) − 2.4 log f(x)` · Lemma 3.3.1 measure approximation ·
Lemma 3.3.2 `m(X(n)) ≲ n^{1.2} 2^{-n}`.

## 2. What already exists

- **Addition theorem, both directions** (upstream): `KPPair_chain_upper`, `KPPair_chain_lower`
  (`Prefix/Symmetry.lean`, `Prefix/ConditionalSymmetry.lean`) with context
  `prefixComplexityContext x k = pairCode x (natCode k)`; the conditional version
  `KPCondPair_chain_upper/lower`. So Theorems 3.1.4 and 3.1.7 are assembly.
- Chapter 1 (ours, inside `KolmogorovMathlib/DescriptionStatistics/`): Corollary 1.7.1
  `progCount_shortest_le` (boundedly many shortest descriptions) and `eq:xHx`
  `KPPair_natCode_self_eq_KPPlain`. These give `x* ≍ ⟨x, K(x)⟩`.
- Coding theorem, conditional coding (`conditional_coding_equivalence`), Kraft
  (`Prefix/Kraft.lean`), `K(⟨y,y'⟩) ≤⁺ K(y)+K(y')`, transport lemmas (`KP_cond_map_le`,
  `KP_cond_first_map_le`, …).
- Chapter 2 (ours): `IsLSCDescription`, `semimeasure_le_exact` (`m ≥ 2^{-K(ν)} ν`), needed for
  `K(P)` in Theorem 3.1.3 and Lemma 3.1.10.
- Mathlib: `Real.negMulLog`, `InformationTheory.klFun`, convexity of `x log x`;
  `RecursiveIn`, `TuringReducible`, `TuringEquivalent` (oracle computability as an inductive
  class — **no oracle codes and no universal oracle machine**).

## 3. Design decisions

- **Complexities as naturals.** For an optimal `U`, `KP U x y < ⊤`; we work with
  `Kc U x y := (KP U x y).toNat` and `Kn U x := Kc U x []`. "`a =⁺ b`" is stated as
  `∃ c, ∀ …, a ≤ b + c ∧ b ≤ a + c` in `ℕ`, or with `ℤ` when differences appear (`I*` can be
  negative up to a constant).
- **Pairs** are `pairCode` (upstream), numbers inside conditions are `natCode k` (as in the
  upstream addition theorem). Any other computable encoding changes complexities by `O(1)`.
- **`x*`** is a shortest description of `x` chosen by `Classical.choose`, with no
  computability claim. Only `x* ≍ ⟨x, K(x)⟩` is used, and it holds for every choice, because
  the set of shortest descriptions has boundedly many elements (Cor 1.7.1).
- **Classical entropy is `ℝ≥0∞`-valued** on countable types, `H(P) = ∑ −P log₂ P`, so
  infinite entropy is allowed and the additivity identity holds with no finiteness
  hypothesis. Differences (`I = H(Y) − H(Y∣X)`) are taken under finiteness hypotheses.
- **Constants in §3.3** are stated with `K(n)` instead of logarithms (the sharp form, which
  implies Gács' `1.2`, `2.4`; see the log "Sharp constants in §3.3").
- **Oracles.** Theorem 3.3.1 needs `K(x ∣ χ)` for an *infinite* oracle; Theorem 3.2.3 needs
  Turing reductions. Mathlib's `TuringEquivalent` covers the statement of 3.2.3. A relative
  prefix complexity with an invariance and coding theorem needs a universal oracle machine,
  which neither Mathlib nor upstream has. This is scheduled last (Stage H) as a separate
  decision.

## 4. Stage plan

| Stage | Content | Est. | Depends on | Who |
|---|---|---|---|---|
| **A** | Classical: Def 3.1.1, Thm 3.1.1 (finite, with equality case), Gibbs in `ℝ≥0∞`, Thm 3.1.2, Def 3.1.2, additivity, `H(Y∣X) ≤ H(Y)`, Def 3.1.3, symmetry, KL form, Prop 3.1.4, classical data processing and triangle | 700 | Mathlib | fork |
| **B** | Thm 3.1.3: `H(P) ≤ ∑ P K ≤ H(P) + K(P) + c` | 150 | A, Ch. 2 `Descriptions` | fork (with A) |
| **C** | Algorithmic identities: Thm 3.1.4, `x*`, Cor 3.1.5, Defs 3.1.6–3.1.9, Remark 3.1.11, Cor 3.1.12, Thm 3.1.7, Thm 3.1.8, Def 3.1.14, Thm 3.1.9, Cor 3.1.15, Thm 3.1.10 | 800 | upstream | main |
| **D** | Lemma 3.1.10 (expected `I*` vs classical `I`) | 250 | A, B, C | main |
| **E** | §3.1.2: `∑ m(y) 2^{I(x:y)} ≲ 1`, Thm 3.1.11, Thm 3.1.12, Remark 3.1.16 | 250 | C | main |
| **F** | Thm 3.1.5 (`K(K(x)∣x)` large, §3.3.1); then Thm 3.1.6 (Levin) | 800 | upstream; C for 3.1.6 | fork; main for 3.1.6 |
| **G** | §3.2: Def 3.2.1 + invariance, Thm 3.2.1, Thm 3.2.2, Defs 3.2.3–3.2.4, Thm 3.2.4; Lemmas 3.3.1, 3.3.2 | 900 | upstream | fork |
| **H** | Thm 3.2.3 (`Ω ≡_T χ`), Thm 3.3.1 (relative complexity) | ? | G | decision |

## 5. Risks

1. **Thm 3.1.5's proof is a sketch** ("this implies `j ≥ n/(4 log n)`"): the counting and
   the description-length bookkeeping must be done explicitly.
2. **Thm 3.2.3** needs many-one completeness of the halting set of the optimal machine, which
   optimality alone may not give; the simulation-style `IsPrefixPrependUniversal` may be
   needed.
3. **Thm 3.3.1** needs relativized prefix complexity (Stage H).
4. **`Ω(1:n)`**: we use `⌊Ω 2^n⌋` and the threshold `Ω^t > Ω(1:n) − 2^{-n}` in the proof of
   Thm 3.2.4, so no irrationality of `Ω` is needed.

## 6. Progress log

### 2026-11-07 — Stages A–G

Written by the main session (Stages C, D, E, Theorem 3.1.6) and three parallel agents
(A+B: `Classical/`; F: `CompComp/`; G: `Halting/`). Namespaces: `Kolmogorov.Information`,
with sub-namespaces `.Classical`, `.CompComp`, `.Halting`.

| Folder | Files (lines) |
|---|---|
| `Classical/` | `Entropy` (285), `Information` (593), `ExpectedComplexity` (128) |
| `Information/` | `Basic` (424), `Identities` (422), `NonIncrease` (210), `Levin` (110), `ExpectedInfo` (264), `InfoRatio` (81) |
| `CompComp/` | `Search` (634), `SometimesComplex` (400) |
| `Halting/` | `DecisionComplexity` (342), `Barzdin` (292), `Omega` (445), `RarelyComplex` (618) |

**§3.1**

| Gács | Lean |
|---|---|
| Def 3.1.1, Thm 3.1.1 (with equality case), Gibbs, Thm 3.1.2 | `Classical.entropy`, `log_sum_inequality`, `log_sum_eq_iff`, `entropy_le_crossEntropy`, `entropy_le_tsum_mul_length`, `shannon_coding_lb` |
| **Thm 3.1.3** | `Classical.entropy_expectedComplexity` |
| Def 3.1.2, additivity, `H(Y∣X) ≤ H(Y)` | `Classical.condEntropy`, `entropy_eq_add_condEntropy`, `condEntropy_le_entropy` |
| Def 3.1.3, symmetry, KL form, Prop 3.1.4 | `Classical.mutualInfo`, `mutualInfo_swap`, `mutualInfo_eq_mutualInfoKL`, `mutualInfo_eq_zero_iff` |
| classical data processing, triangle | `Classical.mutualInfo_chain`, `condEntropy_triangle` |
| **Thm 3.1.4 (addition)** | `addition` |
| `x*`, `x* ≍ ⟨x, K(x)⟩` | `xStar`, `xStar_equiv` (via Cor 1.7.1 and `condCoding_trim`) |
| `K(x,y) − K(x) =⁺ K(y ∣ x*)` | `addition_star` |
| **Cor 3.1.5** | `Ku_xStar_pair` |
| **Thm 3.1.5** | `CompComp.exists_KK_ge` |
| Defs 3.1.6–3.1.9 | `InfoLE`, `InfoLEMod`, `InfoEquiv` (`.cond`, `.obj`), `Kstar` (`Kstar_addition`), `Info`, `InfoStar` |
| `I* =⁺ I(x*:y) =⁺ I(y*:x)` | `infoStar_eq_info_xStar`, `infoStar_eq_info_yStar` |
| **Lemma 3.1.10** | `expected_infoStar` (in `ℝ≥0∞`, no subtraction, no finiteness hypothesis) |
| Remark 3.1.11 | `infoStar_eq_log_ratio` |
| **Cor 3.1.12** | `additivity_defect`, `additivity_defect_le`, `info_asymmetry` |
| **Thm 3.1.6 (Levin)** | `levin_asymmetry` (via `asym_gap`) |
| **Thm 3.1.7** | `condAddition` |
| **Thm 3.1.8** | `simple_triangle` |
| Def 3.1.14 and its two forms | `CondInfoStar`, `condInfoStar_eq_left`, `condInfoStar_eq_right` |
| **Thm 3.1.9** | `data_processing` |
| **Cor 3.1.15** | `infoStar_mono` |
| **Thm 3.1.10** | `starry_triangle` |
| (3.1.x) guessing | `info_guess` |
| **Thm 3.1.11** | `info_nonincrease_det` |
| **Thm 3.1.12** | `info_nonincrease_rand`, `info_nonincrease_rand_mul` |
| Remark 3.1.16 | `info_increase_expectation`, `info_increase_tail` |

Not formalized: Remark 3.1.13 (an incorrect guess) and the remark that `K*` is not
semicomputable; both are informal asides.

**§3.2, §3.3** (namespace `Halting`)

| Gács | Lean |
|---|---|
| Def 3.2.1, invariance, optimal decision machine | `decK`, `univDec_isOptimal`, `exists_isOptimalDecision` |
| `C(x ∣ n) ≤⁺ C(x; n) ≤⁺ C(x)` | `condK_le_decK`, `decK_le_plainK` |
| **Thm 3.2.1** | `computable_iff_decK_bounded` |
| **Thm 3.2.2 (Barzdin)** (a), (b) | `decK_le_log_of_isRE`, `exists_isRE_log_le_decK` |
| Defs 3.2.3, 3.2.4 | `haltSet`, `chi`, `omegaStage`, `omega`, `omegaPrefix` |
| **Thm 3.2.4** | `le_KP_omegaPrefix` |
| **Lemma 3.3.1** | `measure_approx_le`, `measure_approx_lt` |
| **Lemma 3.3.2** | `aprioriMeasure_complexityOfComplexity_le` (sharp form `C 2^{K(n)} 2^{-n}`, implies Gács' `n^{1.2} 2^{-n}`) |

**Design notes.**

- *One engine again.* `condCoding_trim` (conditional coding theorem for any jointly lsc
  family, at conditions where it is a semimeasure) gives `x* ⪯ ⟨x, K(x)⟩` from the uniform
  distribution on shortest descriptions; Chapter 2's `indexed_domination_trim` gives the
  `K(p)` terms of Theorem 3.1.3 and Lemma 3.1.10 *without descriptions of the marginals*.
- *`=⁺` algebra.* All of §3.1 after the addition theorem reduces to the two addition
  theorems, `x* ≍ ⟨x, K(x)⟩`, transport lemmas and pair rearrangements; each identity is
  closed by `omega` over integer-cast complexities.
- *Classical entropy in `ℝ≥0∞`* makes additivity, chain rule, Gibbs, Shannon,
  Theorem 3.1.3 and Lemma 3.1.10 hold with no finiteness hypotheses.
- *Theorem 3.1.5* reconstructs `M_{i+1}` from its size by a fuel-bounded search; Gács'
  assumption `log|M_i ∖ M_{i+1}| ≥ log|M_i| − 1` is not needed, and `4 log n` becomes
  `14 log n` (irrelevant to the result).
- *`Ω(1:n)`* uses the threshold `Ω^t + 2^{-n} > a_n 2^{-n}`, so no irrationality of `Ω`.

### 2026-11-07 (late) — Stage H: oracles, Theorems 3.2.3 and 3.3.1

Ten new files, 2554 lines, in `Oracle/` (shared definitions, oracle machines, relative coding,
Theorem 3.3.1) and `Turing/` (Theorem 3.2.3). Written by the main session (`Defs`,
`HaltingOracle`, `RarelyComplex*`) and three parallel agents (T: `Turing/`; O:
`MachineFilter`, `MachineUniversal`; R: `Coding`).

| Result | Lean name | File |
|---|---|---|
| exact universality; the repository's universal machine has it | `IsExactUniversal`, `universalPrefixMachine_isExactUniversal` | `Oracle/Defs.lean` |
| oracle machine, `K(x ∣ A)`, optimal oracle machine | `IsOracleMachine`, `KPrel`, `IsOptimalOracle` | `Oracle/Defs.lean` |
| **an optimal oracle machine exists**; `K(x ∣ A) ≤⁺ K(x)` | `exists_isOptimalOracle`, `IsOptimalOracle.KPrel_le_KP` | `Oracle/MachineUniversal.lean` |
| **relativized Kraft–Chaitin** | `exists_oracleMachine_of_requests` | `Oracle/Coding.lean` |
| use principle for `RecursiveIn`, `≤ᵀ` via finite tables | `recursiveIn_of_table`, `turingReducible_of_table` | `Turing/RecursiveIn.lean` |
| `χ ≤_T Ω`; `Ω ≤_T χ`; `Ω` not dyadic; `χ` not computable | `chi_le_omega`, `omega_le_chi`, `omega_ne_dyadic`, `chi_not_computable` | `Turing/OmegaChi.lean` |
| **Theorem 3.2.3** | `chi_turingEquivalent_omega` | `Turing/OmegaChi.lean` |
| reading `K(x)`, `K(y ∣ x)` off finite prefixes of `χ` | `knownOut`, `minHit_eq`, `kVal_eq`, `fVal_eq`, `readyB_spec` | `Oracle/HaltingOracle.lean`, `RarelyComplexMain.lean` |
| **Theorem 3.3.1** | `rarely_complex`, `rarely_complex_info` | `Oracle/RarelyComplexMain.lean` |

**Design.**

- *Exact universality* (`U(tag ++ p, y) = M(p, y)`, both directions) is the hypothesis of
  Theorems 3.2.3 and 3.3.1. Additive optimality is not enough for `Ω ≤_T χ` (many-one
  completeness of the halting set). The repository's `universalPrefixMachine` satisfies it, so
  the theorems are not vacuous.
- *Oracle machines* are conditional prefix machines fed finite oracle prefixes, **monotone in
  the prefix**; `K(x ∣ A) = inf_m K_V(x ∣ A↾m)`. Monotonicity rules out reading the prefix
  length. The universal oracle machine is a tagged union of a monotone prefix filter over all
  codes: candidate `n` may only appear at prefixes of length `≥ n`, which makes acceptance
  stable under extension.
- *Relativized Kraft–Chaitin* reuses the upstream online allocator with the oracle prefix as
  its parameter; requests must be stable under extension and form an initial segment.
- *Theorem 3.3.1 uses `χ` directly* (no Turing reduction from `Ω`): with exact universality,
  `U(q, x) = U(t ++ ⟨x, q⟩, [])`, so a finite prefix of `χ` decides all programs needed for
  `K(x)`, `f(x) = K(K(x) ∣ x)` and `K(f(x))`. The requests `(x, K(x) + c₀ + 2 K(f(x)) − f(x))`
  have Kraft mass `≤ C 2^{-c₀} ∑ₙ 2^{-K(n)} ≤ 1` by the sharp Lemma 3.3.2 and Kraft.

**Deviations.**

- Theorem 3.3.1 is proved in the **sharper** form `I(χ : x) ≥ f(x) − 2 K(f(x)) − c` (see the
  log entry "Sharp constants in §3.3" below); Gács' `… − 2.4 log f(x)` follows.
- Theorem 3.2.3: digits of `Ω` are 0-indexed (`omegaBit U n` is Gács' digit `n + 1`).

## 7. What remains in Chapter 3

Nothing beyond the two informal remarks (3.1.13; `K*` not semicomputable). Optional: derive
Gács' literal forms (`n^{1.2} 2^{-n}`, `2.4 log f`) from the sharp ones via
`K(n) ≤ log n + 2 log log n + O(1)`; this is pure asymptotics and adds nothing.

### 2026-11-07 (night) — Sharp constants in §3.3

Lemma 3.3.2 and Theorem 3.3.1 now carry the sharpest constants this proof gives.

| Result | Statement | Gács |
|---|---|---|
| **Lemma 3.3.2** `aprioriMeasure_complexityOfComplexity_le` | `m{f = n} ≤ C 2^{K(n)} 2^{-n}` | `≲ n^{1.2} 2^{-n}` |
| **Theorem 3.3.1** `rarely_complex` | `K(x ∣ χ) + f(x) ≤ K(x) + 2 K(f(x)) + c` | `I(χ : x) ≥⁺ f(x) − 2.4 log f(x)` |
| `rarely_complex_info` | `I(χ : x) ≥ f(x) − 2 K(f(x)) − c` | |

Ours implies Gács': `K(n) ≤ log n + 2 log log n + O(1) ≤ 1.2 log n + O(1)`, so
`2^{K(n)} ≲ n^{1.2}` and `2 K(f) ≤ 2.4 log f + O(1)`.

- *Where Gács loses.* Off the bad set `Y(k)`, `f(x) ≤ K(Ω(1:k)) + O(1)`. Gács bounds
  `K(Ω(1:k)) ≤ k + 1.2 log k`. Instead, `KPPlain_add_le_of_length` gives
  `K(s) + e ≤ n + c` for every `s` of length `n − K(n) − 3e`, with `c` independent of `e`:
  write a shortest program for `n`, then `⟨0^e, s⟩` (`lenMachine` checks
  `|s| + 3e + K(n) = n` using the context `⟨n, K(n)⟩` of the upstream chain rule
  `KPPair_chain_upper`). Taking `e` larger than all other constants gives
  `{f = n} ⊆ Y(n − K(n) − 3e)`, whose measure is `≤ 4·2^{3e}·2^{K(n)−n}`.
- *Why `e` is read from the input.* If `e` were a parameter of the machine, its constant would
  depend on `e`, and choosing `e` larger than that constant would be circular.
- *Theorem 3.3.1.* The oracle also reads `K(f(x))` off `χ` (a third `allKnown` in `readyB`).
  The Kraft sum regroups by `n = f(x)`:
  `∑ₙ 2^{n − 2K(n) − c₀} m{f = n} ≤ C 2^{-c₀} ∑ₙ 2^{-K(n)} ≤ 1`.
- `pairCode_prefix` and `pairCode_primrec'` moved to `Halting/RarelyComplex.lean` (needed there
  first); the `n²`-specific helpers `sq_mul_inv_pow_bitLen_le` and `two_pow_size_le` (Halting)
  are gone.

Build: `lake build Gacs_Chapter_3` green with no warnings in Chapter 3; `rarely_complex`,
`rarely_complex_info`, `aprioriMeasure_complexityOfComplexity_le` and
`KPPlain_add_le_of_length` depend only on `[propext, Classical.choice, Quot.sound]`.
