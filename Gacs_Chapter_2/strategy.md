# Strategy — Formalizing Gács Chapter 2, "Randomness"

Companion to `../../Strategy.md` (Chapter 1). Same conventions: multiplicative
statements in `ℝ≥0∞`, no logarithms, explicit constants, numbering as in the compiled
PDF, every stage closed with an axiom check and a warning sweep. New Lean files go in
a new subfolder `Gacs_Chapter_2/Randomness/`; existing files are not edited.

Status (2026-11-07, evening): **Chapter 2 complete, including Gács' explicit constants.**
Every numbered theorem of §§2.1–2.3 is formalized except the optional Theorem 2.3.6
(monotone machines, Stage J). The `K(d) + K(P)` constants (Tier 2) are done for Theorems
2.2.1, 2.2.2, 2.2.3, Corollary 2.2.8 and Theorem 2.3.3, together with the exact domination
`m ≥ 2^{-K(ν)} ν` and `M ≥ 2^{-K(ν)} ν`. There are 21 files in `Gacs_Chapter_2/Randomness/`,
about 6400 lines, with no `sorry`. The seven files added on 2026-11-07 are warning-free and
axiom-clean; older files still carry long-line lint warnings (`KMBounds.lean`). See §7 for
the log and §9 for what remains.

## 1. What the chapter contains

Three sections, about 23 pages in the PDF (lines 1771–2876 of the extracted text).

| § | Title | Pages | Content |
|---|---|---|---|
| 2.1 | Uniform distribution | 3 | Martin-Löf tests on finite strings; Thm 2.1.1: `d₀(x) = |x| − C(x | |x|)` is a universal ML-test |
| 2.2 | Computable distributions | 6 | integrable vs probability-bounded tests (Prop 2.2.3); Thm 2.2.1: `d_P(x) = −log P(x) − K(x)` is universal; conservation under computable maps (Thm 2.2.2) and randomized maps (Thm 2.2.3, Cor 2.2.8) |
| 2.3 | Infinite sequences | 14 | measures on the Cantor space as functions on strings, null sets, constructive null sets, randomness (Def 2.3.14); Thm 2.3.1 universal null set; Thm 2.3.2 tests ↔ null sets; Thm 2.3.3 universal integrable test; Thm 2.3.4 `d_μ(ξ) =⁺ sup_n (−log μ(ξ_{1:n}) − K(ξ_{1:n}))`; §2.3.7 continuous semimeasures, Thm 2.3.5 universal `M`, monotone machines, Thm 2.3.6; §2.3.8 `KM`, Prop 2.3.37, Thm 2.3.7 |

Full numbering key in §8.

## 2. What already exists

**In the repository.**

- *Discrete semimeasures and universality*: `IsSemimeasure`, `IsLSC` (dyadic
  approximations), `mixture`, `Dominates`, `exists_universalSemimeasure`. Crucially,
  `exists_lsc_semimeasure_family` in `UniversalSemimeasure.lean` already performs
  **Levin's trimming**: it enumerates all lower-semicomputable functions by code
  (`approxEnum`), monotonizes (`makeMono`) and truncates (`truncG`) each into a
  genuine semimeasure `lscEnum i`, and proves every lsc semimeasure is dominated by
  some `lscEnum i`. This is the template for Theorem 2.3.5.
- *Coding theorem, both halves*, and the Kraft–Chaitin realization of any lsc
  subnormalized function by a prefix machine (`kraftChaitin_realization_bound`).
- *Randomness deficiency for finite coded models*: `DeficiencyLe` (the multiplicative
  form of `d(x|P) ≤ β`), `canonicalTest P = m(x)/P(x)` with
  `canonicalTest_expectation_le_one`, `RandomnessTest`, and conservation
  `deficiency_conserved` — all for `CodedFiniteDistribution`, i.e. finite-support
  rational distributions. This is Definition 2.2.4/2.2.7 and half of Theorem 2.2.1
  for that restricted class.
- *From Chapter 1 (ours)*: Levin's Theorem 1.5.3 (`Chapter1Misc/Levin.lean`), which
  is exactly the tool Gács uses to prove Theorem 2.1.1; upper semicomputability of
  `C`; the fuel/dovetailing/enumeration toolkit (`FuelComplexity`, `Levin.lean`).

**In Mathlib.** Infinite product measures (`Measure.infinitePi`), the Ionescu–Tulcea
kernel construction, cylinder sets, `klDiv` with a chain rule. No Martin-Löf
randomness, no Pinsker.

**Not present anywhere**: tests on infinite sequences, null sets, constructive null
sets, randomness of sequences, continuous semimeasures, monotone machines, `KM`, a
general notion of computable probability measure (the repo's is finite-support).

## 3. Design decisions

### 3.1 Tests are multiplicative

Gács's tests `d` are real-valued with additive constants. We formalize `t = 2^d`:

- `t : BitString → ℝ≥0∞`, lower semicomputable (`IsLSC₁`, Stage 0);
- **probability-bounded (ML) test** for `P`: `P {x : 2^m < t x} ≤ 2^{-m}` for all `m`;
- **integrable test** for `P`: `∑ x, P x · t x ≤ 1`;
- universality: `t ≤ 2^c · t₀`, one constant.

`d(x) ≤⁺ d₀(x)` becomes `t x ≤ 2^c · t₀ x`; `d_P(x) = −log P(x) − K(x)` becomes
`t_P x = 2^{-K(x)} / P x`, which is the repo's `canonicalTest`. Prop 2.2.3's
`d − 2 log d − c` is stated by dyadic level: on `{2^m < t ≤ 2^{m+1}}` take
`2^m / (m² 2^c)`. No logarithm anywhere.

### 3.2 Computable measures

Needed for §2.2 and §2.3 alike. Definition (Stage 0):
`IsComputableENNReal f` — computable dyadic approximations with error `2^{-k}` — and
`ComputableMeasure` on `BitString` as a probability measure (`∑ = 1`) that is
`IsComputableENNReal`. On sequences (§2.3), a computable measure is a computable
`μ : BitString → ℝ≥0∞` with `μ [] = 1` and `μ x = μ (x++[0]) + μ (x++[1])`
(Def 2.3.5 verbatim). The repo's `CodedFiniteDistribution` is a special case; a
bridge lemma keeps the existing deficiency results usable.

### 3.3 The constants `K(d) + K(P)`

Theorems 2.2.1–2.2.3 and 2.3.3 carry constants `K(d) + K(P)`, the complexities of the
*indices* of the test and of the measure. Two-tier plan:

1. **Tier 1**: state universality with an existential constant `∃ c` per test. This is
   what the mixture construction gives directly and is all the later chapter uses.
2. **Tier 2**: index tests and measures through an effective enumeration (the repo's
   `lscEnum i`, or a code `i : ℕ`) and prove the constant is `2^{K(i) + O(1)}` with
   `K(i) := KPPlain U (natCode i)`. This is the `2^{-K(i)}`-weighted mixture instead of
   the dyadic one; the repo's `TaggedUnionUniversal` shows the pattern.

Tier 2 is scheduled after Tier 1 in every stage and can be dropped without breaking
anything downstream.

### 3.4 Infinite sequences at the string level

Gács develops measure theory on `Σ^ℕ` by hand (§§2.3.1–2.3.4, Defs 2.3.4–2.3.28).
Every theorem of §2.3 he actually proves uses only **cylinder sets**, so we work at
the level of strings and do not build his integration theory:

- sequences are `ℕ → Bool`; `x ⊑ ξ` is "x is a prefix of ξ";
- a measure is a function on strings with the additivity law (Def 2.3.5);
- an open set is given by its set of generating strings `Γ ⊆ BitString`; its measure
  is the supremum of `∑_{x ∈ F} μ x` over finite **prefix-free** `F ⊆ Γ`
  (Def 2.3.8, Prop 2.3.9 via Lemma 2.3.6/Cor 2.3.7);
- a null set is one covered by opens `G_m` with `μ(G_m) ≤ 2^{-m}` (Def 2.3.10); a
  constructive null set has `Γ_m` uniformly r.e. in `m` (Def 2.3.13); random = in no
  constructive null set (Def 2.3.14);
- an lsc function on sequences is given by an r.e. set of pairs `(x, q)` meaning
  "`t ≥ q` on the cylinder of `x`"; its value at `ξ` is the sup over `x ⊑ ξ`; its
  integral is the sup over finite prefix-free families of `∑ μ(x_i) q_i`. This is the
  constructive integral and makes lower semicomputability built in (Def 2.3.29).

The general definitions 2.3.15–2.3.28 (σ-algebra, Lebesgue measure, measurable and
computable real functions, integrals) are **out of scope**: they are textbook
material that Mathlib provides. An optional bridge, "a string-level measure induces a
`MeasureTheory.Measure` on `ℕ → Bool` via Ionescu–Tulcea", is listed as a late stage.

### 3.5 Continuous semimeasures and `M`

`IsContSemimeasure μ : μ [] ≤ 1 ∧ ∀ x, μ (x++[false]) + μ (x++[true]) ≤ μ x`,
constructive if `IsLSC₁`. Theorem 2.3.5 is proved by adapting the discrete trimming
`truncG`: the truncation now enforces the two continuous constraints instead of
`∑ ≤ 1`. Monotone machines (Defs 2.3.33–2.3.34) are modelled as `BitString →. BitString`
with the monotonicity `p ⊑ p' → T p ⊑ T p'` on the domain; `P_T x = ∑_{p minimal,
x ⊑ T p} 2^{-|p|}`. Theorem 2.3.6, the monotone Kraft–Chaitin theorem, is the one
genuinely hard result of the chapter and is scheduled last and marked optional.

## 4. Stage plan

Estimates are Lean lines, calibrated on Chapter 1 (Section 1.7 came in at 3445 for
an estimate of 3300; Section 1.4 at 704 for 600).

| Stage | Content | Est. | Depends on |
|---|---|---|---|
| **0** | `IsLSC₁`, `IsComputableENNReal`, closure lemmas, Prop 1.6.8 — **done** (`LowerSemicomputable.lean`, `LSCAlgebra.lean`, `Conservation.lean`) | 350 → 900 | — |
| **A** | Test foundations, Prop 2.2.3 both directions — **done** (`ComputableMeasure.lean`, `MLToIntegrable.lean`) | 300 → 345 | 0 |
| **B** | §2.1, Thm 2.1.1 — **done** (`MartinLofTest.lean`) | 350 → 372 | A, `Levin.lean` |
| **C** | §2.2 Tier 1: Thm 2.2.1, Prop 2.2.5, Thm 2.2.2 — **done** (`UniversalTest.lean`, `Conservation.lean`); bridge to `CodedFiniteDistribution` not done | 800 → 573 | A, 0 |
| **C′** | Thm 2.2.3 and Cor 2.2.8 (randomized transformations `T(x,y)`) — **done, Tier 1** (`RandomizedConservation.lean`); constants `K(d) + K(P)` via indexed enumeration — **not done** | 700 → 314 (Tier 1) | C |
| **D** | §2.3 string-level foundations: sequences, cylinders, measures on strings, uniform `λ`, open sets and their measure (Lemma 2.3.6, Cor 2.3.7, Prop 2.3.9), null sets, Prop 2.3.12 (countable union), constructive null sets, randomness — **done** (`Sequences.lean`, `SeqMeasure.lean`) | 900 → 560 | 0 |
| **E** | §2.3.7: `IsContSemimeasure`, constructive, **Thm 2.3.5** universal `M` by adapted trimming; `KM`; Prop 2.3.37 `KM ≤⁺ K ≤⁺ KM + K(|x|)` — **done** (`ContTrim.lean`, `ContTrimComputable.lean`, `UniversalContSemimeasure.lean`, `KMBounds.lean`) | 1500 → 945 | 0, D |
| **F** | Thm 2.3.1 universal constructive null set — **done** (`LevinSchnorr.lean`), *not* by measure-guarded enumeration but as `{R = ∞}` via Thms 2.3.2 and 2.3.3, see §7 | 800 → ~40 | D, G, H |
| **G** | Thm 2.3.2 tests ↔ null sets — **done** (`SeqTest.lean`); Thm 2.3.3 universal integrable test on sequences — **done, Tier 1** (`LevinSchnorr.lean`) | 900 → 452 + part of H | D |
| **H** | Thm 2.3.4 and Cor 2.3.30: `d_μ(ξ) =⁺ sup_n (−log μ(ξ_{1:n}) − K(ξ_{1:n}))`, randomness of a sequence ⇔ incompressibility of prefixes — **done** (`PrefixFreeMass.lean`, `LevinSchnorr.lean`) | 900 → 883 (with G's Thm 2.3.3 and F) | G, coding theorem |
| **I** | §2.3.8: Def 2.3.38 `d′_P`, Thm 2.3.7 (it is an ML-test), relation to `d_P` — **done** (`RandomnessViaM.lean`) | 500 → 196 | E, G |
| **J** | *Optional*: monotone machines, Def 2.3.34, **Thm 2.3.6** (every constructive semimeasure is some `P_T`) | 2000 | E |
| **K** | *Optional*: bridge from string-level measures to `MeasureTheory.Measure (ℕ → Bool)` via Ionescu–Tulcea | 400 | D |

Core (0, A–I): about **7700 lines**. With J and K: about 10,000. Chapter 1 took about
5500 in total, so this is roughly a doubling of the project's Gács footprint.

**Recommended order**: 0 → A → C → B → D → E → F → G → H → I, then C′, then J, K.
Stage E is pulled forward because Theorem 2.3.5 is the piece the Solomonoff/AIXI
direction needs; nothing after it depends on F–I.

## 5. Risks and how each is handled

1. **Logarithms.** Every additive statement is recast multiplicatively (§3.1); the
   only place a genuine logarithm-like quantity appears is Prop 2.2.3's second half,
   handled by dyadic levels.
2. **Index-dependent constants.** Deferred to Tier 2 (§3.3); Tier 1 is what the rest
   of the chapter consumes.
3. **Measure theory on the Cantor space.** Avoided by working on strings (§3.4).
   Risk: a reader may want the connection to Mathlib measures; Stage K provides it.
4. **Measure-guarded enumeration (Thm 2.3.1).** Enumerating a constructive null set
   requires checking `∑ μ(x_i) ≤ 2^{-m}` while adding cylinders; with `μ` only
   computable this is done with the upper approximations and a strict margin. Needs
   care but is standard; budgeted in F.
5. **Theorem 2.3.6.** Hard, long, optional; nothing else depends on it.
6. **Gaps in the source.** Theorems 2.3.4 and 2.3.7 are proved "by standard methods";
   we will consult Li–Vitányi §4.5 and Downey–Hirschfeldt §6 when writing H and I.

## 6. Conventions

- Files in `Gacs_Chapter_2/Randomness/`, one file per stage or theorem group,
  headers as in `DescriptionStatistics/`, snake_case names, module docstrings that
  state the Gács number and the deviation from his statement shape.
- `Learnings.md` gets every new Lean lesson; this file gets a progress log (§7) and
  the label ↔ Lean-name table per stage.
- Build roots: the last file of each stage; axiom check via a scratch file with
  `#print axioms`; forced rebuild of the folder for a zero-warning check.

## 7. Progress log

### 2026-09-11 — §2.1 complete, Theorem 2.1.1 (Martin-Löf)

Two files in `Gacs_Chapter_2/Randomness/`, 734 lines, two rounds of fixes each. All
theorems check against `[propext, Classical.choice, Quot.sound]`; forced rebuild gives
zero warnings; no `sorry`.

| Result (Gács label) | Lean name | File |
|---|---|---|
| Definition 2.1.2 (ML-test, universality) | `IsMLTestUniform`, `IsUniversalMLTestUniform` | `MartinLofTest.lean` |
| Definition 2.1.3 (`d₀`) | `mlDeficiency` | `MartinLofTest.lean` |
| Theorem 2.1.1, `d₀` is a test | `mlDeficiency_isMLTestUniform` | `MartinLofTest.lean` |
| Theorem 2.1.1, universality | `mlTest_le_mlDeficiency` | `MartinLofTest.lean` |
| Theorem 2.1.1, packaged | `mlDeficiency_isUniversalMLTestUniform` | `MartinLofTest.lean` |
| lsc infrastructure (Stage 0-lite) | `IsLSC₁`, `isLSC₁_complexityWeight_of_isRE`, `IsLSC₁.mul_natCast_left`, `IsLSC₁.dyadic_lt_isRE` | `LowerSemicomputable.lean` |

**What was done differently from the plan.**

- Stage 0 was cut to what §2.1 needs: the unary lsc notion `IsLSC₁` and its closure
  facts. `IsComputableENNReal` and Proposition 1.6.8 are still pending; they enter
  with computable measures in Stage C.
- Stage A was likewise cut to the uniform-distribution test; the general
  `IsMLTest`/`IsIntegrableTest` for arbitrary `P` and Prop 2.2.3 come with Stage C.
- The universality proof is Gács' proof verbatim through Levin's Theorem 1.5.3 from
  Chapter 1. The multiplicative `F` is the least `m` with `2^{|x|} < 2^m · t x`; its
  minimality gives the bound `2^F · t x ≤ 2^{|x|+1}`, which is where the constant
  `c + 1` (one bit above Levin's constant) comes from. The corner case `F = 0` is
  handled by the test condition at level `k = |x| + 1`.
- Condition (2.1.1) is formalized with `≤` (Gács writes `<` in the display and "at most"
  in the text); `≤` is what the proof of universality consumes and `d₀` satisfies it.

**Reusable output.** `LowerSemicomputable.lean` is the Stage-0 layer for the whole
chapter: generic fuel-bounded halting on any `Primcodable` type, three `IsRE`
combinators (`congr`, `comp`, `inter_decidable`), projection of a decidable relation
(`isRE_exists_of_computable`), and the three lsc closure lemmas.

Build: `lake build Gacs_Chapter_2.Randomness.MartinLofTest`.

### 2026-09-11 — §2.2 complete (Tier 1), Stages 0, A, C

Five new files, 1267 lines. All theorems check against
`[propext, Classical.choice, Quot.sound]`; forced rebuild gives zero warnings; no `sorry`.
The Lean sources moved to `Gacs_Chapter_2/Randomness/` and are built as the Lake library
`Gacs_Chapter_2` (two-line addition to `lakefile.toml`; module names
`Gacs_Chapter_2.Randomness.*`).

| Result (Gács label) | Lean name | File |
|---|---|---|
| Definition 1.5.1 (computable real function on strings) | `IsComputableENNReal` | `LSCAlgebra.lean` |
| computable probability measure | `ComputableMeasure` | `ComputableMeasure.lean` |
| Definition 2.2.1 (integrable test), ML-test for `P`, universality | `IsIntegrableTest`, `IsMLTest`, `IsUniversalIntegrableTest` | `ComputableMeasure.lean` |
| Proposition 2.2.3 (a), integrable ⇒ probability-bounded | `IsIntegrableTest.isMLTest` | `ComputableMeasure.lean` |
| Proposition 2.2.3 (b), probability-bounded ⇒ integrable after correction | `IsMLTest.mlCorrected_isIntegrableTest`, `le_mul_mlCorrected` | `MLToIntegrable.lean` |
| Definitions 2.2.4/2.2.7 (`d_P`, `t_P`) | `canonicalIntegrableTest` | `UniversalTest.lean` |
| **Theorem 2.2.1** (universal integrable test), `2^{-K}` form | `canonicalIntegrableTest_isUniversal` | `UniversalTest.lean` |
| **Theorem 2.2.1**, Gács' `m(x)/P(x)` form | `universalSemimeasure_div_isUniversal` | `UniversalTest.lean` |
| Proposition 2.2.5 (pushforward computable) | `pushforward` | `Conservation.lean` |
| **Theorem 2.2.2** (conservation under computable maps) | `canonical_pushforward_le` | `Conservation.lean` |
| Proposition 1.6.8 (lsc + total mass 1 ⇒ computable) | `IsLSC₁.isComputable_of_tsum_eq_one` | `Conservation.lean` |
| infrastructure | `IsLSC₁.of_ratApprox`, `IsLSC₁.of_ratSeq`, `IsLSC₁.mul`, `IsComputableENNReal.inv_isLSC₁`, `KP_le_isRE`, `prefixComplexityWeight_isLSC₁` | `LSCAlgebra.lean`, `UniversalTest.lean` |

**Design notes.**

- *Rationals are the working representation.* `IsLSC₁` insists on dyadic approximations
  at the stage's scale, which is wrong for products and reciprocals. `LSCAlgebra.lean`
  builds lsc from any computable rational sequence converging from below
  (`of_ratSeq`, via running maxima implemented with `Computable.nat_rec`, because Mathlib
  has no `Computable` list fold), and everything else is derived from that.
- *`IsComputableENNReal` is two rational sequences* squeezing `f` to within `2^{-k}`,
  not one sequence with an error bound. This makes `f` lsc and `1/f` lsc immediately
  (`inv_iInf` for the latter), which is exactly what Theorem 2.2.1 consumes.
- *Theorem 2.2.2 has no pointwise numerator bound.* `2^{-K(f x)}` can be much larger than
  `2^{-K(x)}`. Gács' proof shows instead that `x ↦ t_{f_*P}(f x)` is itself an integrable
  test for `P` (its expectation telescopes to `∑ 2^{-K} ≤ 1`) and applies universality.
  Formalized as such.
- *Proposition 1.6.8 does double duty.* It is the computability half of Proposition
  2.2.5: the pushforward mass is lsc as a growing finite sum of lower approximations and
  has total mass one.
- *Prop 2.2.3 (b) uses weights `2^k/((k+1)(k+2))`*, whose series telescopes to exactly
  one, so the correction is `d ↦ d − 2 log(d+2) − 1` with no free constant. Gács'
  `π²/6` normalisation is avoided.

**Deferred (Stage C′).** Theorem 2.2.3 and Corollary 2.2.8 (randomized transformations
`T(x, y)`), and the `K(d) + K(P)` constants of Theorems 2.2.1–2.2.2.

Build: `lake build Gacs_Chapter_2.Randomness.Conservation Gacs_Chapter_2.Randomness.MLToIntegrable`.

## 8. Numbering key (compiled PDF)

Definitions: 2.1.2 ML-test and universality · 2.1.3 `d₀` · 2.2.1 integrable test ·
2.2.4 `d_P` · 2.2.7 `t_P` · 2.3.5 measure over `Σ^ℕ` · 2.3.8 measure of an open set ·
2.3.10 null set · 2.3.13 constructive null set · 2.3.14 random sequence ·
2.3.29 integrable / ML test on sequences · 2.3.31 (continuous) semimeasure,
constructive · 2.3.32/2.3.35 `M` · 2.3.33 monotone machine · 2.3.34 `P_T` · 2.3.36 `KM` ·
2.3.38 `d′_P`.

Results: Thm 2.1.1 (Martin-Löf) · Prop 2.2.3 · Thm 2.2.1 · Prop 2.2.5 · Thm 2.2.2 ·
Thm 2.2.3 · Cor 2.2.8 · Lemma 2.3.6 · Cor 2.3.7 · Prop 2.3.9 · Prop 2.3.12 · Thm 2.3.1 ·
Thm 2.3.2 · Thm 2.3.3 · Thm 2.3.4 · Cor 2.3.30 · Thm 2.3.5 · Thm 2.3.6 · Prop 2.3.37 ·
Thm 2.3.7.

Out of scope (Mathlib territory): Defs 2.3.15–2.3.28 and Props 2.3.19, 2.3.21,
2.3.24, 2.3.26, 2.3.28.

### 2026-09-18 — namespace change

All files under `Gacs_Chapter_2/Randomness/` moved from `namespace Kolmogorov` to
`namespace Kolmogorov.Randomness`. Thirteen declarations here carried the same
fully-qualified name as declarations in `KolmogorovMathlib`, which no file had noticed
because nothing imported both library roots; `lake exe checkdecls`, which imports every
module of every library, fails outright on the first such clash. The collisions were
`IsLSC₁`, `IsLSC.toUnary`, `IsComputableENNReal`, `IsLSC₁.comp_computable`, `goodStage`
and its three companions, `exists_goodStage`, `natLe_primrec`, `natPow_primrec`,
`sum_range_getD_eq`, `cylinder` and `mem_cylinder`. Note that several of these were *not*
the same statement: our `IsComputableENNReal` is the two-sided lo/hi version and Chapter
1's is one-sided, so merging them would have been wrong.

One exception: `IsRE.congr`, `IsRE.comp` and `IsRE.inter_decidable` extend a type from
Chapter 1, so they are declared `_root_.Kolmogorov.IsRE.*` and dot notation on an `IsRE`
value keeps working. Anything about our own types needs no such treatment.

Nothing else changed; `lake build Gacs_Chapter_2` is green.

### Backfill — §2.3 files committed without a log entry ("update missing proofs")

Stages D and E, and Theorem 2.3.2, were committed without an entry here. Checked on
2026-11-07: they build and contain no `sorry`. The main declarations:

| Result (Gács label) | Lean name | File |
|---|---|---|
| Definition 2.3.1, cylinders, open sets by generators, compactness | `cylinder`, `openOf`, `exists_level_of_cylinder_subset` | `Sequences.lean` |
| Definition 2.3.5 (measure on `Σ^ℕ`), computable measure, uniform `λ` | `IsSeqMeasure`, `ComputableSeqMeasure`, `uniformSeqMeasure` | `SeqMeasure.lean` |
| Definition 2.3.8 (measure of an open set) | `openMeasure` (sup of level masses) | `SeqMeasure.lean` |
| Lemma 2.3.6 (depends only on the open set) | `openMeasure_mono_openOf` | `SeqMeasure.lean` |
| Prop 2.3.9, countable subadditivity | `openMeasure_iUnion_le`, `openMeasure_le_tsum` | `SeqMeasure.lean` |
| Definitions 2.3.10, 2.3.13, 2.3.14; Prop 2.3.12 | `IsNullSet`, `IsConstructiveNull`, `IsRandomSeq`, `isNullSet_iUnion` | `SeqMeasure.lean` |
| Definition 2.3.29 (tests on sequences), Markov | `IsIntegrableSeqTest`, `IsMLSeqTest`, `IsIntegrableSeqTest.isMLSeqTest` | `SeqTest.lean` |
| **Theorem 2.3.2** (a), (b) | `isConstructiveNull_seqVal_top`, `exists_integrableSeqTest_of_constructiveNull` | `SeqTest.lean` |
| Definition 2.3.31, **Theorem 2.3.5** (universal `M`) | `IsContSemimeasure`, `univContSemimeasure_isUniversal` | `UniversalContSemimeasure.lean` (+ `ContTrim*.lean`) |
| Definition 2.3.36, **Proposition 2.3.37** | `KM_bounds` | `KMBounds.lean` |

Corollary 2.3.7 (`P(G) = ∑ P(x)` for prefix-free generators) is not stated as an equality.
Both inequalities exist: `openMeasure_le_tsum`, and from 2026-11-07
`sum_le_levelMass_of_prefixFree`.

### 2026-11-07 — §2.3 complete (Tier 1), Stages F, G, H, I, C′

Four new files, 1393 lines: `PrefixFreeMass.lean` (244), `LevinSchnorr.lean` (639),
`RandomnessViaM.lean` (196) and `RandomizedConservation.lean` (314, written by a parallel
agent). All main theorems depend only on `[propext, Classical.choice, Quot.sound]`; a forced
rebuild of the four files gives zero warnings; no `sorry`.

| Result (Gács label) | Lean name | File |
|---|---|---|
| Thm 2.3.4, `≤` direction (the key lemma) | `seqVal_le_of_isIntegrableSeqTest` | `LevinSchnorr.lean` |
| `R(ξ) = sup_n 2^{-K(ξ_{1:n})}/P(ξ_{1:n})` | `complexityRatioSup` | `LevinSchnorr.lean` |
| Thm 2.3.4, `≥` direction (the test property) | `levelIntegral_canonicalSeqTest_le`, `canonicalSeqTest_isIntegrable` | `LevinSchnorr.lean` |
| **Theorem 2.3.3** (universal integrable test on sequences) | `canonicalSeqTest_isUniversal` | `LevinSchnorr.lean` |
| **Theorem 2.3.4** | `universalSeqTest_equiv` | `LevinSchnorr.lean` |
| **Theorem 2.3.1** (universal constructive null set) | `isConstructiveNull_universalNull`, `subset_universalNull` | `LevinSchnorr.lean` |
| random ⇔ `R(ξ) < ∞` | `isRandomSeq_iff` | `LevinSchnorr.lean` |
| **Corollary 2.3.30** | `uniform_universalSeqTest_equiv` | `LevinSchnorr.lean` |
| **Levin–Schnorr**: λ-random ⇔ `∃ c ∀ n, n ≤ K(ξ_{1:n}) + c` | `isRandomSeq_uniform_iff` | `LevinSchnorr.lean` |
| Definition 2.3.38 (`δ'_P`) | `ratioTest` | `RandomnessViaM.lean` |
| **Theorem 2.3.7** (`δ'` is an ML test) | `ratioTest_isMLSeqTest` | `RandomnessViaM.lean` |
| `δ' ≥ d̄`, same random sequences | `complexityRatioSup_le_ratioTest`, `isRandomSeq_iff_ratioTest` | `RandomnessViaM.lean` |
| `KM ≤⁺ −log P`; `KM ≈ −log P` along random sequences | `seqMeasure_le_univ`, `univ_comparable_on_random` | `RandomnessViaM.lean` |
| transition, image measure | `ComputableTransition`, `ComputableTransition.image` | `RandomizedConservation.lean` |
| **Theorem 2.2.3** | `transTest_isIntegrableTest`, `transTest_le_canonical` | `RandomizedConservation.lean` |
| **Corollary 2.2.8** | `transition_deficiency_tail` | `RandomizedConservation.lean` |
| Thm 2.2.2 as the deterministic case of 2.2.3 | `detTransition`, `det_canonical_image_le` | `RandomizedConservation.lean` |
| combinatorics | `sum_le_levelMass_of_prefixFree`, `sum_le_one_of_prefixFree`, `sum_ext_take_mul`, `tsum_levels_le`, `le_of_forall_levels` | `PrefixFreeMass.lean` |
| lsc of `x ↦ ∑_y g(x,y) h(y)` | `isLSC₁_tsum_mul`, `isLSC_swap` | `RandomizedConservation.lean` |

**What was done differently from the plan.**

- *One key lemma carries §2.3.* The plan had Stage F (Theorem 2.3.1) built by
  measure-guarded enumeration, and Stage G's Theorem 2.3.3 by a projection over an
  enumeration of trimmed tests. Neither is needed. The hard half of Theorem 2.3.4, that
  every integrable test `T` satisfies `T(ξ) ≤ 2^c R(ξ)`, makes `max_{y⊑·} 2^{-K(y)}/P(y)`
  universal (Theorem 2.3.3). Theorem 2.3.1 then follows from Theorem 2.3.2: every
  constructive null set lies in `{T = ∞}` for an integrable `T`, so it lies in `{R = ∞}`.
  The trade: the universal test is the explicit complexity test, not an abstract mixture.
- *Gács' decomposition made decidable.* His proof of the key lemma writes `2^{⌈d⌉}` as
  `sup_i 2^{k_i} 1_{y_i}` with the `k_i` increasing along every sequence, and leaves the
  enumeration implicit. We use dyadic levels `{T > 2^{k+1}}`. A string *hits* level `k`
  when the stage-`|z|` approximation, maximised over prefixes, exceeds `2^{k+1}`
  (`hitB`). It is a *first hit* when no proper prefix hits (`firstB`). Tying the stage to
  the length makes hits monotone along prefixes and first hits **decidable** and
  prefix-free, with no minimality over an r.e. set. Then `γ(z) = ∑_{first hits} 2^k` is
  computable, the layer cake gives `∑ P γ ≤ ∫ T ≤ 1`, and the coding theorem gives
  `γ ≤ 2^c w/P`.
- *Theorem 2.3.7 needs no enumeration either.* The measure bound
  `P{δ' > 2^k} ≤ 2^{-k}` is pure combinatorics: prefix-minimal witnesses of length `≤ n`
  form a finite prefix-free family, and a continuous semimeasure has mass `≤ 1` on such a
  family. Universality and lower semicomputability are used only for the test's lsc
  property and for the comparisons.
- *Transitions are only required to be lsc* (Theorem 2.2.3). With rows summing to one,
  this already implies computability (Prop 1.6.8 row by row), and it is exactly what the
  proof consumes.
- *Estimates.* F + G + H + I came in at about 1080 lines against a plan of 3100, because
  the key lemma replaced two enumeration constructions.

### 2026-11-07 (evening) — Tier 2: the constants `K(d) + K(P)`

Three new files, 1047 lines: `Descriptions.lean` (353), `ExactSeqTest.lean` (298) and
`ExactConservation.lean` (396). The last two were written by two parallel agents on top of
the first. All main theorems depend only on `[propext, Classical.choice, Quot.sound]`; a
forced rebuild gives zero warnings; no `sorry`.

| Result (Gács label) | Lean name | File |
|---|---|---|
| description of an lsc function; every lsc function has one | `IsLSCDescription`, `exists_lscDescription` | `Descriptions.lean` |
| indexed domination (the engine) | `indexed_domination`, `indexed_domination_trim`, `contIndexed_domination` | `Descriptions.lean` |
| `K(⟨y, y'⟩) ≤⁺ K(y) + K(y')` | `exists_pairCode_weight` | `Descriptions.lean` |
| exact coding theorem `m(x) ≥ 2^{-K(ν)} ν(x)` (§1.6, used in 2.2.1) | `semimeasure_le_exact` | `Descriptions.lean` |
| `M(x) ≥ 2^{-K(ν)} ν(x)` for continuous `ν` (§2.3.7) | `contSemimeasure_le_univ_exact` | `Descriptions.lean` |
| **Theorem 2.2.1** with `K(d) + K(P)` | `integrableTest_le_canonical_exact`, `…_exact'` (exponent form) | `Descriptions.lean` |
| **Theorem 2.2.3** with `K(T) + K(P)` | `transTest_le_canonical_exact` | `ExactConservation.lean` |
| **Corollary 2.2.8** with `K(T) + K(P)` | `transition_deficiency_tail_exact` | `ExactConservation.lean` |
| **Theorem 2.2.2** with `K(f) + K(P)` | `det_canonical_image_le_exact` | `ExactConservation.lean` |
| **Theorem 2.3.3** with `K(d) + K(P)` | `seqVal_le_exact`, `seqVal_le_canonicalSeqTest_exact`, `seqVal_le_exact'` | `ExactSeqTest.lean` |

**Design.**

- *What `K(d)` means.* A bit string `y` describes an lsc function `f` (`IsLSCDescription y f`)
  when the `bitsToNat y`-th component of the upstream enumeration of lsc approximations
  (`approxEnum`, i.e. a `Nat.Partrec.Code`, monotonised as `enumApprox`) converges to `f`.
  `K(f)` is read as `K(y)`. All statements quantify over descriptions, so they hold for a
  shortest one. Transitions are described on encoded pairs
  (`q ↦ T(decodeFirst q, decodeSecond q)`), maps by their graph indicator; both agree with
  "a program for `T`/`f`" up to `O(1)`. `K(P)` needs only a *lower* description of `P`.
- *One engine.* `indexed_domination_trim`: for any jointly lsc family `G(x, z)`,
  `2^{-K(z)} G(x, z) ≤ 2^c 2^{-K(x)}` at every `z` where `G(·, z)` is a semimeasure. Proof:
  trim with the upstream `truncG` (uniform in the context), mix with Kraft weights `2^{-K(z)}`
  (`isLSC₁_tsum_mul`), apply the coding theorem. Each Tier-2 theorem is then one jointly lsc
  family indexed by `z = pairCode y_d y_P` that equals the theorem's semimeasure at valid
  `z`, plus `exists_pairCode_weight`. No code-level composition of programs is needed.
- *Joint lower semicomputability of the families* goes through two plumbing lemmas,
  `IsLSC.comp₁` (read a jointly lsc function along computable maps) and `IsLSC₁.toLSC₂`
  (read a unary one at `pairCode x z`), so the unary lsc algebra (`mul`, `of_ratSeq`, …)
  applies.
- *`1/Q` for an image measure* is upper, not lower, semicomputable. When `Q` has total mass
  one, `Q(y) = 1 − ∑_{y'≠y} Q(y')`, and `a ↦ (1 − a)⁻¹` preserves lsc
  (`exact_isLSC₁_one_sub_inv`).
- *Theorem 2.3.3* reruns the key lemma of `LevinSchnorr.lean` uniformly in `z`: the
  computability of `hitB`/`firstB`/`gamN` is re-proved with a parameter
  (`gamN_computable_param`).

## 9. What remains in Chapter 2

1. **Stage J, Theorem 2.3.6** (monotone machines realise every constructive semimeasure).
   Optional; nothing depends on it.
2. **Stage K**, the bridge to `MeasureTheory.Measure (ℕ → Bool)`. Optional.
3. Smaller items: Corollary 2.3.7 as an equality; the remark that `δ'` is not
   expectation-bounded (needs a counterexample); the bridge from `ComputableMeasure` to
   the upstream `CodedFiniteDistribution`; long-line lint warnings in `KMBounds.lean`.
