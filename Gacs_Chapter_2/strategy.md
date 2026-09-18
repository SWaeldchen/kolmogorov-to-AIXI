# Strategy — Formalizing Gács Chapter 2, "Randomness"

Companion to `../../Strategy.md` (Chapter 1). Same conventions: multiplicative
statements in `ℝ≥0∞`, no logarithms, explicit constants, numbering as in the compiled
PDF, every stage closed with an axiom check and a warning sweep. New Lean files go in
a new subfolder `Gacs_Chapter_2/Randomness/`; existing files are not edited.

Status (2026-09-11): **§2.1 and §2.2 (Tier 1) complete**: seven files in
`Gacs_Chapter_2/Randomness/`, 2001 lines, axiom-clean, no warnings, no `sorry`. Stage C′
(Theorem 2.2.3, Corollary 2.2.8, index-dependent constants) is the remaining part of §2.2.
The Lean files live in the `Gacs_Chapter_2` Lake library (added to `lakefile.toml`). See §7.

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
| **C′** | §2.2 Tier 2: constants `K(d) + K(P)` via indexed enumeration; Thm 2.2.3 and Cor 2.2.8 (randomized transformations `T(x,y)`) | 700 | C |
| **D** | §2.3 string-level foundations: sequences, cylinders, measures on strings, uniform `λ`, open sets and their measure (Lemma 2.3.6, Cor 2.3.7, Prop 2.3.9), null sets, Prop 2.3.12 (countable union), constructive null sets, randomness | 900 | 0 |
| **E** | §2.3.7: `IsContSemimeasure`, constructive, **Thm 2.3.5** universal `M` by adapted trimming; `KM`; Prop 2.3.37 `KM ≤⁺ K ≤⁺ KM + K(|x|)` | 1500 | 0, D |
| **F** | Thm 2.3.1 universal constructive null set (projection over codes with measure-guarded enumeration) | 800 | D |
| **G** | Thm 2.3.2 tests ↔ null sets; Thm 2.3.3 universal integrable test on sequences (Tier 1, then Tier 2) | 900 | D, F |
| **H** | Thm 2.3.4 and Cor 2.3.30: `d_μ(ξ) =⁺ sup_n (−log μ(ξ_{1:n}) − K(ξ_{1:n}))`, randomness of a sequence ⇔ incompressibility of prefixes | 900 | G, coding theorem |
| **I** | §2.3.8: Def 2.3.38 `d′_P`, Thm 2.3.7 (it is an ML-test), relation to `d_P` | 500 | E, G |
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
