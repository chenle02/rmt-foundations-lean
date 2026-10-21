<div align="center">

<img src="docs/assets/mark.svg" width="88" height="88" alt="rmt-foundations mark: a curve over three bars">

# rmt-foundations

Tracy–Widom distributions, Airy and Painlevé II theory, finite GUE identities
and analytic random-matrix tools, formalized in Lean 4.

[![CI](https://github.com/chenle02/rmt-foundations-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/chenle02/rmt-foundations-lean/actions/workflows/ci.yml)
[![Docs](https://img.shields.io/badge/docs-GitHub%20Pages-153e63)](https://chenle02.github.io/rmt-foundations-lean/)
[![Version](https://img.shields.io/badge/version-0.2.0-153e63)](CITATION.cff)
[![Lean](https://img.shields.io/badge/Lean-v4.35.0-153e63)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache--2.0-153e63)](LICENSE)

[What is proved](#what-is-proved) · [Verification page](docs/verification.md) · [Build](#build-and-verify) · [Cite](#citation)

</div>

## What is proved

Every item below is a Lean declaration checked by the kernel. The hypotheses
of each declaration are part of the claim. Declaration names are given
relative to the namespace `RMTFoundations`.

- **TW1 and TW2 (GOE and GUE).** The distribution functions, defined as
  Fredholm determinants of Airy kernels, are globally smooth and
  strictly increasing, with limits 0 and 1. Each is the distribution function
  of a unique probability measure, with a globally smooth positive density, unique
  quantiles, an exponential moment and all absolute moments. Both have sharp
  right-tail asymptotics, left-tail bounds of linear exponential order, and
  the Painlevé II integral representations of $F_2$ and $F_1^2$.
  (`TracyWidom.strictMono_TW1R`, `TracyWidom.TW1Measure_unique`,
  `TracyWidom.TW2_rightTail_isEquivalent`, `TracyWidom.Painleve.TW2R_integral_formula`.)
- **Hastings–McLeod.** Painlevé II has exactly one real global solution with
  relative Airy normalization at $+\infty$, and it equals the Fredholm
  response. (`TracyWidom.HastingsMcLeod.exists_unique`,
  `TracyWidom.HastingsMcLeod.eq_canonical`.)
- **TW4 (GSE).** The determinant-average function is positive and $C^1$, has
  limits 0 and 1, attains every level in $(0,1)$, and has a closed formula in
  terms of TW2 and the Painlevé II solution. (`TracyWidom.TW4R_positive`,
  `TracyWidom.TW4AiryR_eq_sqrt_TW2R_cosh_tail`.)
- **Airy2.** The extended Airy kernel, its integral realization, and the
  reduction of the one-time expression to TW2.
  (`TracyWidom.Airy2.extendedAiryKernel_eq_integral`,
  `TracyWidom.Airy2.airy2FredholmCandidate_one_time`.)
- **Finite GUE.** Hermite Christoffel–Darboux identities, the normalized
  determinantal eigenvalue density with its projection kernel, and the GUE
  matrix model with the distribution function of its largest eigenvalue.
  (`TracyWidom.GUEHermite.hermite_christoffel_darboux`,
  `TracyWidom.GUEProjection.gue_projection_determinantal_ensemble`,
  `TracyWidom.GUEIdentification.gueCDF`.)
- **Analytic tools.** The Airy function and its asymptotics, Fredholm series,
  Stieltjes transforms (analyticity, inversion, Herglotz–Borel
  representation), the Marchenko–Pastur law, semicircle moments, free
  convolution subordination, Bernstein and Chernoff bounds, the
  moment–cumulant recursion, resolvent identities, and simple stochastic
  integrals against Brownian motion. For example, for $0<y<1$ the
  Marchenko–Pastur measure has density
  $\sqrt{(b-x)(x-a)}/(2\pi y x)$ on $[a,b]$ with $a=(1-\sqrt y)^2$, $b=(1+\sqrt y)^2$
  (`MarchenkoPastur.mpMeasure_density`), and for a finite measure $\nu$ and $a<b$,
  $`\lim_{\eta\downarrow0}\int_a^b \operatorname{Im} S_\nu(x+i\eta)\,dx=\pi\big(\nu((a,b))+\tfrac12\nu(\lbrace a\rbrace)+\tfrac12\nu(\lbrace b\rbrace)\big)`$
  (`StieltjesInversion.tendsto_interval_im`).

The 16 main results of [`coverage.yaml`](coverage.yaml), each with its Lean
statement and a plain-language statement beside it, are on the
[verification page](docs/verification.md); the same page is rendered
[below](#verification-at-a-glance). The
[status page](https://chenle02.github.io/rmt-foundations-lean/status.html)
names the declaration behind each item above.

> [!IMPORTANT]
> **Not proved here.**
> - **TW4:** monotonicity, and hence a TW4 probability measure. On this point
>   the library proves only that monotonicity is equivalent to a resolvent
>   sign condition.
> - **GUE edge limit:** the identification of the GUE edge limit with TW2
>   assumes the convergence hypothesis `GUELimit TW2R`. That convergence is
>   not proved. The finite-$N$ density is not proved to be the eigenvalue law
>   of the matrix model.
> - **Multi-time Airy2:** the distinct-time finite-ensemble joint-limit
>   producer remains open. The probability limit theorems retain explicit
>   finite-law joint-limit and scalar coordinate-limit hypotheses.
> - **Left tails:** sharp cubic left-tail asymptotics are not established.
>
> General local laws, universality and general Itô integration are outside
> the scope of this library.

## Paper and references

The [Tracy–Widom guide](docs/tracy-widom.md) covers smoothness, Hermite-to-Airy
limits, finite stationary Dyson laws, conditional Airy2 probability limits and
TW4 tail and compact-window certificates. Distinct-time convergence and all
certificate hypotheses remain explicit.

The [status page](https://chenle02.github.io/rmt-foundations-lean/status.html)
names the declaration behind each item.

Standalone library; the motivating paper (with Haoran Li) is in preparation.

Some proofs are adapted from other Apache-2.0 Lean sources, recorded in
[NOTICE](NOTICE): spectral results from Adam Benenson's *compact-spectral*
(license bundled as [compact-spectral-LICENSE](compact-spectral-LICENSE)),
derivative and weighted-pairing proofs from the
[Tau Ceti](https://github.com/TauCetiProject/TauCeti) project (license bundled
as [TauCeti-LICENSE](TauCeti-LICENSE)), and regularized hypergeometric
material derived from [Mathlib](https://github.com/leanprover-community/mathlib4).

## Build and verify

Install [elan](https://github.com/leanprover/elan). The toolchain is the
stable release **Lean v4.35.0**, pinned in `lean-toolchain`. Mathlib is
pinned in `lake-manifest.json`.

```sh
git clone https://github.com/chenle02/rmt-foundations-lean.git
cd rmt-foundations-lean
lake exe cache get
lake build
```

[`examples/Quickstart.lean`](examples/Quickstart.lean) is a small consumer.
The full verification is one script:

```sh
bash scripts/verify.sh
```

It checks the source policy, builds every module, test and example from a
clean project build, compares the `#print axioms` output with
[`EXPECTED-AXIOMS.txt`](EXPECTED-AXIOMS.txt), and replays each compiled module
through `leanchecker`. It needs the pinned toolchain and Python 3.

To use the library from another Lake project, use the same `lean-toolchain`
and add to `lakefile.toml`:

```toml
[[require]]
name = "RMTFoundations"
git = "https://github.com/chenle02/rmt-foundations-lean.git"
rev = "v0.2.0"
```

Then run `lake update RMTFoundations`, `lake exe cache get` and `lake build`,
and write `import RMTFoundations`. The
[dependency guide](https://chenle02.github.io/rmt-foundations-lean/dependency.html)
covers narrower imports and version pinning.

**Documentation.** GitHub Pages publishes the guided site from branch `main`,
folder `/docs`, with its built-in Jekyll build. The pinned package in
[`docbuild/`](docbuild/README.md) builds the full API reference locally:

```sh
lake exe cache get
cd docbuild
lake -R -Kenv=dev build RMTFoundations:docs
python3 -m http.server --directory .lake/build/doc 8000
```

## Find your way

| If you want to | Start here |
|---|---|
| Use the library | [Getting started](https://chenle02.github.io/rmt-foundations-lean/getting-started.html) · [examples/](examples/) |
| Find a theorem | [Module map](https://chenle02.github.io/rmt-foundations-lean/modules.html) · [Declaration index](https://chenle02.github.io/rmt-foundations-lean/declarations.html) · [claims.yaml](claims.yaml) |
| Check the evidence | [Verification page](docs/verification.md) · [Coverage](docs/coverage.md) · [Trust and reproducibility](https://chenle02.github.io/rmt-foundations-lean/trust.html) · [formalization.yaml](formalization.yaml) · [EXPECTED-AXIOMS.txt](EXPECTED-AXIOMS.txt) |
| Contribute or use an agent | [CONTRIBUTING.md](CONTRIBUTING.md) · [AGENTS.md](AGENTS.md) · [llms.txt](llms.txt) |

## Trust and axioms

Proofs use only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry`, `admit`, custom axiom or `native_decide`.
The recorded build check at commit `df8d037ff7db` found `sorry` count 0 and
exactly these three axioms, and lean-pkg's claims ledger closes all 66
required claims of [`claims.yaml`]; its axiom check covers all 384 claims.
For the 16 main results of
[`coverage.yaml`](coverage.yaml), the comparator confirmed that the proof in
[`Solution.lean`](Solution.lean) proves exactly the statement in
[`Challenge.lean`](Challenge.lean) (the reference statements under
[`Challenge/`](Challenge/)), with only the permitted axioms, and independent
kernels replayed it. The other declarations listed above are covered by the
build check and the axiom comparison of `scripts/verify.sh`, not by the
comparator. The build check ran on Lean `v4.35.0` (see
[How this was checked](#how-this-was-checked)).
A kernel check confirms a proof; it does not remove any hypothesis from the
statement. Details and receipts:
[What the checks establish](#what-the-checks-establish).

## Built with lean-pkg

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
The receipts under [`.lean-receipts/`](.lean-receipts/) bind the checks to a
source commit, and the verification section below is rendered by
`lean-pkg page` from [`coverage.yaml`](coverage.yaml),
[`claims.yaml`](claims.yaml) and those receipts;
`lean-pkg page rmt-foundations --check --site docs` confirms that it and
[`docs/verification.md`](docs/verification.md) are current.

## Authors and AI disclosure

**Le Chen**, Associate Professor, Department of Mathematics and Statistics,
Auburn University.

Haoran Li — co-author of the research paper that motivated this library and
proposer of the problem.

Development used OpenAI Codex (gpt-6.1-sol) workers, with Anthropic Claude for
orchestration and independent audits. Every result is kernel-checked and
depends only on `propext`, `Classical.choice` and `Quot.sound`. Hypotheses and
limitations are stated explicitly in the theorem statements.

Released under [Apache-2.0](LICENSE). See [NOTICE](NOTICE) for third-party
attributions and the bundled [compact-spectral](compact-spectral-LICENSE) and
[Tau Ceti](TauCeti-LICENSE) licenses. Please cite *rmt-foundations*, version
0.2.0, by Le Chen, and record the source commit you used. Metadata is in
[CITATION.cff](CITATION.cff). See also the
[citation page](https://chenle02.github.io/rmt-foundations-lean/citation.html).

The generated verification record below describes the published v0.1.0
release. Commit-specific build evidence is stored in `.lean-receipts/`.

<!-- lean-pkg:page:begin -->
<!-- Generated by `lean-pkg page rmt-foundations` from coverage.yaml, claims.yaml, the claims ledger and the receipts committed under .lean-receipts/. Do not edit between the markers: change the data and run `lean-pkg page rmt-foundations --write`. -->

## Verification at a glance

**How to read this page.** Lean has checked every step of the proofs listed here. Each result is exactly its Lean statement: read the statements below to see what is proved. The titles, the words and the notes are the authors' description, which Lean does not check.

Kernel-checked foundations for random matrix theory (Airy function and kernel, Fredholm series, order-one Tracy-Widom monotonicity, moment-cumulant recursion, resolvent identity, Marchenko-Pastur law, Stieltjes transform and inversion, Herglotz-Borel representation, free-convolution subordination); 16 main results compared. Version 0.2.0 adds Tracy-Widom smoothness and Hermite-Airy limits.

- Main results: 16; verified: 16 of 16.

## Main results

### The actual real Airy function satisfies its second-order ODE

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For every real $x$, the real Airy function satisfies
\[ \operatorname{Ai}''(x) = x\,\operatorname{Ai}(x). \]
Here $\operatorname{Ai}$ on $\mathbb{R}$ is the real part of the complex Airy function.
```

**In Lean.** `RMTFoundations.Airy.iteratedDeriv_two_airyAiReal` in [Challenge/Reference/Airy/Core.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Airy/Core.lean#L1147): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem iteratedDeriv_two_airyAiReal (x : ℝ /- [definition] -/ ) :
    iteratedDeriv 2 airyAiReal x = x * airyAiReal x
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The genuine shifted Airy kernel operator is trace class

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For every real $s$, let $A_s$ be the integral operator on $L^2(0,\infty)$ with kernel
$\operatorname{Ai}(x+y+s)$. Then $K_s = A_s \circ A_s$ is trace class, that is, a composition of two
Hilbert--Schmidt operators.
```

**In Lean.** `RMTFoundations.Airy.isTraceClass_airyKernelShift` in [Challenge/Reference/Airy/Core.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Airy/Core.lean#L8894): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem isTraceClass_airyKernelShift (s : ℝ /- [definition] -/) :
    IsTraceClass (airyKernelShift s)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Factorially bounded coefficients give an entire Fredholm power series

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $c_n \in \mathbb{C}$ and $M \ge 0$ satisfy $|c_n| \le M^n / n!$ for all $n \ge 0$. Then the power series
\[ z \mapsto \sum_{n \ge 0} c_n z^n \]
is analytic on all of $\mathbb{C}$.
```

**In Lean.** `RMTFoundations.Fredholm.fredholmSeries_entire` in [Challenge/Reference/Operator/Fredholm.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Operator/Fredholm.lean#L92): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem fredholmSeries_entire
    (c : ℕ → ℂ /- [definition] -/ )
    (M : ℝ /- [definition] -/ )
    (hM : 0 ≤ M /- [standing] -/ )
    (hc : ∀ n, ‖c n‖ ≤ M ^ n / (n.factorial : ℝ)  /- [standing] -/ )
    : AnalyticOnNhd ℂ (fredholmSeries c) Set.univ
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The canonical real order-one Airy kernel series is monotone

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $F_1(s)$ be the real part of the Fredholm series, at coupling $-1$, of the kernel
$\operatorname{Ai}(x+y+s)$ on $(0,\infty)$ (formally $\det(I - A_s)$). Then $s \mapsto F_1(s)$ is
nondecreasing on $\mathbb{R}$.
```

**In Lean.** `RMTFoundations.TWOneMonotone.monotone_TW1R` in [Challenge/Reference/TracyWidom/OrderOneMonotone.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/TracyWidom/OrderOneMonotone.lean#L51791): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem monotone_TW1R : Monotone TW1R
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Analytic moment-cumulant recursion at zero on the interior of the exponential integrability set

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $X$ be a real random variable on a space with a nonzero measure $\mu$, and suppose $0$ lies in the
interior of the set of $t$ for which $e^{tX}$ is $\mu$-integrable. Then for every $n \ge 0$,
\[ \int X^{n+1}\,d\mu = \sum_{j=0}^{n} \binom{n}{j}\, \kappa_{j+1} \int X^{n-j}\,d\mu, \]
where $\kappa_m$ is the $m$-th derivative at $0$ of the cumulant generating function of $X$.
```

**In Lean.** `RMTFoundations.Cumulants.moment_succ_eq_sum_cumulant_mul_moment` in [Challenge/Reference/Probability/Cumulants.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Probability/Cumulants.lean#L63): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem moment_succ_eq_sum_cumulant_mul_moment [NeZero μ /- [standing] -/ ]
    (h : (0 : ℝ) ∈ interior (integrableExpSet X μ)  /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    μ[X ^ (n + 1)] = ∑ j ∈ Finset.range (n + 1),
      (n.choose j : ℝ) * cumulant (j + 1) X μ * μ[X ^ (n - j)]
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### First resolvent identity for two invertible shifts of an arbitrary finite complex matrix

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $H$ be a square complex matrix and $z_1, z_2 \in \mathbb{C}$ such that $H - z_1 I$ and $H - z_2 I$
are invertible. Then
\[ (H - z_1 I)^{-1} - (H - z_2 I)^{-1} = (z_1 - z_2)\,(H - z_1 I)^{-1}(H - z_2 I)^{-1}. \]
```

**In Lean.** `RMTFoundations.Resolvent.resolvent_identity` in [Challenge/Reference/Matrix/Resolvent.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Matrix/Resolvent.lean#L23): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem resolvent_identity (H : Matrix n n ℂ /- [definition] -/ ) (z₁ z₂ : ℂ /- [definition] -/ )
    (h₁ : IsUnit (H - z₁ • (1 : Matrix n n ℂ)).det /- [standing] -/ )
    (h₂ : IsUnit (H - z₂ • (1 : Matrix n n ℂ)).det /- [standing] -/ ) :
    (H - z₁ • (1 : Matrix n n ℂ))⁻¹ - (H - z₂ • (1 : Matrix n n ℂ))⁻¹
      = (z₁ - z₂) • ((H - z₁ • (1 : Matrix n n ℂ))⁻¹ * (H - z₂ • (1 : Matrix n n ℂ))⁻¹)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Signed real-parameter complex-valued Taylor integral remainder

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $F : \mathbb{R} \to \mathbb{C}$ be $K+1$ times continuously differentiable. Then for every real $h$,
of either sign,
\[ F(h) - \sum_{j=0}^{K} \frac{h^j}{j!}\, F^{(j)}(0) = \int_0^h \frac{(h-t)^K}{K!}\, F^{(K+1)}(t)\,dt. \]
```

**In Lean.** `RMTFoundations.Taylor.remainder_eq_interval_integral` in [Challenge/Reference/Analysis/Taylor.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Analysis/Taylor.lean#L37): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem remainder_eq_interval_integral (F : ℝ → ℂ /- [definition] -/ ) (K : ℕ /- [definition] -/ )
    (hF : ContDiff ℝ (K+1 : ℕ) F /- [standing] -/ ) (h : ℝ /- [standing] -/ ) :
    remainder F K h = ∫ t in (0:ℝ)..h,
      ((h-t)^K / (K.factorial : ℝ)) • iteratedDeriv (K+1) F t
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Scalar binomial repeated-edge walk-count majorant; does not count walks itself

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For natural numbers $k, v, s$ with $v \ge 1$ and $k + 2 = 2v + s$,
\[ \binom{k}{2v-2}\, v^{2s}\, 2^{2v-2} \le 2^k\, k^{3s}. \]
This is the scalar inequality used to bound walk counts; it does not itself count walks.
```

**In Lean.** `RMTFoundations.WalkMajorant.walk_count_majorant` in [Challenge/Reference/Combinatorics/WalkMajorant.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Combinatorics/WalkMajorant.lean#L17): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem walk_count_majorant (k v s : ℕ /- [definition] -/ ) (hv : 1 ≤ v /- [standing] -/ ) (hk : k + 2 = 2 * v + s /- [standing] -/ ) :
    (k.choose (2 * v - 2) : ℝ) * (v : ℝ) ^ (2 * s) * 2 ^ (2 * v - 2)
      ≤ 2 ^ k * (k : ℝ) ^ (3 * s)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Any two Airy ODE solutions with identical first-order initial data agree

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Suppose $(f, f')$ and $(g, g')$ both solve the Airy equation on $\mathbb{R}$: $f$ has derivative $f'$
and $f'$ has derivative $x f(x)$ at every $x$, and likewise for $g$ and $g'$. If $f(t_0) = g(t_0)$ and
$f'(t_0) = g'(t_0)$ at some point $t_0$, then $f = g$.
```

**In Lean.** `RMTFoundations.Airy.airySolution_unique` in [Challenge/Reference/Airy/ODE.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Airy/ODE.lean#L221): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem airySolution_unique (hf : IsAirySolution f f' /- [standing] -/ ) (hg : IsAirySolution g g' /- [standing] -/ ) {t₀ : ℝ /- [definition] -/ }
    (h0 : f t₀ = g t₀ /- [standing] -/ ) (h1 : f' t₀ = g' t₀ /- [standing] -/ ) : f = g
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The finite-measure Stieltjes transform is analytic on the upper half-plane

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For every finite measure $\mu$ on $\mathbb{R}$, the Stieltjes transform
\[ S_\mu(z) = \int \frac{d\mu(x)}{x - z} \]
is analytic on the upper half-plane $\{ z : \operatorname{Im} z > 0 \}$.
```

**In Lean.** `RMTFoundations.Stieltjes.analyticOn_stieltjes` in [Challenge/Reference/Stieltjes/HalfPlane.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Stieltjes/HalfPlane.lean#L86): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem analyticOn_stieltjes (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] :
    AnalyticOn ℂ (stieltjes μ) {w : ℂ | 0 < w.im}
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### For aspect ratio 0 &lt; y &lt; 1, the explicitly constructed MP measure is a probability law

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For $0 < y < 1$, the Marchenko--Pastur measure $\mu_y$ constructed in the library is a probability
measure.
```

**In Lean.** `RMTFoundations.MarchenkoPastur.mpMeasure_prob` in [Challenge/Reference/Measure/MarchenkoPastur.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Measure/MarchenkoPastur.lean#L535): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem mpMeasure_prob (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : IsProbabilityMeasure (mpMeasure y)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The MP law equals volume weighted by its explicit density for 0 &lt; y &lt; 1

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For $0 < y < 1$, the Marchenko--Pastur measure $\mu_y$ has the density
\[ \frac{\sqrt{(b - x)(x - a)}}{2\pi y x} \quad \text{on } [a, b], \qquad 0 \text{ elsewhere}, \]
with respect to Lebesgue measure, where $a = (1 - \sqrt{y})^2$ and $b = (1 + \sqrt{y})^2$.
```

**In Lean.** `RMTFoundations.MarchenkoPastur.mpMeasure_density` in [Challenge/Reference/Measure/MarchenkoPastur.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Measure/MarchenkoPastur.lean#L526): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem mpMeasure_density (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) : mpMeasure y = volume.withDensity (fun x => ENNReal.ofReal (mpDensity y x))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The genuine MP Stieltjes transform solves its covariance quadratic in the upper half-plane

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For $0 < y < 1$ and $\operatorname{Im} z > 0$, the Stieltjes transform $m(z) = S_{\mu_y}(z)$ of the
Marchenko--Pastur measure satisfies
\[ y z\, m(z)^2 + (z + y - 1)\, m(z) + 1 = 0. \]
```

**In Lean.** `RMTFoundations.MarchenkoPastur.mpMeasure_transform_quadratic` in [Challenge/Reference/Measure/MarchenkoPastur.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Measure/MarchenkoPastur.lean#L632): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem mpMeasure_transform_quadratic (y : ℝ 
     /- [definition] -/ ) (hy : 0 < y 
     /- [standing] -/ ) (hlt : y < 1 
     /- [standing] -/ ) (z : ℂ 
     /- [definition] -/ ) (hz : 0 < z.im 
     /- [standing] -/ ) : (y : ℂ)*z*(stieltjes (mpMeasure y) z)^2+
      (z+y-1)*stieltjes (mpMeasure y) z+1 = 0
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Analytic subordination for compactly supported probability measures with explicit support hypotheses

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $\mu_1, \mu_2$ be probability measures on $\mathbb{R}$ supported in $[-R, R]$ for some $R > 0$, and
$\operatorname{Im} z > 0$. The library's subordination functions $\omega_1, \omega_2$ satisfy
$\operatorname{Im} \omega_j(z) \ge \operatorname{Im} z$ for $j = 1, 2$ and
\[ -\frac{1}{S_{\mu_1}(\omega_1(z))} = -\frac{1}{S_{\mu_2}(\omega_2(z))} = \omega_1(z) + \omega_2(z) - z. \]
```

**In Lean.** `RMTFoundations.FreeConvolution.subordination` in [Challenge/Reference/Measure/FreeConvolution.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Measure/FreeConvolution.lean#L1200): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem subordination (h1 : SupportedIn μ1 R /- [standing] -/ ) (h2 : SupportedIn μ2 R /- [standing] -/ ) (hR : 0 < R /- [standing] -/ ) {z : ℂ /- [definition] -/ }
    (hz : 0 < z.im /- [standing] -/ ) :
    z.im ≤ (omega1 μ1 μ2 z).im ∧ z.im ≤ (omega2 μ1 μ2 z).im
      ∧ -(stieltjes μ1 (omega1 μ1 μ2 z))⁻¹ = omega1 μ1 μ2 z + omega2 μ1 μ2 z - z
      ∧ -(stieltjes μ2 (omega2 μ1 μ2 z))⁻¹ = omega1 μ1 μ2 z + omega2 μ1 μ2 z - z
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### Finite Herglotz-Borel representation under upper-half-plane holomorphy, positivity and an inverse-height bound

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $F$ be holomorphic on the upper half-plane, with $\operatorname{Im} F(z) \ge 0$ and
$|F(z)| \le M / \operatorname{Im} z$ there. Then there is a finite measure $\mu$ on $\mathbb{R}$ of total
mass at most $M$ such that $F(z) = S_\mu(z)$ for every $z$ in the upper half-plane.
```

**In Lean.** `RMTFoundations.HerglotzBorelProof.herglotzBorel` in [Challenge/Reference/Measure/HerglotzBorel.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Measure/HerglotzBorel.lean#L516): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem herglotzBorel : RMTFoundations.AnalyticHalfPlane.HerglotzBorel
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### The interval Stieltjes inversion limit includes the exact half-endpoint atom terms

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
For a finite measure $\nu$ on $\mathbb{R}$ and real $a < b$,
\[ \lim_{\eta \downarrow 0} \int_a^b \operatorname{Im} S_\nu(x + i\eta)\,dx
   = \pi \Big( \nu\big((a,b)\big) + \tfrac12\, \nu(\{a\}) + \tfrac12\, \nu(\{b\}) \Big). \]
```

**In Lean.** `RMTFoundations.StieltjesInversion.tendsto_interval_im` in [Challenge/Reference/Measure/StieltjesInversion.lean](https://github.com/chenle02/rmt-foundations-lean/blob/df8d037ff7db61ec172188bf20d85e7078199c70/Challenge/Reference/Measure/StieltjesInversion.lean#L190): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem tendsto_interval_im (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] (a b : ℝ /- [definition] -/ ) (hab : a < b /- [standing] -/ ) :
    Tendsto (fun η : ℝ => ∫ x in a..b, (stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im)
      (𝓝[>] 0) (𝓝 (π * (ν.real (Ioo a b) + ν.real {a} / 2 + ν.real {b} / 2)))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

## What the checks establish

- **Every proof is checked by Lean.** The package builds; no `sorry` (an unfinished proof) remains; the only axioms used are `Classical.choice`, `Quot.sound`, `propext` (allowed: `propext`, `Quot.sound`, `Classical.choice`).
- **The statements shown are the ones proved.** For 16 statement(s), a second checker (comparator) confirmed that the proof proves exactly the statement shown, with only the permitted axioms, and independent Lean kernels replayed the proof.
- **Not checked by any tool:** that a title or note describes its Lean statement. A definition listed under *Definitions checked by a person* is compared by name and type only.

The full account of what each check covers and what it takes on trust is lean-pkg's [trust model](https://github.com/lean-pkg/lean-pkg/blob/main/docs/trust-model.md).

## How this was checked

- lean-pkg's claims ledger: **ready**, every required claim is closed by the recorded receipts; 66 of 66 required claim(s) verified (`sha256:0623031714fb83ce…`).
- Build check (`lean-pkg gate`) at commit `df8d037ff7db`: `sorry` count 0; axioms used: `Classical.choice`, `Quot.sound`, `propext`; run in a container (Singularity), SIF SHA-256 `0639ce71c13d479d456499b53f1efd887055123fe67573873170b7d1d9bba36a`.
- Axioms of every claim: read from the built environment (Lean's `collectAxioms`) for all 384 claim(s) in `claims.yaml`, not only the theorems the build prints; none uses an axiom beyond `propext`, `Quot.sound` and `Classical.choice`.
- Statement comparison (comparator) at commit `df8d037ff7db`: 1 configuration(s), 16 theorem(s) compared (each Challenge statement against its Solution proof); permitted axioms: `Classical.choice`, `Quot.sound`, `propext`; definitions compared by name only: none.
- Built on lean-pkg stack [lts-2026.10](https://github.com/lean-pkg/lean-pkg/blob/main/docs/stacks/lts-2026.10.md) (Lean `v4.35.0`, Mathlib `v4.35.0`), supported until 2028-04-30.

### Receipts

| Receipt | Check | Commit | Date | Job | SHA-256 |
|---|---|---|---|---|---|
| `.lean-receipts/8edff84bb8b0-5581013.json` | build | `8edff84bb8b0` | 2026-10-17 | — | `56c95df82c4d5fb39d84a8a1c1b1cc526049a8733f872c94bf1b1330d236f066` |
| `.lean-receipts/8edff84bb8b0-comparator.json` | statement comparison | `8edff84bb8b0` | 2026-10-17 | — | `901709b417ac6c2edf00000a88645ec90b3d7377075f95f02fb94be7b83ea459` |
| `.lean-receipts/8edff84bb8b0-slurm-5582463.json` | build | `8edff84bb8b0` | 2026-10-17 | slurm-5582463 | `4a582767900357f534b12f851e0a3fcbb38432ada76eb2f1b8a19c65efd28036` |
| `.lean-receipts/df8d037ff7db-comparator.json` (used here) | statement comparison | `df8d037ff7db` | 2026-10-21 | — | `d434eaaa24572bbc1ec0f762fa30313c2d84697c0e7d22766094c9b01122f209` |
| `.lean-receipts/df8d037ff7db-slurm-5588758.json` (used here) | build | `df8d037ff7db` | 2026-10-20 | slurm-5588758 | `fee03ee58ec07b574e9b30e4af136576f1681909fa45c1ae6924c955570ae2e8` |

*(used here)*: the receipt the lean-pkg registry holds for this package, which the lines above read. SHA-256 is of the file as committed.

### Reproduce

- Lean toolchain: `leanprover/lean4:v4.35.0`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (lake-manifest.json).

```bash
git clone https://github.com/chenle02/rmt-foundations-lean
cd rmt-foundations-lean
git checkout df8d037ff7db61ec172188bf20d85e7078199c70   # the commit the build check binds
lake exe cache get
lake build
```

Expected: `#print axioms` on any declaration above reports a subset of {`Classical.choice`, `Quot.sound`, `propext`} (the union the build check records); `sorryAx` never appears.

## Citation

Le Chen. *rmt-foundations: random-matrix and analytic foundations in Lean*. Version 0.2.0. [doi:10.5281/zenodo.23539485](https://doi.org/10.5281/zenodo.23539485).

See [CITATION.cff](CITATION.cff).

## License

Released under `Apache-2.0`; see [LICENSE](LICENSE).

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html).

<!-- lean-pkg:page:end -->
