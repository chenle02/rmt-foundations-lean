<div align="center">

<img src="docs/assets/mark.svg" width="88" height="88" alt="rmt-foundations mark: a curve over three bars">

# rmt-foundations

Tracy–Widom distributions, Airy and Painlevé II theory, finite GUE identities
and analytic random-matrix tools, formalized in Lean 4.

[![CI](https://github.com/chenle02/rmt-foundations-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/chenle02/rmt-foundations-lean/actions/workflows/ci.yml)
[![Docs](https://img.shields.io/badge/docs-GitHub%20Pages-153e63)](https://chenle02.github.io/rmt-foundations-lean/)
[![Version](https://img.shields.io/badge/version-0.1.0-153e63)](CITATION.cff)
[![Lean](https://img.shields.io/badge/Lean-v4.35.0--rc2-153e63)](lean-toolchain)
[![License](https://img.shields.io/badge/license-Apache--2.0-153e63)](LICENSE)

</div>

## What version 0.1.0 proves

Every item below is a Lean declaration checked by the kernel. The hypotheses
of each declaration are part of the claim.

- **TW1 and TW2 (GOE and GUE).** The distribution functions, defined as
  Fredholm determinants of Airy kernels, are continuously differentiable and
  strictly increasing, with limits 0 and 1. Each is the distribution function
  of a unique probability measure, with a continuous positive density, unique
  quantiles, an exponential moment and all absolute moments. Both have sharp
  right-tail asymptotics, left-tail bounds of linear exponential order, and
  the Painlevé II integral representations of $F_2$ and $F_1^2$.
- **Hastings–McLeod.** Painlevé II has exactly one real global solution with
  relative Airy normalization at $+\infty$, and it equals the Fredholm
  response.
- **TW4 (GSE).** The determinant-average function is positive and $C^1$, has
  limits 0 and 1, attains every level in $(0,1)$, and has a closed formula in
  terms of TW2 and the Painlevé II solution.
- **Airy2.** The extended Airy kernel, its integral realization, and the
  reduction of the one-time expression to TW2.
- **Finite GUE.** Hermite Christoffel–Darboux identities, the normalized
  determinantal eigenvalue density with its projection kernel, and the GUE
  matrix model with the distribution function of its largest eigenvalue.
- **Analytic tools.** The Airy function and its asymptotics, Fredholm series,
  Stieltjes transforms (analyticity, inversion, Herglotz–Borel
  representation), the Marchenko–Pastur law, semicircle moments, free
  convolution subordination, Bernstein and Chernoff bounds, the
  moment–cumulant recursion, resolvent identities, and simple stochastic
  integrals against Brownian motion.

> [!IMPORTANT]
> **Not established in this release.**
> - **TW4:** monotonicity, and hence a TW4 probability measure. On this point
>   the library proves only that monotonicity is equivalent to a resolvent
>   sign condition.
> - **GUE edge limit:** the identification of the GUE edge limit with TW2
>   assumes the convergence hypothesis `GUELimit TW2R`. That convergence is
>   not proved. The finite-$N$ density is not proved to be the eigenvalue law
>   of the matrix model.
> - **Multi-time Airy2:** the multi-time Fredholm expression is a formal
>   candidate. Its convergence, operator realization and probability
>   properties are not established.
> - **Left tails:** sharp cubic left-tail asymptotics are not established.
> - **Densities:** $C^1$ regularity of the TW1 and TW2 densities is not
>   established.
>
> General local laws, universality and general Itô integration are outside
> the scope of this library.

The [status page](https://chenle02.github.io/rmt-foundations-lean/status.html)
names the declaration behind each item.

## Quick start

Install [elan](https://github.com/leanprover/elan). The toolchain is the
release candidate **Lean v4.35.0-rc2**, pinned in `lean-toolchain`. Mathlib is
pinned in `lake-manifest.json`.

```sh
git clone https://github.com/chenle02/rmt-foundations-lean.git
cd rmt-foundations-lean
lake exe cache get
lake build
```

[`examples/Quickstart.lean`](examples/Quickstart.lean) is a small consumer.

## Use as a Lake dependency

Use the same `lean-toolchain` in your project and add to `lakefile.toml`:

```toml
[[require]]
name = "RMTFoundations"
git = "https://github.com/chenle02/rmt-foundations-lean.git"
rev = "v0.1.0"
```

Then run `lake update RMTFoundations`, `lake exe cache get` and `lake build`,
and write `import RMTFoundations`. The
[dependency guide](https://chenle02.github.io/rmt-foundations-lean/dependency.html)
covers narrower imports and version pinning.

## Where to go next

| If you want to | Start here |
|---|---|
| Use the library | [Getting started](https://chenle02.github.io/rmt-foundations-lean/getting-started.html) · [examples/](examples/) |
| Find a theorem | [Module map](https://chenle02.github.io/rmt-foundations-lean/modules.html) · [Declaration index](https://chenle02.github.io/rmt-foundations-lean/declarations.html) · [claims.yaml](claims.yaml) |
| Check the evidence | [Trust and reproducibility](https://chenle02.github.io/rmt-foundations-lean/trust.html) · [formalization.yaml](formalization.yaml) · [EXPECTED-AXIOMS.txt](EXPECTED-AXIOMS.txt) |
| Contribute or use an agent | [CONTRIBUTING.md](CONTRIBUTING.md) · [AGENTS.md](AGENTS.md) · [llms.txt](llms.txt) |

## Trust and reproducibility

Proofs use only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`. There is no `sorry`, `admit`, custom axiom or `native_decide`.

```sh
bash scripts/verify.sh
```

This script checks the source policy, builds every module, test and example
from a clean project build, compares the `#print axioms` output with
`EXPECTED-AXIOMS.txt`, and replays each compiled module through
`leanchecker`. It needs the pinned toolchain and Python 3. A kernel check
confirms a proof; it does not remove any hypothesis from the statement.

## Documentation

GitHub Pages publishes the guided site from branch `main`, folder `/docs`,
with its built-in Jekyll build. The pinned package in
[`docbuild/`](docbuild/README.md) builds the full API reference locally:

```sh
lake exe cache get
cd docbuild
lake -R -Kenv=dev build RMTFoundations:docs
python3 -m http.server --directory .lake/build/doc 8000
```

## Author

**Le Chen**, Associate Professor, Department of Mathematics and Statistics,
Auburn University.

## AI disclosure

Development used OpenAI Codex (gpt-6.1-sol) workers, with Anthropic Claude for
orchestration and independent audits. Every result is kernel-checked and
depends only on `propext`, `Classical.choice` and `Quot.sound`. Hypotheses and
limitations are stated explicitly in the theorem statements.

## Acknowledgments

Haoran Li — co-author of the research paper that motivated this library and proposer of the problem.

## License and citation

[Apache-2.0](LICENSE). See [NOTICE](NOTICE) for third-party attributions and
the bundled [compact-spectral](compact-spectral-LICENSE) and
[Tau Ceti](TauCeti-LICENSE) licenses.

Please cite *rmt-foundations*, version 0.1.0, by Le Chen, and record the
source commit you used. Metadata is in [CITATION.cff](CITATION.cff). See also
the [citation page](https://chenle02.github.io/rmt-foundations-lean/citation.html).

<!-- lean-pkg:page:begin -->
<!-- Generated by `lean-pkg page rmt-foundations` from coverage.yaml, claims.yaml, the claims ledger and the receipts committed under .lean-receipts/. Do not edit between the markers: change the data and run `lean-pkg page rmt-foundations --write`. -->

## Verification status

Kernel-checked foundations for random matrix theory (Airy function and kernel, Fredholm series, order-one Tracy-Widom monotonicity, moment-cumulant recursion, resolvent identity, Marchenko-Pastur law, Stieltjes transform and inversion, Herglotz-Borel representation, free-convolution subordination); 16 main results compared.

- Library: each row below is a main result of the library, stated by its Lean declarations.
- Main results: 16; 16 of 16 main result(s) verified.
- Claims ledger (promote stage): **ready**, every required claim is closed by the recorded receipts; 66 of 66 required claim(s) verified (`sha256:7d6032bb246b6275…`).

## Main results

| Result | Lean declarations | Ledger | Notes |
|---|---|---|---|
| The actual real Airy function satisfies its second-order ODE | `RMTFoundations.Airy.iteratedDeriv_two_airyAiReal` | verified | — |
| The genuine shifted Airy kernel operator is trace class | `RMTFoundations.Airy.isTraceClass_airyKernelShift` | verified | — |
| Factorially bounded coefficients give an entire Fredholm power series | `RMTFoundations.Fredholm.fredholmSeries_entire` | verified | — |
| The canonical real order-one Airy kernel series is monotone | `RMTFoundations.TWOneMonotone.monotone_TW1R` | verified | — |
| Analytic moment-cumulant recursion at zero on the interior of the exponential integrability set | `RMTFoundations.Cumulants.moment_succ_eq_sum_cumulant_mul_moment` | verified | — |
| First resolvent identity for two invertible shifts of an arbitrary finite complex matrix | `RMTFoundations.Resolvent.resolvent_identity` | verified | — |
| Signed real-parameter complex-valued Taylor integral remainder | `RMTFoundations.Taylor.remainder_eq_interval_integral` | verified | — |
| Scalar binomial repeated-edge walk-count majorant; does not count walks itself | `RMTFoundations.WalkMajorant.walk_count_majorant` | verified | — |
| Any two Airy ODE solutions with identical first-order initial data agree | `RMTFoundations.Airy.airySolution_unique` | verified | — |
| The finite-measure Stieltjes transform is analytic on the upper half-plane | `RMTFoundations.Stieltjes.analyticOn_stieltjes` | verified | — |
| For aspect ratio 0 &lt; y &lt; 1, the explicitly constructed MP measure is a probability law | `RMTFoundations.MarchenkoPastur.mpMeasure_prob` | verified | — |
| The MP law equals volume weighted by its explicit density for 0 &lt; y &lt; 1 | `RMTFoundations.MarchenkoPastur.mpMeasure_density` | verified | — |
| The genuine MP Stieltjes transform solves its covariance quadratic in the upper half-plane | `RMTFoundations.MarchenkoPastur.mpMeasure_transform_quadratic` | verified | — |
| Analytic subordination for compactly supported probability measures with explicit support hypotheses | `RMTFoundations.FreeConvolution.subordination` | verified | — |
| Finite Herglotz-Borel representation under upper-half-plane holomorphy, positivity and an inverse-height bound | `RMTFoundations.HerglotzBorelProof.herglotzBorel` | verified | — |
| The interval Stieltjes inversion limit includes the exact half-endpoint atom terms | `RMTFoundations.StieltjesInversion.tendsto_interval_im` | verified | — |

*verified*: `lean-pkg claims ledger` closes every claim of the row at the promote stage (gate and comparator receipts); any other word is the ledger's status.

## Trust boundary

- Lower-tier gate receipt at `8edff84bb8b0` records: `sorry` count 0 after the build; axioms used: `Classical.choice`, `Quot.sound`, `propext`; allowed: `propext`, `Quot.sound`, `Classical.choice`.
- Comparator receipt at `8edff84bb8b0`: 1 configuration(s), 16 theorem(s) compared (Challenge statement against Solution proof); permitted axioms: `Classical.choice`, `Quot.sound`, `propext`; definition holes: none.

What these checks do not establish: the gate checks the build, the `sorry` count and the axioms at one commit; the comparator checks that the Solution proves exactly the Challenge statement using only the permitted axioms, and that the kernel accepts it. Neither checks that a Lean statement says what its title above says: the titles and notes are written by the authors, and the Lean statement is the result. Definition holes (`definition_names`) are compared by name only and need a human reviewer.

## Reproduce

- Lean toolchain: `leanprover/lean4:v4.35.0-rc2`.
- Mathlib: `8ab8a31c6565f9f71fe6c5ed91babd559e8deae4` (lake-manifest.json).

```bash
git clone <repository URL>
cd <checkout>
git checkout 8edff84bb8b00441bf8b860b96547122103c0279   # the commit the gate receipt binds
lake exe cache get
lake build
```

Expected: `#print axioms` on any declaration of the map reports a subset of {`Classical.choice`, `Quot.sound`, `propext`} (the union the gate receipt records); `sorryAx` never appears.

## Evidence

| Receipt | Tier | Commit | Date | Job | SHA-256 |
|---|---|---|---|---|---|
| `.lean-receipts/8edff84bb8b0-5581013.json` | lower tier | `8edff84bb8b0` | 2026-10-17 | — | `56c95df82c4d5fb39d84a8a1c1b1cc526049a8733f872c94bf1b1330d236f066` |
| `.lean-receipts/8edff84bb8b0-comparator.json` (recorded) | comparator | `8edff84bb8b0` | 2026-10-17 | — | `901709b417ac6c2edf00000a88645ec90b3d7377075f95f02fb94be7b83ea459` |
| `.lean-receipts/8edff84bb8b0-slurm-5582463.json` (recorded) | lower tier | `8edff84bb8b0` | 2026-10-17 | slurm-5582463 | `4a582767900357f534b12f851e0a3fcbb38432ada76eb2f1b8a19c65efd28036` |

*(recorded)*: the receipt the lean-pkg registry holds for this package. SHA-256 is of the file as committed.

## Citation

Le Chen. *rmt-foundations: random-matrix and analytic foundations in Lean*. Version 0.1.0.

See [CITATION.cff](CITATION.cff).

## License

Released under `Apache-2.0`; see [LICENSE](LICENSE).

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).
This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html).

<!-- lean-pkg:page:end -->
