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

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).

This work was completed in part with resources provided by the [Auburn University Easley Cluster](https://hpc.auburn.edu/hpc/docs/hpcdocs/build/html/easley/intro.html). Full verification gates ran as Slurm jobs on Easley.

## License and citation

[Apache-2.0](LICENSE). See [NOTICE](NOTICE) for third-party attributions and
the bundled [compact-spectral](compact-spectral-LICENSE) and
[Tau Ceti](TauCeti-LICENSE) licenses.

Please cite *rmt-foundations*, version 0.1.0, by Le Chen, and record the
source commit you used. Metadata is in [CITATION.cff](CITATION.cff). See also
the [citation page](https://chenle02.github.io/rmt-foundations-lean/citation.html).
