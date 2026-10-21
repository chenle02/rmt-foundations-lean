---
layout: landing
title: Tracy–Widom foundations
permalink: /tracy-widom.html
---

# Tracy–Widom foundations

The public API is `RMTFoundations.TracyWidom`. It packages the canonical Airy
Fredholm functions and their probability measures. The analytic theorems have
no matrix-model, regular-edge, moment, or probabilistic-event hypotheses.
The underlying proofs remain in the existing Airy and operator modules.

## Imports and objects

| Import | Provides |
| --- | --- |
| `RMTFoundations.TracyWidom.Functions` | functions, continuity, Fredholm formulas |
| `RMTFoundations.TracyWidom.Distribution` | monotonicity, limits, bounds, GOE derivative |
| `RMTFoundations.TracyWidom.Probability` | CDF measures, uniqueness, quantiles and medians |
| `RMTFoundations.TracyWidom.Painleve` | canonical response, ODE, Airy normalization, integral formulas |
| `RMTFoundations.TracyWidom.HastingsMcLeod` | unique real global classical Airy-normalized PII solution, equal to the Fredholm response |
| `RMTFoundations.TracyWidom.Regularity` | C¹ CDFs, positive continuous densities, strict monotonicity, unique quantiles, factorization (smoothness: see `Smoothness`) |
| `RMTFoundations.TracyWidom.TailBounds` | quantitative right bounds, linear left bounds, trace-interface counterinstance; sharp cubic left-tail asymptotics remain open |
| `RMTFoundations.TracyWidom.Measures` | Stieltjes CDFs, probability laws, CDF agreement |

| Name | Type | Meaning |
| --- | --- | --- |
| `TW1`, `TW2` | `ℝ → ℂ` | complex Fredholm values at coupling −1 |
| `TW1R`, `TW2R` | `ℝ → ℝ` | real CDFs; `TW1R_coe` and `TW2R_coe` recover the complex values |
| `TW1Stieltjes`, `TW2Stieltjes` | `StieltjesFunction ℝ` | the same functions with monotonicity and right continuity |
| `TW1Measure`, `TW2Measure` | `Measure ℝ` | measures with registered `IsProbabilityMeasure` instances |
| `TW1Law`, `TW2Law` | `ProbabilityMeasure ℝ` | bundled versions of exactly those measures |

The complex and real names describe the same two laws, not four distinct
probability measures. No choice of an arbitrary CDF enters the construction.

## Normalization and Fredholm domains

Write Ai for the canonically normalized real Airy function and
K(u,v) = ∫₀∞ Ai(u+t) Ai(v+t) dt. The integration measure on (0,∞) is
Lebesgue measure restricted to that interval. The function identities are

* TW1(s) = det(I − Bₛ), with Bₛ(x,y) = Ai(x+y+s) on (0,∞).
* TW2(s) = det(I − Kₛ), with Kₛ(x,y) = K(x+s,y+s) on (0,∞).

Here `kernelFredholm` is the actual absolutely convergent determinant-minor
series, not an abstract determinant specified by these identities. Its
compatibility with the operator determinant is proved upstream. The public
`TW1_fredholm` and `TW2_fredholm` use these literal physical kernels.

`TW1_fredholm_halfLine` places Ai(u+v) on **(s/2,∞)**. Moving it to (s,∞)
requires Ai(u+v−s). `TW2_fredholm_halfLine` places K(u,v) on (s,∞).
This factor of two is essential when translating the GOE Hankel kernel.

These are the conventional order-one and order-two Airy normalizations.
Finite-N ensemble scaling and identification with a particular matrix limit
must be supplied by the application.

## Headline theorems

| Property | Public declarations |
| --- | --- |
| continuity on all real cutoffs | `continuous_TW1R`, `continuous_TW2R` |
| monotonicity on all real cutoffs | `monotone_TW1R`, `monotone_TW2R` |
| left endpoint 0 | `tendsto_TW1R_atBot`, `tendsto_TW2R_atBot` |
| right endpoint 1 | `tendsto_TW1R_atTop`, `tendsto_TW2R_atTop` |
| C¹ CDFs and positive continuous densities | `contDiff_TW1R`, `contDiff_TW2R`, `TW1Density_positive`, `TW2Density_positive` |
| strict monotonicity and unique quantiles | `strictMono_TW1R`, `strictMono_TW2R`, `TW1R_quantile_exists_unique`, `TW2R_quantile_exists_unique` |
| finite-cutoff bounds | `TW1R_bounds`: 0 < TW1R(s) < 1; `TW2R_strict_bounds`: 0 < TW2R(s) < 1 |
| exponential upper bounds | `TW1R_le_exp_tail`, `TW2R_le_exp_trace` |
| GOE derivative-resolvent formula | `hasDerivAt_TW1R_canonical_resolvent` |
| measure of a lower half-line | `TW1Measure_Iic`, `TW2Measure_Iic` |
| agreement with Mathlib CDF | `cdf_TW1Measure`, `cdf_TW2Measure` |
| uniqueness and quantiles (probability interface) | `TW1Measure_unique`, `TW2Measure_unique`, `TW1R_quantile_exists`, `TW2R_quantile_exists` |
| bundled/unbundled agreement | `TW1Law_toMeasure`, `TW2Law_toMeasure` |

The integral-tail bounds use the actual Airy tail and diagonal trace.
`Regularity` strengthens the GUE finite-cutoff bounds to strict inequalities,
and exports strict monotonicity and C¹ CDFs for both laws. `TW1Density` and
`TW2Density` are the proved derivative functions of the CDFs. Both CDFs and both strictly positive densities are globally smooth; import `RMTFoundations.TracyWidom.Smoothness` for the short exports.
Every interior probability has a unique finite quantile; both medians are unique.

## Canonical Painleve response and integral representations

Import `RMTFoundations.TracyWidom.Painleve`. Its `Painleve.q` is the actual
endpoint of the inverse physical Airy-kernel response, with a continuous
representative. The kernel proves differentiability, Painleve II, and relative
Airy normalization at positive infinity. In conventional notation:

* q''(s) = s q(s) + 2 q(s)^3, and q(s)/Ai(s) tends to 1 as s tends to infinity.
* TW2R(s) = exp(- integral from s to infinity of (t-s) q(t)^2 dt).
* TW1R(s)^2 = TW2R(s) exp(- integral from s to infinity of q(t) dt).

`Painleve.integrable_tails` proves absolute integrability of q, q squared,
and the weighted square tail on every upper half-line. These formulas refer
to the same canonically defined Fredholm CDFs and the same q. The global witness
in `CanonicalPainleveWitness` jointly realizes the ODE, normalization, physical
representative and both formulas with nonzero actual sources. The
`HastingsMcLeod` module now proves uniqueness among all real global classical
Painleve II solutions with this relative Airy normalization. No uniqueness
without that normalization is claimed.

## Factorization and quantitative tails

`airy_actual_operator_factorization` supplies genuine trace-class and diagonal
basis data and proves TW2R(s) = TW1R(s) times the plus Hankel determinant.
`OrderTwoFactorization` identifies that plus determinant with the physical
Fredholm series at coupling +1. Generic determinant/spectrum support remains
available in `DetFactor`, `OperatorCore` and `Spectrum`.

Import `RMTFoundations.TracyWidom.TailBounds`; its public namespace is
`RMTFoundations.TracyWidom.Tails`. `TW_right_tail_bounds` constructs a positive
Airy-envelope constant and an explicit logarithmic threshold. Above that
threshold, the upper bounds have exponential rates -2 s^(3/2)/3 for order one
(with an additional -4 s^(3/2)/3 term), and -4 s^(3/2)/3 for order two.
The same theorem includes explicit positive lower envelopes. These three-halves exponential estimates give explicit envelopes. Separately,
`RightTailLogSharp` proves logarithmic asymptotics with limiting constants
−2/3 and −4/3 after division by s^(3/2), for the first and second orders respectively.
`TW1_rightTail_isEquivalent` and `TW2_rightTail_isEquivalent` also prove the sharp polynomial prefactors for the physical right tails.

`TW2R_left_tail_linear` applies for s <= 0 and bounds the CDF by
exp(-originMass |s|). `TW1R_left_tail_linear` applies for s <= -1 and bounds it
by exp(-signedTraceFloor-originMass |s|/8); both constants are actual Airy-data
constants retained from `LeftTail`. Sharp cubic left tails remain outside this
expansion. `trace_interface_cubic_counterinstance` explains why trace-only
estimates cannot imply that cubic rate; it does not refute the physical Airy
cubic tail. Identification of a finite matrix model with its Hermite law is a separate explicit interface.

```lean
import RMTFoundations.TracyWidom.Measures
open MeasureTheory ProbabilityTheory Set
open RMTFoundations.TracyWidom

example : Monotone TW1R := monotone_TW1R
example : IsProbabilityMeasure TW2Measure := inferInstance
example (s : ℝ /- [definition] -/) : cdf TW1Measure s = TW1R s := cdf_TW1Measure s
example (s : ℝ /- [definition] -/) : TW2Measure (Iic s) = ENNReal.ofReal (TW2R s) :=
  TW2Measure_Iic s
```


## Smoothness, moments and fourth-order candidate

Both first- and second-order CDFs and their positive densities are globally smooth. Every polynomial absolute moment is finite. The fourth-order candidate is defined using the canonical response and has proved limits, derivative and integral characterization. Its slope is strictly positive on two nonempty tails. A compact-window sign certificate remains an explicit hypothesis; global monotonicity and a fourth-order probability measure remain open.

## Airy and finite Hermite models

The Airy function has its canonical normalization and positive-half-line asymptotics. The normalized Hermite density is a genuine finite-dimensional probability law with its projection-kernel determinant formula. Hermite edge normalization, locally uniform Hermite-to-Airy convergence, uniform tail envelopes and finite stationary Dyson/OU two-time laws are proved. Spectral identification for a particular matrix ensemble remains a separate input.

## One-time Fredholm limits, probability limits, and perturbation tools

`HermiteHankelConvergence` proves L2 convergence of both actual neighboring
Hermite Hankel kernels on the full positive quadrant. `SoftEdgeTraceProducts`
gives a reusable Hilbert-Schmidt-to-trace-norm product estimate. Both ordered
products of the actual neighboring Hankel operators converge in trace norm
to the Airy kernel operator at every real cut.
`HermiteKernelIntegral` gives the true adjacent-mode convolution identity;
`HermiteFredholmLimit` supplies a common exponential kernel envelope and
proves convergence of the one-time Fredholm determinants for every complex
coupling. At physical coupling the real limit is `TW2R` at every real cut.
These are analytic determinant limits. Identification of a finite matrix
spectral pushforward with the normalized Hermite-density law remains separate.

`Airy2LimitLaws.finite_law_limit_with_weak` is a general finite-dimensional
probability theorem: joint pointwise CDF convergence, continuity, and scalar
coordinate limits with zero/one endpoints produce a unique probability law
and convergence of the full sequence. Tightness and nonnegative rectangular
increments are derived. `Airy2LimitPhysical` applies this API to the full
complex extended Airy determinant, with actual TW2 marginal measures, while
retaining finite joint-limit and coordinate-limit producers as explicit
hypotheses. `Airy2LimitEscape` exhibits escaping mass. `Airy2OneTimeGap`
shows that equal-time blocks do not supply the missing distinct-time limit.
Neither counterinstance refutes existence of the intended Airy2 process.

`WeightedVolterraFoundation` and `WeightedVolterraUniqueness` give size,
deviation and uniqueness estimates with every smallness, boundedness, support
and integrability input explicit. `ODEVolterraFoundation` converts the
normalized perturbed ODE to its Volterra equation under the stated boundary
and integration assumptions. `AiryGreenKernelFoundation` derives the actual
positive Airy kernel bound; `AiryPerturbationComparison` applies it with a
small integrable perturbation budget. Nondegenerate examples satisfy the
interfaces. `HermitePerturbationObstruction` proves that the true Hermite
coefficient error has neither a finite half-line supremum nor an integrable
envelope for any positive dimension. It kills this global ODE adapter route;
it does not affect the contour proof of Hermite-to-Airy convergence.

The actual TW4 candidate has positive derivative and strict monotonicity on
two genuine nonempty tails, in both Airy and conventional scaling.
`TW4GridCertificate` and `TW4ResponseGrid` provide a conditional compact-window
certificate with explicit margin, coverage and derivative bounds. The caller
must prove that certificate; an existential small-window example is not a
certificate for the intervening global interval. Global TW4 monotonicity and
a TW4 probability measure therefore remain open. Sharp cubic left tails and
the distinct-time finite-ensemble producer for an Airy2 process also remain
open.
