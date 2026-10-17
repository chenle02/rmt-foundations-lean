import RMTFoundations.Stochastic.Increments
import Mathlib.Probability.Independence.Integration

/-!
# Simple predictable processes and their stochastic integral

This file builds the first rung of the Itô integral: the integral of a *simple
predictable* integrand against a process, together with its linearity and the
Itô isometry on simple integrands.

A simple predictable integrand is the data of a monotone sequence of times
`τ : ℕ → ι` and a sequence `H : ℕ → Ω → ℝ` with `H i` measurable for the
σ-algebra `ℱ (τ i)` of the past at time `τ i` and uniformly bounded.  The
process it represents is `∑ i, H i · 1_{Ioc (τ i) (τ (i+1))}`; we do not need
that representation, only the finite sums it produces, so it is not formed.

`simpleIntegral H M τ n` is `∑_{i < n} H i · (M (τ (i+1)) - M (τ i))`.

## What is proved

* `simpleIntegral_add`, `simpleIntegral_smul`, `simpleIntegral_add_integrator`:
  the integral is linear in the integrand and additive in the integrator.  These
  are algebraic identities and hold with no hypothesis whatsoever.
* `stronglyMeasurable_simpleIntegral`: the integral up to step `n` is measurable
  for `ℱ (τ n)`, i.e. the integral is an adapted process.
* `memLp_two_simpleIntegral`: it is in `L²` when the integrator is.
* `integral_sq_simpleIntegral`: **the Itô isometry on simple integrands**,
  `E[(∫ H dM)²] = ∑_{i < n} E[(H i)² (M (τ (i+1)) - M (τ i))²]`, for an `L²`
  martingale integrator `M`.  This is the exact form in which the isometry is
  true for a general `L²` martingale; the familiar `∑ E[(H i)²] (t_{i+1} - t_i)`
  is the specialisation `integral_sq_simpleIntegral_of_indep` below, which needs
  the increments to be independent of the past and to have a known variance.
* `integral_simpleIntegral_eq_zero`: the integral has mean zero.

## What is *not* proved

The `L²` limit that extends the integral off simple integrands is absent.  It
needs (a) the density of simple predictable processes in the space of
progressively measurable `H` with `E ∫ H² d⟨M⟩ < ∞`, which in turn needs the
quadratic variation `⟨M⟩`, and (b) completeness of the space of `L²` martingales,
which needs Doob's `L²` maximal inequality in continuous time.  Neither the
quadratic variation nor the continuous-time Doob inequality exists in the pinned
mathlib; see `RMTFoundations/Stochastic/Basic.lean`.
-/

namespace RMTFoundations.Stochastic

open MeasureTheory
open scoped ENNReal

variable {Ω ι : Type* /- [definition] -/ } [Preorder ι /- [definition] -/ ] {m0 : MeasurableSpace Ω /- [definition] -/ } {μ : Measure Ω /- [definition] -/ }
  {ℱ : Filtration ι m0} {M N : ι → Ω → ℝ} {τ : ℕ → ι} {H K : ℕ → Ω → ℝ}

/-- A real function in `L∞` times a function in `L²` is in `L²`. -/
theorem memLp_two_bdd_mul {f g : Ω → ℝ /- [definition] -/ } {C : ℝ /- [definition] -/ } (hf : AEStronglyMeasurable f μ /- [standing] -/ )
    (hfb : ∀ ω, ‖f ω‖ ≤ C /- [standing] -/ ) (hg : MemLp g 2 μ /- [standing] -/ ) : MemLp (fun ω => f ω * g ω) 2 μ := by
  have hftop : MemLp f ∞ μ := memLp_top_of_bound hf C (Filter.Eventually.of_forall hfb)
  simpa only [mul_comm] using hg.mul' (r := (2 : ENNReal)) hftop

/-- A **simple predictable integrand** relative to a filtration `ℱ`: a monotone
sequence of times `τ` and a uniformly bounded sequence `H` with `H i` measurable
for the past `ℱ (τ i)`. -/
structure IsSimplePredictable (ℱ : Filtration ι m0 /- [definition] -/ ) (τ : ℕ → ι /- [definition] -/ ) (H : ℕ → Ω → ℝ /- [definition] -/ ) : Prop where
  /-- the partition times increase -/
  monotone_times : Monotone τ
  /-- `H i` only uses information available at time `τ i` -/
  stronglyMeasurable : ∀ i, StronglyMeasurable[ℱ (τ i)] (H i)
  /-- the integrand is uniformly bounded -/
  isBounded : ∃ C : ℝ, ∀ i, ∀ ω, ‖H i ω‖ ≤ C

/-- The stochastic integral of a simple predictable integrand `H` against a
process `M` along the partition `τ`, truncated at step `n`:
`∑_{i < n} H i · (M (τ (i+1)) - M (τ i))`. -/
noncomputable def simpleIntegral (H : ℕ → Ω → ℝ /- [definition] -/ ) (M : ι → Ω → ℝ /- [definition] -/ ) (τ : ℕ → ι /- [definition] -/ ) (n : ℕ /- [definition] -/ )
    (ω : Ω /- [definition] -/ ) : ℝ :=
  ∑ i ∈ Finset.range n, H i ω * (M (τ (i + 1)) ω - M (τ i) ω)

omit [Preorder ι] in
theorem simpleIntegral_apply (H : ℕ → Ω → ℝ /- [definition] -/ ) (M : ι → Ω → ℝ /- [definition] -/ ) (τ : ℕ → ι /- [definition] -/ ) (n : ℕ /- [definition] -/ ) (ω : Ω /- [definition] -/ ) :
    simpleIntegral H M τ n ω
      = ∑ i ∈ Finset.range n, H i ω * (M (τ (i + 1)) ω - M (τ i) ω) := rfl

omit [Preorder ι] in
theorem simpleIntegral_zero (H : ℕ → Ω → ℝ /- [definition] -/ ) (M : ι → Ω → ℝ /- [definition] -/ ) (τ : ℕ → ι /- [definition] -/ ) (ω : Ω /- [definition] -/ ) :
    simpleIntegral H M τ 0 ω = 0 := by
  rw [simpleIntegral_apply, Finset.sum_range_zero]

omit [Preorder ι] in
theorem simpleIntegral_succ (H : ℕ → Ω → ℝ /- [definition] -/ ) (M : ι → Ω → ℝ /- [definition] -/ ) (τ : ℕ → ι /- [definition] -/ ) (n : ℕ /- [definition] -/ ) (ω : Ω /- [definition] -/ ) :
    simpleIntegral H M τ (n + 1) ω
      = simpleIntegral H M τ n ω + H n ω * (M (τ (n + 1)) ω - M (τ n) ω) := by
  rw [simpleIntegral_apply, simpleIntegral_apply, Finset.sum_range_succ]

omit [Preorder ι] in
/-- **Linearity in the integrand.** -/
theorem simpleIntegral_add (H K : ℕ → Ω → ℝ /- [definition] -/ ) (M : ι → Ω → ℝ /- [definition] -/ ) (τ : ℕ → ι /- [definition] -/ ) (n : ℕ /- [definition] -/ ) (ω : Ω /- [definition] -/ ) :
    simpleIntegral (fun i => H i + K i) M τ n ω
      = simpleIntegral H M τ n ω + simpleIntegral K M τ n ω := by
  rw [simpleIntegral_apply, simpleIntegral_apply, simpleIntegral_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, add_mul]

omit [Preorder ι] in
/-- **Homogeneity in the integrand.** -/
theorem simpleIntegral_smul (c : ℝ /- [definition] -/ ) (H : ℕ → Ω → ℝ /- [definition] -/ ) (M : ι → Ω → ℝ /- [definition] -/ ) (τ : ℕ → ι /- [definition] -/ ) (n : ℕ /- [definition] -/ )
    (ω : Ω /- [definition] -/ ) :
    simpleIntegral (fun i => c • H i) M τ n ω = c * simpleIntegral H M τ n ω := by
  rw [simpleIntegral_apply, simpleIntegral_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

omit [Preorder ι] in
/-- **Additivity in the integrator.** -/
theorem simpleIntegral_add_integrator (H : ℕ → Ω → ℝ /- [definition] -/ ) (M N : ι → Ω → ℝ /- [definition] -/ ) (τ : ℕ → ι /- [definition] -/ ) (n : ℕ /- [definition] -/ )
    (ω : Ω /- [definition] -/ ) :
    simpleIntegral H (M + N) τ n ω = simpleIntegral H M τ n ω + simpleIntegral H N τ n ω := by
  rw [simpleIntegral_apply, simpleIntegral_apply, simpleIntegral_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

/-- The simple integral truncated at `n` is measurable for the past at time `τ n`;
that is, the simple integral is an adapted process. -/
theorem stronglyMeasurable_simpleIntegral (hτ : Monotone τ /- [standing] -/ )
    (hH : ∀ i, StronglyMeasurable[ℱ (τ i)] (H i)  /- [standing] -/ )
    (hM : ∀ i, StronglyMeasurable[ℱ i] (M i)  /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    StronglyMeasurable[ℱ (τ n)] (simpleIntegral H M τ n) := by
  refine Finset.stronglyMeasurable_fun_sum _ fun i hi => ?_
  have hi' : i < n := Finset.mem_range.mp hi
  have h1 : StronglyMeasurable[ℱ (τ n)] (H i) := (hH i).mono (ℱ.mono (hτ hi'.le))
  have h2 : StronglyMeasurable[ℱ (τ n)] (M (τ (i + 1))) :=
    (hM _).mono (ℱ.mono (hτ (Nat.succ_le_of_lt hi')))
  have h3 : StronglyMeasurable[ℱ (τ n)] (M (τ i)) := (hM _).mono (ℱ.mono (hτ hi'.le))
  exact h1.mul (h2.sub h3)

/-- One term of the simple integral is in `L²`. -/
theorem memLp_two_simpleIntegral_term (hM2 : ∀ i, MemLp (M i) 2 μ /- [standing] -/ )
    (hH : IsSimplePredictable ℱ τ H /- [standing] -/ ) (i : ℕ /- [definition] -/ ) :
    MemLp (fun ω => H i ω * (M (τ (i + 1)) ω - M (τ i) ω)) 2 μ := by
  obtain ⟨C, hC⟩ := hH.isBounded
  have hmeas : AEStronglyMeasurable (H i) μ :=
    ((hH.stronglyMeasurable i).mono (ℱ.le _)).aestronglyMeasurable
  exact memLp_two_bdd_mul hmeas (hC i) ((hM2 _).sub (hM2 _))

/-- The simple integral is in `L²` when the integrator is. -/
theorem memLp_two_simpleIntegral (hM2 : ∀ i, MemLp (M i) 2 μ /- [standing] -/ )
    (hH : IsSimplePredictable ℱ τ H /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    MemLp (simpleIntegral H M τ n) 2 μ :=
  memLp_finsetSum _ fun i _ => memLp_two_simpleIntegral_term hM2 hH i

/-- The simple integral against a martingale has mean zero. -/
theorem integral_simpleIntegral_eq_zero [IsFiniteMeasure μ /- [standing] -/ ]
    (hM : Martingale M ℱ μ /- [standing] -/ ) (hM2 : ∀ i, MemLp (M i) 2 μ /- [standing] -/ )
    (hH : IsSimplePredictable ℱ τ H /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    ∫ ω, simpleIntegral H M τ n ω ∂μ = 0 := by
  induction n with
  | zero =>
    rw [integral_congr_ae
      (Filter.Eventually.of_forall (simpleIntegral_zero H M τ)), integral_zero]
  | succ n ih =>
    have hIn : MemLp (simpleIntegral H M τ n) 2 μ := memLp_two_simpleIntegral hM2 hH n
    have hTn : MemLp (fun ω => H n ω * (M (τ (n + 1)) ω - M (τ n) ω)) 2 μ :=
      memLp_two_simpleIntegral_term hM2 hH n
    have hstep : τ n ≤ τ (n + 1) := hH.monotone_times (Nat.le_succ n)
    have hcross : ∫ ω, H n ω * (M (τ (n + 1)) ω - M (τ n) ω) ∂μ = 0 :=
      integral_mul_increment_eq_zero hM hstep (hH.stronglyMeasurable n) (hTn.integrable one_le_two)
    rw [integral_congr_ae (Filter.Eventually.of_forall (simpleIntegral_succ H M τ n)),
      integral_add (hIn.integrable one_le_two) (hTn.integrable one_le_two), ih, hcross, add_zero]

/-- **Itô isometry on simple integrands.** For an `L²` martingale integrator `M`
and a simple predictable integrand `H`, the second moment of the simple integral is
the sum of the second moments of its terms: all cross terms vanish, by the
orthogonality of martingale increments. -/
theorem integral_sq_simpleIntegral [SigmaFiniteFiltration μ ℱ /- [definition] -/ ]
    (hM : Martingale M ℱ μ /- [standing] -/ ) (hM2 : ∀ i, MemLp (M i) 2 μ /- [standing] -/ )
    (hH : IsSimplePredictable ℱ τ H /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    ∫ ω, simpleIntegral H M τ n ω ^ 2 ∂μ
      = ∑ i ∈ Finset.range n, ∫ ω, (H i ω * (M (τ (i + 1)) ω - M (τ i) ω)) ^ 2 ∂μ := by
  obtain ⟨C, hC⟩ := hH.isBounded
  induction n with
  | zero =>
    have h0 : ∀ ω, simpleIntegral H M τ 0 ω ^ 2 = 0 := by
      intro ω
      rw [simpleIntegral_zero]
      exact zero_pow two_ne_zero
    rw [Finset.sum_range_zero, integral_congr_ae (Filter.Eventually.of_forall h0), integral_zero]
  | succ n ih =>
    have hIn : MemLp (simpleIntegral H M τ n) 2 μ := memLp_two_simpleIntegral hM2 hH n
    have hTn : MemLp (fun ω => H n ω * (M (τ (n + 1)) ω - M (τ n) ω)) 2 μ :=
      memLp_two_simpleIntegral_term hM2 hH n
    have hstep : τ n ≤ τ (n + 1) := hH.monotone_times (Nat.le_succ n)
    have hHmeas : AEStronglyMeasurable (H n) μ :=
      ((hH.stronglyMeasurable n).mono (ℱ.le _)).aestronglyMeasurable
    have hX2 : MemLp (fun ω => H n ω * simpleIntegral H M τ n ω) 2 μ :=
      memLp_two_bdd_mul hHmeas (hC n) hIn
    have hXmeas : StronglyMeasurable[ℱ (τ n)] fun ω => H n ω * simpleIntegral H M τ n ω :=
      (hH.stronglyMeasurable n).mul
        (stronglyMeasurable_simpleIntegral hH.monotone_times hH.stronglyMeasurable
          hM.stronglyMeasurable n)
    have hBcore : Integrable
        (fun ω => H n ω * simpleIntegral H M τ n ω * (M (τ (n + 1)) ω - M (τ n) ω)) μ :=
      integrable_mul_of_memLp_two hX2 ((hM2 _).sub (hM2 _))
    have hcross :
        ∫ ω, H n ω * simpleIntegral H M τ n ω * (M (τ (n + 1)) ω - M (τ n) ω) ∂μ = 0 :=
      integral_mul_increment_eq_zero hM hstep hXmeas hBcore
    have hA : Integrable (fun ω => simpleIntegral H M τ n ω ^ 2) μ :=
      integrable_sq_of_memLp_two hIn
    have hB : Integrable
        (fun ω => 2 * (H n ω * simpleIntegral H M τ n ω * (M (τ (n + 1)) ω - M (τ n) ω))) μ :=
      hBcore.const_mul 2
    have hCi : Integrable (fun ω => (H n ω * (M (τ (n + 1)) ω - M (τ n) ω)) ^ 2) μ :=
      integrable_sq_of_memLp_two hTn
    have hsplit : ∀ ω, simpleIntegral H M τ (n + 1) ω ^ 2
        = simpleIntegral H M τ n ω ^ 2
          + 2 * (H n ω * simpleIntegral H M τ n ω * (M (τ (n + 1)) ω - M (τ n) ω))
          + (H n ω * (M (τ (n + 1)) ω - M (τ n) ω)) ^ 2 := by
      intro ω
      rw [simpleIntegral_succ]
      ring
    have hAB : Integrable (fun ω => simpleIntegral H M τ n ω ^ 2
        + 2 * (H n ω * simpleIntegral H M τ n ω * (M (τ (n + 1)) ω - M (τ n) ω))) μ := hA.add hB
    rw [integral_congr_ae (Filter.Eventually.of_forall hsplit),
      integral_add hAB hCi, integral_add hA hB, integral_const_mul, hcross, mul_zero,
      add_zero, ih, Finset.sum_range_succ]

section IndependentIncrements

open ProbabilityTheory

/-- If two real random variables are independent, the second moment of their product
factorises. -/
theorem integral_sq_mul_of_indep {X Y : Ω → ℝ /- [definition] -/ } (hXY : IndepFun X Y μ /- [standing] -/ )
    (hX : AEMeasurable X μ /- [standing] -/ ) (hY : AEMeasurable Y μ /- [standing] -/ ) :
    ∫ ω, (X ω * Y ω) ^ 2 ∂μ = (∫ ω, X ω ^ 2 ∂μ) * ∫ ω, Y ω ^ 2 ∂μ := by
  have hsqX : AEStronglyMeasurable (fun x : ℝ => x ^ 2) (μ.map X) :=
    (continuous_pow 2).aestronglyMeasurable
  have hsqY : AEStronglyMeasurable (fun x : ℝ => x ^ 2) (μ.map Y) :=
    (continuous_pow 2).aestronglyMeasurable
  have h := hXY.integral_fun_comp_mul_comp hX hY hsqX hsqY
  have hpt : ∀ ω, (X ω * Y ω) ^ 2 = X ω ^ 2 * Y ω ^ 2 := fun ω => mul_pow _ _ 2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  exact h

/-- **Itô isometry, factorised form.** When each `H i` is independent of the increment
it multiplies -- which is what happens for the natural filtration of a process with
independent increments, and in particular for Brownian motion -- the isometry becomes
`E[(∫ H dM)²] = ∑ E[(H i)²] · E[(M (τ (i+1)) - M (τ i))²]`. -/
theorem integral_sq_simpleIntegral_of_indep [SigmaFiniteFiltration μ ℱ /- [definition] -/ ]
    (hM : Martingale M ℱ μ /- [standing] -/ ) (hM2 : ∀ i, MemLp (M i) 2 μ /- [standing] -/ )
    (hH : IsSimplePredictable ℱ τ H /- [standing] -/ )
    (hindep : ∀ i, IndepFun (H i) (fun ω => M (τ (i + 1)) ω - M (τ i) ω) μ /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    ∫ ω, simpleIntegral H M τ n ω ^ 2 ∂μ
      = ∑ i ∈ Finset.range n,
          (∫ ω, H i ω ^ 2 ∂μ) * ∫ ω, (M (τ (i + 1)) ω - M (τ i) ω) ^ 2 ∂μ := by
  rw [integral_sq_simpleIntegral hM hM2 hH n]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hX : AEMeasurable (H i) μ :=
    ((hH.stronglyMeasurable i).mono (ℱ.le _)).measurable.aemeasurable
  have hY : AEMeasurable (fun ω => M (τ (i + 1)) ω - M (τ i) ω) μ :=
    ((hM2 (τ (i + 1))).sub (hM2 (τ i))).aestronglyMeasurable.aemeasurable
  exact integral_sq_mul_of_indep (hindep i) hX hY

/-- **Itô isometry against a clock.**  If in addition the increment of `M` over
`[τ i, τ (i+1)]` has second moment `v (i+1) - v i` -- for Brownian motion, `v = id`
and this is `τ (i+1) - τ i` -- then the isometry takes the familiar form
`E[(∫ H dM)²] = ∑ E[(H i)²] · (v (i+1) - v i)`. -/
theorem integral_sq_simpleIntegral_of_indep_clock [SigmaFiniteFiltration μ ℱ /- [definition] -/ ]
    (hM : Martingale M ℱ μ /- [standing] -/ ) (hM2 : ∀ i, MemLp (M i) 2 μ /- [standing] -/ )
    (hH : IsSimplePredictable ℱ τ H /- [standing] -/ )
    (hindep : ∀ i, IndepFun (H i) (fun ω => M (τ (i + 1)) ω - M (τ i) ω) μ /- [standing] -/ )
    (v : ℕ → ℝ /- [definition] -/ ) (hv : ∀ i, ∫ ω, (M (τ (i + 1)) ω - M (τ i) ω) ^ 2 ∂μ = v (i + 1) - v i /- [standing] -/ )
    (n : ℕ /- [definition] -/ ) :
    ∫ ω, simpleIntegral H M τ n ω ^ 2 ∂μ
      = ∑ i ∈ Finset.range n, (∫ ω, H i ω ^ 2 ∂μ) * (v (i + 1) - v i) := by
  rw [integral_sq_simpleIntegral_of_indep hM hM2 hH hindep n]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hv i]

end IndependentIncrements

section MartingaleTransform

/-- **The discrete-time martingale transform and its isometry.**  This is the special
case `ι = ℕ`, `τ = id` of `integral_sq_simpleIntegral`, written out so that the
discrete statement is visible without unfolding: if `H i` is `𝒢 i`-measurable and
uniformly bounded and `M` is an `L²` martingale, then the transform
`∑_{i < n} H i (M (i+1) - M i)` has second moment `∑_{i < n} E[(H i)² (M (i+1) - M i)²]`. -/
theorem integral_sq_martingaleTransform {𝒢 : Filtration ℕ m0 /- [definition] -/ } [SigmaFiniteFiltration μ 𝒢 /- [definition] -/ ]
    {M : ℕ → Ω → ℝ /- [definition] -/ } {H : ℕ → Ω → ℝ /- [definition] -/ } (hM : Martingale M 𝒢 μ /- [standing] -/ ) (hM2 : ∀ i, MemLp (M i) 2 μ /- [standing] -/ )
    (hHmeas : ∀ i, StronglyMeasurable[𝒢 i] (H i)  /- [standing] -/ ) (C : ℝ /- [definition] -/ ) (hHbdd : ∀ i, ∀ ω, ‖H i ω‖ ≤ C /- [standing] -/ )
    (n : ℕ /- [definition] -/ ) :
    ∫ ω, (∑ i ∈ Finset.range n, H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ
      = ∑ i ∈ Finset.range n, ∫ ω, (H i ω * (M (i + 1) ω - M i ω)) ^ 2 ∂μ :=
  integral_sq_simpleIntegral hM hM2 ⟨monotone_id, hHmeas, ⟨C, hHbdd⟩⟩ n

end MartingaleTransform

end RMTFoundations.Stochastic

#print axioms RMTFoundations.Stochastic.memLp_two_bdd_mul
#print axioms RMTFoundations.Stochastic.IsSimplePredictable
#print axioms RMTFoundations.Stochastic.simpleIntegral
#print axioms RMTFoundations.Stochastic.simpleIntegral_apply
#print axioms RMTFoundations.Stochastic.simpleIntegral_zero
#print axioms RMTFoundations.Stochastic.simpleIntegral_succ
#print axioms RMTFoundations.Stochastic.simpleIntegral_add
#print axioms RMTFoundations.Stochastic.simpleIntegral_smul
#print axioms RMTFoundations.Stochastic.simpleIntegral_add_integrator
#print axioms RMTFoundations.Stochastic.stronglyMeasurable_simpleIntegral
#print axioms RMTFoundations.Stochastic.memLp_two_simpleIntegral_term
#print axioms RMTFoundations.Stochastic.memLp_two_simpleIntegral
#print axioms RMTFoundations.Stochastic.integral_simpleIntegral_eq_zero
#print axioms RMTFoundations.Stochastic.integral_sq_simpleIntegral
#print axioms RMTFoundations.Stochastic.integral_sq_mul_of_indep
#print axioms RMTFoundations.Stochastic.integral_sq_simpleIntegral_of_indep
#print axioms RMTFoundations.Stochastic.integral_sq_simpleIntegral_of_indep_clock
#print axioms RMTFoundations.Stochastic.integral_sq_martingaleTransform
