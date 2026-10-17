import RMTFoundations.Stochastic.BrownianIncrements
import RMTFoundations.Stochastic.Independence
import RMTFoundations.Stochastic.SimpleIntegral
import Mathlib.Probability.Process.Adapted

/-

# Brownian motion is a martingale, and the Itô isometry for Brownian motion

## Independence of increments and the past

`ProbabilityTheory.IsPreBrownianReal.indepFun_shift` gives independence of the *shifted
process* `fun ω s => B (t₀ + s) ω - B t₀ ω` from the *restricted path*
`fun ω (s : Set.Iic t₀) => B s ω`.  To feed `martingale_of_indep_increments` one needs
independence of a *single increment* `B t - B t₀` from the *whole past σ-algebra*
`MeasureTheory.Filtration.natural B hB' t₀`.  Two comparisons close the gap, and it is
the restricted-path sigma-algebra and measurability of the increment:

* Past side.  `MeasureTheory.Filtration.natural_eq_comap` is already in the pinned
  mathlib and states the comparison as an *equality*,
  `natural u hum i = .comap (fun ω (j : Set.Iic i) ↦ u j ω) inferInstance`, in exactly the
  shape `indepFun_shift` produces.  Nothing had to be proved; the statement is recorded
  here as `natural_eq_comap_pathIic` only so that the shape is visible at the call site.
* Increment side.  This one is not in mathlib: `comap_increment_le_comap_shift`, that
  `B t - B t₀` is measurable for the shifted process when `t₀ ≤ t`.  It is the
  composition of the shifted process with evaluation at `t - t₀`, and it is where the
  truncated subtraction of `ℝ≥0` has to be handled (`add_tsub_cancel_of_le`).

## What is proved

* `natural_eq_comap_pathIic`: the past σ-algebra as the σ-algebra of the restricted path.
* `comap_increment_le_comap_shift`: `σ(B t - B t₀) ≤ σ(B (t₀ + ·) - B t₀)` for `t₀ ≤ t`.
* `indep_natural_increment_isPreBrownianReal`: `Indep (natural B hB' t₀) σ(B t - B t₀) P`.
* `memLp_two_isPreBrownianReal`: `MemLp (B t) 2 P`, so `B` is an `L²` process and the
  orthogonality lemmas of `Increments.lean` apply to it.
* `martingale_isPreBrownianReal` and `martingale_isBrownianReal`:
  `Martingale B (Filtration.natural B hB') P`.  Brownian motion is a martingale in
  mathlib's own sense.
* `exists_modification_martingale_isPreBrownianReal`: every pre-Brownian motion, with no
  measurability hypothesis at all, has a modification which is a martingale for its own
  natural filtration.
* `indepFun_of_indep_comap` and `indepFun_simplePredictable_increment_isPreBrownianReal`:
  a simple predictable integrand is independent of the increment it multiplies.
* `integral_sq_simpleIntegral_isPreBrownianReal`: **the Itô isometry for Brownian motion**,
  `E[(∫ H dB)²] = ∑_{i < n} E[(H i)²] · (τ (i+1) - τ i)`.
* `integral_simpleIntegral_isPreBrownianReal_eq_zero`: the simple integral has mean zero.
* `integral_sq_simpleIntegral_one_isPreBrownianReal`: the isometry at `H ≡ 1` returns
  `τ n - τ 0`, agreeing with the direct computation.  This also shows the hypothesis
  `IsSimplePredictable (Filtration.natural B hB') τ H` is satisfiable, so the isometry is
  not vacuous.
* `integral_increment_mul_increment_isPreBrownianReal`,
  `integral_sq_increment_pythagoras_isPreBrownianReal`, `integral_sq_eval_isPreBrownianReal`:
  the `L²` martingale facts of `Increments.lean` instantiated at `B`, plus `E[(B t)²] = t`.

## The standing hypothesis, and why it is there

Every statement about `Filtration.natural B` carries `hB' : ∀ i, StronglyMeasurable (B i)`.
Mathlib's `IsPreBrownianReal` only supplies `AEMeasurable`, and
`MeasureTheory.Filtration.natural` cannot be formed from that: the filtration is a
genuine σ-algebra, not an a.e. class.  This is not a gap in the argument, it is a
condition on which process one names.  It is removed entirely by
`exists_modification_martingale_isPreBrownianReal`, at the cost of passing to a
modification, which is the standard move.  For real-valued processes
`StronglyMeasurable` and `Measurable` coincide, so the hypothesis is just measurability.

## What is *not* proved

* No quadratic variation `⟨M⟩`, so no `L²` extension of the integral off simple
  integrands: the space the extension lives on still cannot be stated.  See
  `RMTFoundations/Stochastic/Basic.lean` item 1.
* No Itô formula, no SDE, no Dyson Brownian motion.
* Nothing about the integral as a process in the time variable: `simpleIntegral H B τ n`
  is indexed by the partition step `n`, not by a continuous time, and no continuity or
  càdlàg property of it is established.
* The isometry is proved for `IsSimplePredictable` integrands, which are *uniformly
  bounded* by definition.  The `L²`-bounded case is not covered and needs the same
  density argument as the extension.
* No Doob maximal or `L^p` inequality in continuous time, so no maximal control of the
  integral.

-/

namespace RMTFoundations.Stochastic

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type* /- [definition] -/ } {mΩ : MeasurableSpace Ω /- [definition] -/ } {P : Measure Ω /- [definition] -/ } {B : ℝ≥0 → Ω → ℝ /- [definition] -/ }

section SigmaAlgebra

/-- The natural filtration at time `t₀` is exactly the σ-algebra generated by the whole
path on `Set.Iic t₀`. -/
theorem natural_eq_comap_pathIic (hB' : ∀ i, StronglyMeasurable (B i)  /- [definition] -/ ) (t₀ : ℝ≥0 /- [definition] -/ ) :
    (Filtration.natural B hB' : Filtration ℝ≥0 mΩ) t₀
      = MeasurableSpace.comap (fun ω (s : Set.Iic t₀) => B s ω) inferInstance :=
  Filtration.natural_eq_comap B hB' t₀

/-- A single increment is measurable for the shifted process. -/
theorem comap_increment_le_comap_shift {t₀ t : ℝ≥0 /- [definition] -/ } (h : t₀ ≤ t /- [standing] -/ ) :
    MeasurableSpace.comap (fun ω => B t ω - B t₀ ω) (inferInstance : MeasurableSpace ℝ)
      ≤ MeasurableSpace.comap (fun ω (s : ℝ≥0) => B (t₀ + s) ω - B t₀ ω)
          (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)) := by
  refine Measurable.comap_le ?_
  have hF : Measurable[MeasurableSpace.comap
      (fun ω (s : ℝ≥0) => B (t₀ + s) ω - B t₀ ω) (inferInstance : MeasurableSpace (ℝ≥0 → ℝ))]
      (fun ω (s : ℝ≥0) => B (t₀ + s) ω - B t₀ ω) := Measurable.of_comap_le le_rfl
  have hev := (measurable_pi_apply (t - t₀)).comp hF
  have hfun : ((fun f : ℝ≥0 → ℝ => f (t - t₀)) ∘ fun ω (s : ℝ≥0) => B (t₀ + s) ω - B t₀ ω)
      = fun ω => B t ω - B t₀ ω := by
    funext ω
    show B (t₀ + (t - t₀)) ω - B t₀ ω = B t ω - B t₀ ω
    rw [add_tsub_cancel_of_le h]
  rwa [hfun] at hev

end SigmaAlgebra

section Martingale

/-- **A pre-Brownian increment is independent of the whole past.** -/
theorem indep_natural_increment_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ )
    (hB' : ∀ i, StronglyMeasurable (B i)  /- [definition] -/ ) {t₀ t : ℝ≥0 /- [definition] -/ } (h : t₀ ≤ t /- [standing] -/ ) :
    Indep ((Filtration.natural B hB' : Filtration ℝ≥0 mΩ) t₀)
      (MeasurableSpace.comap (fun ω => B t ω - B t₀ ω) (inferInstance : MeasurableSpace ℝ)) P := by
  have hshift : Indep
      (MeasurableSpace.comap (fun ω (s : ℝ≥0) => B (t₀ + s) ω - B t₀ ω) inferInstance)
      (MeasurableSpace.comap (fun ω (s : Set.Iic t₀) => B s ω) inferInstance) P := by
    rw [← IndepFun_iff_Indep]
    exact hB.indepFun_shift t₀
  have h2 : Indep
      (MeasurableSpace.comap (fun ω => B t ω - B t₀ ω) (inferInstance : MeasurableSpace ℝ))
      ((Filtration.natural B hB' : Filtration ℝ≥0 mΩ) t₀) P :=
    indep_of_indep_of_le hshift (comap_increment_le_comap_shift h)
      (le_of_eq (natural_eq_comap_pathIic hB' t₀))
  exact h2.symm

/-- Each marginal of a pre-Brownian motion is in `L²`. -/
theorem memLp_two_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ ) (t : ℝ≥0 /- [definition] -/ ) :
    MemLp (B t) 2 P :=
  (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two

/-- **Brownian motion is a martingale for its natural filtration.** -/
theorem martingale_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ )
    (hB' : ∀ i, StronglyMeasurable (B i)  /- [definition] -/ ) :
    Martingale B (Filtration.natural B hB' : Filtration ℝ≥0 mΩ) P := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine martingale_of_indep_increments (Filtration.stronglyAdapted_natural hB')
    (fun i => hB.integrable_eval i) (fun s t hst => ?_) (fun s t _ => ?_)
  · exact indep_natural_increment_isPreBrownianReal hB hB' hst
  · exact integral_increment_isPreBrownianReal hB t s

/-- **Brownian motion, with continuous paths, is a martingale for its natural filtration.**
The same statement as `martingale_isPreBrownianReal`, for mathlib's
`ProbabilityTheory.IsBrownianReal`; continuity of paths is not used. -/
theorem martingale_isBrownianReal (hB : IsBrownianReal B P /- [standing] -/ )
    (hB' : ∀ i, StronglyMeasurable (B i)  /- [definition] -/ ) :
    Martingale B (Filtration.natural B hB' : Filtration ℝ≥0 mΩ) P :=
  martingale_isPreBrownianReal hB.toIsPreBrownianReal hB'

end Martingale

section ItoIsometry

/-- If `X` is measurable for a σ-algebra independent of the one generated by `Y`, then
`X` and `Y` are independent. -/
theorem indepFun_of_indep_comap {m : MeasurableSpace Ω /- [definition] -/ } {X Y : Ω → ℝ /- [definition] -/ }
    (hX : StronglyMeasurable[m] X /- [standing] -/ )
    (hindep : Indep m (MeasurableSpace.comap Y (inferInstance : MeasurableSpace ℝ)) P /- [standing] -/ ) :
    IndepFun X Y P := by
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le hindep hX.measurable.comap_le le_rfl

variable {τ : ℕ → ℝ≥0 /- [definition] -/ } {H : ℕ → Ω → ℝ /- [definition] -/ }

/-- A simple predictable integrand for the natural filtration of a pre-Brownian motion is
independent of the increment it multiplies. -/
theorem indepFun_simplePredictable_increment_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ )
    (hB' : ∀ i, StronglyMeasurable (B i)  /- [definition] -/ )
    (hH : IsSimplePredictable (Filtration.natural B hB' : Filtration ℝ≥0 mΩ) τ H /- [standing] -/ ) (i : ℕ /- [definition] -/ ) :
    IndepFun (H i) (fun ω => B (τ (i + 1)) ω - B (τ i) ω) P :=
  indepFun_of_indep_comap (hH.stronglyMeasurable i)
    (indep_natural_increment_isPreBrownianReal hB hB' (hH.monotone_times (Nat.le_succ i)))

/-- **The Itô isometry for Brownian motion on simple integrands.**  For a pre-Brownian
motion `B` with measurable marginals, its own natural filtration, and a simple
predictable integrand `H` along the partition `τ`,
`E[(∫ H dB)²] = ∑_{i < n} E[(H i)²] · (τ (i+1) - τ i)`. -/
theorem integral_sq_simpleIntegral_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ )
    (hB' : ∀ i, StronglyMeasurable (B i)  /- [definition] -/ )
    (hH : IsSimplePredictable (Filtration.natural B hB' : Filtration ℝ≥0 mΩ) τ H /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    ∫ ω, simpleIntegral H B τ n ω ^ 2 ∂P
      = ∑ i ∈ Finset.range n, (∫ ω, H i ω ^ 2 ∂P) * ((τ (i + 1) : ℝ) - (τ i : ℝ)) := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  refine integral_sq_simpleIntegral_of_indep_clock (martingale_isPreBrownianReal hB hB')
    (memLp_two_isPreBrownianReal hB) hH
    (indepFun_simplePredictable_increment_isPreBrownianReal hB hB' hH)
    (fun i => ((τ i : ℝ))) (fun i => ?_) n
  exact integral_sq_increment_isPreBrownianReal_le hB (hH.monotone_times (Nat.le_succ i))

/-- The simple integral against Brownian motion has mean zero. -/
theorem integral_simpleIntegral_isPreBrownianReal_eq_zero (hB : IsPreBrownianReal B P /- [standing] -/ )
    (hB' : ∀ i, StronglyMeasurable (B i)  /- [definition] -/ )
    (hH : IsSimplePredictable (Filtration.natural B hB' : Filtration ℝ≥0 mΩ) τ H /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    ∫ ω, simpleIntegral H B τ n ω ∂P = 0 := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact integral_simpleIntegral_eq_zero (martingale_isPreBrownianReal hB hB')
    (memLp_two_isPreBrownianReal hB) hH n

/-- **The constant integrand, as a consistency check and a proof that the isometry above is
not vacuous.**  For `H ≡ 1` the simple integral telescopes to `B (τ n) - B (τ 0)`, and the
isometry returns `τ n - τ 0`, which is what
`integral_sq_increment_isPreBrownianReal_le` gives directly. -/
theorem integral_sq_simpleIntegral_one_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ )
    (hB' : ∀ i, StronglyMeasurable (B i)  /- [definition] -/ ) (hτ : Monotone τ /- [standing] -/ ) (n : ℕ /- [definition] -/ ) :
    ∫ ω, simpleIntegral (fun _ _ => (1 : ℝ)) B τ n ω ^ 2 ∂P = (τ n : ℝ) - (τ 0 : ℝ) := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hH : IsSimplePredictable (Filtration.natural B hB' : Filtration ℝ≥0 mΩ) τ
      (fun _ _ => (1 : ℝ)) :=
    ⟨hτ, fun _ => stronglyMeasurable_const, ⟨1, fun _ _ => le_of_eq norm_one⟩⟩
  rw [integral_sq_simpleIntegral_isPreBrownianReal hB hB' hH n]
  have hone : ∫ _ω : Ω, (1 : ℝ) ^ 2 ∂P = 1 := by
    rw [one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one]
  have hstep : ∀ i ∈ Finset.range n,
      (∫ _ω : Ω, (1 : ℝ) ^ 2 ∂P) * ((τ (i + 1) : ℝ) - (τ i : ℝ))
        = (fun j => (τ j : ℝ)) (i + 1) - (fun j => (τ j : ℝ)) i := by
    intro i _
    rw [hone, one_mul]
  rw [Finset.sum_congr rfl hstep]
  exact Finset.sum_range_sub (fun j => (τ j : ℝ)) n

end ItoIsometry

section L2Martingale

/-- Increments of Brownian motion over non-overlapping intervals are orthogonal in `L²`. -/
theorem integral_increment_mul_increment_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ )
    (hB' : ∀ i, StronglyMeasurable (B i)  /- [definition] -/ ) {s t u v : ℝ≥0 /- [definition] -/ } (hst : s ≤ t /- [standing] -/ ) (htu : t ≤ u /- [standing] -/ )
    (huv : u ≤ v /- [standing] -/ ) :
    ∫ ω, (B t ω - B s ω) * (B v ω - B u ω) ∂P = 0 := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact integral_increment_mul_increment_eq_zero (martingale_isPreBrownianReal hB hB')
    (memLp_two_isPreBrownianReal hB) hst htu huv

/-- The `L²` Pythagoras identity for Brownian motion: `E[(B t - B s)²] = E[(B t)²] - E[(B s)²]`. -/
theorem integral_sq_increment_pythagoras_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ )
    (hB' : ∀ i, StronglyMeasurable (B i)  /- [definition] -/ ) {s t : ℝ≥0 /- [definition] -/ } (hst : s ≤ t /- [standing] -/ ) :
    ∫ ω, (B t ω - B s ω) ^ 2 ∂P = (∫ ω, B t ω ^ 2 ∂P) - ∫ ω, B s ω ^ 2 ∂P := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact integral_sq_increment (martingale_isPreBrownianReal hB hB')
    (memLp_two_isPreBrownianReal hB) hst

/-- The second moment of a pre-Brownian motion at time `t` is `t`. -/
theorem integral_sq_eval_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ ) (t : ℝ≥0 /- [definition] -/ ) :
    ∫ ω, B t ω ^ 2 ∂P = (t : ℝ) := by
  have h0 := hB.eval_zero_ae_eq_zero
  have hpt : (fun ω => (B t ω - B 0 ω) ^ 2) =ᵐ[P] fun ω => B t ω ^ 2 := by
    filter_upwards [h0] with ω hω
    rw [hω, sub_zero]
  have h := integral_sq_increment_isPreBrownianReal hB t 0
  rw [integral_congr_ae hpt] at h
  rw [h, NNReal.coe_zero, sub_zero, abs_of_nonneg t.coe_nonneg]

end L2Martingale

section Modification

/-- **Every pre-Brownian motion has a modification that is a martingale for its own natural
filtration.**  This removes the measurability hypothesis from
`martingale_isPreBrownianReal`: mathlib's `IsPreBrownianReal` only supplies
`AEMeasurable`, which is not enough to form `MeasureTheory.Filtration.natural`, but a
measurable modification is pre-Brownian again and carries the filtration. -/
theorem exists_modification_martingale_isPreBrownianReal (hB : IsPreBrownianReal B P /- [standing] -/ ) :
    ∃ (C : ℝ≥0 → Ω → ℝ) (hC : ∀ i, StronglyMeasurable (C i)),
      (∀ t, B t =ᵐ[P] C t) ∧ IsPreBrownianReal C P ∧
        Martingale C (Filtration.natural C hC : Filtration ℝ≥0 mΩ) P := by
  set C : ℝ≥0 → Ω → ℝ := fun t => (hB.aemeasurable t).mk (B t) with hCdef
  have hC : ∀ i, StronglyMeasurable (C i) := fun i =>
    ((hB.aemeasurable i).measurable_mk).stronglyMeasurable
  have hmod : ∀ t, B t =ᵐ[P] C t := fun t => (hB.aemeasurable t).ae_eq_mk
  have hCB : IsPreBrownianReal C P := hB.congr hmod
  exact ⟨C, hC, hmod, hCB, martingale_isPreBrownianReal hCB hC⟩

end Modification

end RMTFoundations.Stochastic

#print axioms RMTFoundations.Stochastic.natural_eq_comap_pathIic
#print axioms RMTFoundations.Stochastic.comap_increment_le_comap_shift
#print axioms RMTFoundations.Stochastic.indep_natural_increment_isPreBrownianReal
#print axioms RMTFoundations.Stochastic.memLp_two_isPreBrownianReal
#print axioms RMTFoundations.Stochastic.martingale_isPreBrownianReal
#print axioms RMTFoundations.Stochastic.martingale_isBrownianReal
#print axioms RMTFoundations.Stochastic.indepFun_of_indep_comap
#print axioms RMTFoundations.Stochastic.indepFun_simplePredictable_increment_isPreBrownianReal
#print axioms RMTFoundations.Stochastic.integral_sq_simpleIntegral_isPreBrownianReal
#print axioms RMTFoundations.Stochastic.integral_simpleIntegral_isPreBrownianReal_eq_zero
#print axioms RMTFoundations.Stochastic.integral_sq_simpleIntegral_one_isPreBrownianReal
#print axioms RMTFoundations.Stochastic.integral_increment_mul_increment_isPreBrownianReal
#print axioms RMTFoundations.Stochastic.integral_sq_increment_pythagoras_isPreBrownianReal
#print axioms RMTFoundations.Stochastic.integral_sq_eval_isPreBrownianReal
#print axioms RMTFoundations.Stochastic.exists_modification_martingale_isPreBrownianReal
