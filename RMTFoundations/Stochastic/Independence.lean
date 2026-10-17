import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Conditional expectation under independence, and the martingale property

The pinned mathlib has no lemma computing the conditional expectation of a
random variable independent of the conditioning σ-algebra.  That single lemma is
what prevents mathlib's `ProbabilityTheory.IsBrownianReal` and mathlib's
`MeasureTheory.Martingale` from ever meeting: Brownian motion is built there from
its independent increments, and the martingale property is the only bridge.

## What is proved

* `condExp_eq_integral_of_indep`: if `X` is integrable and measurable for a
  σ-algebra independent of `m`, then `μ[X | m] =ᵐ[μ] fun _ => ∫ X`.
* `martingale_of_indep_increments`: an adapted, integrable process whose increment
  over `[s, t]` is independent of the past `ℱ s` and has mean zero is a martingale.

## What is *not* proved

The instantiation at Brownian motion is not done here.  It is done in
`RMTFoundations/Stochastic/BrownianMartingale.lean`, which supplies the two σ-algebra
comparisons that turn `ProbabilityTheory.IsPreBrownianReal.indepFun_shift` into the
`hindep` hypothesis of `martingale_of_indep_increments`; the centring hypothesis is
discharged by `RMTFoundations/Stochastic/BrownianIncrements.lean`.  Nothing in this file
mentions Brownian motion, and nothing here is specialised to `ℝ≥0`.
-/

namespace RMTFoundations.Stochastic

open MeasureTheory ProbabilityTheory

variable {Ω : Type* /- [definition] -/ } {m0 : MeasurableSpace Ω /- [definition] -/ } {μ : Measure Ω /- [definition] -/ }

/-- **Conditional expectation of an independent variable.** If `X` is integrable and
measurable for a σ-algebra `mX` independent of `m`, then conditioning on `m` gives the
mean of `X`. -/
theorem condExp_eq_integral_of_indep [IsFiniteMeasure μ /- [standing] -/ ] {m mX : MeasurableSpace Ω /- [definition] -/ }
    (hm : m ≤ m0 /- [standing] -/ ) {X : Ω → ℝ /- [definition] -/ } (hX : Integrable X μ /- [standing] -/ ) (hXm : Measurable[mX] X /- [standing] -/ )
    (hindep : Indep m mX μ /- [standing] -/ ) :
    μ[X | m] =ᵐ[μ] fun _ => ∫ ω, X ω ∂μ := by
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hX ?_ ?_ ?_).symm
  · intro s _ hμs
    exact integrableOn_const hμs.ne
  · intro s hs _
    have hsm : MeasurableSet[m0] s := hm s hs
    have hind : IndepFun (s.indicator fun _ => (1 : ℝ)) X μ := by
      rw [IndepFun_iff_Indep]
      refine indep_of_indep_of_le hindep ?_ hXm.comap_le
      exact (Measurable.indicator (measurable_const (a := (1 : ℝ))) hs).comap_le
    have hfac := hind.integral_mul_eq_mul_integral
      ((measurable_const.indicator hsm).aestronglyMeasurable) hX.aestronglyMeasurable
    have hpt : ∀ ω, (s.indicator (fun _ => (1 : ℝ)) * X) ω = s.indicator X ω := by
      intro ω
      by_cases hω : ω ∈ s
      · rw [Pi.mul_apply, Set.indicator_of_mem hω, Set.indicator_of_mem hω, one_mul]
      · rw [Pi.mul_apply, Set.indicator_of_notMem hω, Set.indicator_of_notMem hω, zero_mul]
    have hleft : ∫ ω, (s.indicator (fun _ => (1 : ℝ)) * X) ω ∂μ = ∫ ω in s, X ω ∂μ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_indicator hsm]
    have hone : ∫ ω, s.indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real s := by
      rw [integral_indicator_const (1 : ℝ) hsm, smul_eq_mul, mul_one]
    rw [setIntegral_const, smul_eq_mul, ← hleft, hfac, hone]
  · exact stronglyMeasurable_const.aestronglyMeasurable

variable {ι : Type* /- [definition] -/ } [Preorder ι /- [definition] -/ ] {ℱ : Filtration ι m0 /- [definition] -/ } {X : ι → Ω → ℝ /- [definition] -/ }

/-- **Independent centred increments give a martingale.** An adapted, integrable process
whose increment over `[s, t]` is independent of the past `ℱ s` and centred is a
martingale for `ℱ`.  This is the bridge between a process described by its increments
(such as mathlib's Brownian motion) and mathlib's martingale theory. -/
theorem martingale_of_indep_increments [IsFiniteMeasure μ /- [standing] -/ ]
    (hadapted : StronglyAdapted ℱ X /- [standing] -/ ) (hint : ∀ i, Integrable (X i) μ /- [standing] -/ )
    (hindep : ∀ s t : ι, s ≤ t →
      Indep (ℱ s) (MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance) μ /- [standing] -/ )
    (hcentred : ∀ s t : ι, s ≤ t → ∫ ω, (X t ω - X s ω) ∂μ = 0 /- [standing] -/ ) :
    Martingale X ℱ μ := by
  refine ⟨hadapted, fun s t hst => ?_⟩
  have hΔint : Integrable (fun ω => X t ω - X s ω) μ := (hint t).sub (hint s)
  have hΔmeas : Measurable[MeasurableSpace.comap (fun ω => X t ω - X s ω) inferInstance]
      fun ω => X t ω - X s ω := Measurable.of_comap_le le_rfl
  have h1 : μ[fun ω => X t ω - X s ω | ℱ s] =ᵐ[μ] fun _ => ∫ ω, (X t ω - X s ω) ∂μ :=
    condExp_eq_integral_of_indep (ℱ.le s) hΔint hΔmeas (hindep s t hst)
  have h2 : μ[X t - X s | ℱ s] =ᵐ[μ] μ[X t | ℱ s] - μ[X s | ℱ s] :=
    condExp_sub (hint t) (hint s) (ℱ s)
  have h3 : (μ[X s | ℱ s]) = X s :=
    condExp_of_stronglyMeasurable (ℱ.le s) (hadapted s) (hint s)
  filter_upwards [h1, h2] with ω hω1 hω2
  have h4 : (μ[X t | ℱ s]) ω - (μ[X s | ℱ s]) ω = ∫ ω, (X t ω - X s ω) ∂μ := by
    rw [← Pi.sub_apply, ← hω2]
    exact hω1
  rw [hcentred s t hst, h3] at h4
  linarith [h4]

end RMTFoundations.Stochastic

#print axioms RMTFoundations.Stochastic.condExp_eq_integral_of_indep
#print axioms RMTFoundations.Stochastic.martingale_of_indep_increments
