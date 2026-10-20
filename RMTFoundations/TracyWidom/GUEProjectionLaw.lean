import RMTFoundations.TracyWidom.GUEDensity
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.GUEProjectionLaw
open MeasureTheory Set
open RMTFoundations.TracyWidom.GUEProjection

/-- Concrete normalized unordered finite Hermite projection law.
No matrix spectral pushforward or multi-time identity is asserted. -/
noncomputable def projectionLaw (N : ℕ /- [definition] -/) :
    Measure (Fin N → ℝ) :=
  (Measure.pi (fun _ => (volume : Measure ℝ))).withDensity
    (fun x => ENNReal.ofReal (gueDensity N x))

instance projectionLaw_probability (N : ℕ /- [definition] -/) :
    IsProbabilityMeasure (projectionLaw N) := by
  constructor
  rw [projectionLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gue_density_integrable N)
      (Filter.Eventually.of_forall (gue_density_nonnegative N)),
    gue_density_integral, ENNReal.ofReal_one]

/-- Literal gap event for the largest unordered particle. -/
noncomputable def projectionGap (N : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : ℝ :=
  (projectionLaw N).real {x | ∀ i, x i ≤ s}

lemma projectionGap_measurableSet (N : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) :
    MeasurableSet {x : Fin N → ℝ | ∀ i, x i ≤ s} := by
  simp only [setOf_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_le (measurable_pi_apply i) measurable_const)

lemma projectionGap_nonneg (N : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : 0 ≤ projectionGap N s := by
  exact ENNReal.toReal_nonneg

lemma projectionGap_le_one (N : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) : projectionGap N s ≤ 1 := by
  exact measureReal_le_one

lemma projectionGap_monotone (N : ℕ /- [definition] -/) :
    Monotone (projectionGap N) := by
  intro s t hst
  exact measureReal_mono (fun x hx i => (hx i).trans hst)

/-- The genuine gap probability equals the integral of the
finite-N determinantal density. This is a density integral, not a claimed
multi-time extended Fredholm identity. -/
theorem projectionGap_density_integral (N : ℕ /- [definition] -/)
    (s : ℝ /- [definition] -/) :
    projectionGap N s =
      ∫ x in {x : Fin N → ℝ | ∀ i, x i ≤ s}, gueDensity N x
        ∂Measure.pi (fun _ => (volume : Measure ℝ)) := by
  rw [projectionGap, measureReal_def, projectionLaw,
    withDensity_apply _ (projectionGap_measurableSet N s),
    ← ofReal_integral_eq_lintegral_ofReal ((gue_density_integrable N).restrict)
      (Filter.Eventually.of_forall (gue_density_nonnegative N)),
    ENNReal.toReal_ofReal]
  exact integral_nonneg (gue_density_nonnegative N)

/-- Nondegenerate same-instance example: three distinct particles, positive
physical density, normalized measure and genuine monotone gap function. -/
theorem projectionLaw_all_binder_joint_probe :
    ∃ x : Fin 3 → ℝ, Function.Injective x ∧ 0 < gueDensity 3 x ∧
      IsProbabilityMeasure (projectionLaw 3) ∧
      Monotone (projectionGap 3) ∧
      (∀ s, 0 ≤ projectionGap 3 s ∧ projectionGap 3 s ≤ 1) ∧
      (∫ y : Fin 3 → ℝ, gueDensity 3 y
        ∂Measure.pi (fun _ => (volume : Measure ℝ))) = 1 := by
  obtain ⟨x,hx,hpos,hdet⟩ := gue_density_joint_probe
  exact ⟨x,hx,hpos,inferInstance,projectionGap_monotone 3,
    fun s => ⟨projectionGap_nonneg 3 s,projectionGap_le_one 3 s⟩,
    gue_density_integral 3⟩

end RMTFoundations.TracyWidom.GUEProjectionLaw

#print axioms RMTFoundations.TracyWidom.GUEProjectionLaw.projectionLaw
#print axioms RMTFoundations.TracyWidom.GUEProjectionLaw.projectionLaw_probability
#print axioms RMTFoundations.TracyWidom.GUEProjectionLaw.projectionGap
#print axioms RMTFoundations.TracyWidom.GUEProjectionLaw.projectionGap_measurableSet
#print axioms RMTFoundations.TracyWidom.GUEProjectionLaw.projectionGap_nonneg
#print axioms RMTFoundations.TracyWidom.GUEProjectionLaw.projectionGap_le_one
#print axioms RMTFoundations.TracyWidom.GUEProjectionLaw.projectionGap_monotone
#print axioms RMTFoundations.TracyWidom.GUEProjectionLaw.projectionGap_density_integral
#print axioms RMTFoundations.TracyWidom.GUEProjectionLaw.projectionLaw_all_binder_joint_probe
