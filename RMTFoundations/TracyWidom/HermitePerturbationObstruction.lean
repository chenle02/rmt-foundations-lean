import RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation
import RMTFoundations.TracyWidom.HalfLineIntegrabilityFoundation
import RMTFoundations.TracyWidom.HermiteEdgeReduction
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermitePerturbationObstruction
open Set Filter MeasureTheory Real
open scoped Topology
open RMTFoundations.TracyWidom.HermiteEdgeScale RMTFoundations.TracyWidom.HermiteEdgeReduction

/-- The exact additive perturbation in the literal edge ODE. -/
lemma error_identity (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    edgeCoefficient N x-x = (N:ℝ)^(-2/3:ℝ)/4*x^2-(N:ℝ)^(-1/3:ℝ)/2 := by
  unfold edgeCoefficient
  ring

/-- At every fixed positive dimension the additive coefficient error diverges.
Local uniform convergence in dimension does not give a global sup-tail bound. -/
theorem error_tendsto_atTop (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) :
    Tendsto (fun x : ℝ => edgeCoefficient N x-x) atTop atTop := by
  have hpos : 0 < (N:ℝ)^(-2/3:ℝ)/4 := by positivity
  simpa only [error_identity] using
    RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation.quadratic_tendsto
      ((N:ℝ)^(-2/3:ℝ)/4) ((N:ℝ)^(-1/3:ℝ)/2) hpos

/-- No finite sup-error budget is possible on any full right half-line. -/
theorem no_sup_tail_budget (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (s : ℝ /- [definition] -/) :
    ¬ ∃ η : ℝ, ∀ x, s ≤ x → |edgeCoefficient N x-x| ≤ η := by
  simpa only [error_identity] using RMTFoundations.TracyWidom.QuadraticTailObstructionFoundation.no_sup
    ((N:ℝ)^(-2/3:ℝ)/4) ((N:ℝ)^(-1/3:ℝ)/2) s (by positivity)

/-- The two actual envelope premises of ai_ode_comparison cannot be supplied
for a literal fixed-dimensional Hermite mode. This refutes the method adapter,
not the Hermite-to-Airy limit or any existing theorem. -/
theorem no_integrable_tail_budget (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (s : ℝ /- [definition] -/) :
    ¬ ∃ (η : ℝ) (b : ℝ → ℝ), IntegrableOn b (Ioi s) ∧
      ∀ x, s ≤ x → |edgeCoefficient N x-x| ≤ η*b x := by
  exact RMTFoundations.TracyWidom.HalfLineIntegrabilityFoundation.no_integrable_envelope
    (fun x => edgeCoefficient N x-x) s (error_tendsto_atTop N hN)

/-- Even the absolute additive error itself has infinite L1 tail mass. -/
theorem absolute_error_not_integrable (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (s : ℝ /- [definition] -/) :
    ¬ IntegrableOn (fun x => |edgeCoefficient N x-x|) (Ioi s) := by
  intro hi
  apply no_integrable_tail_budget N hN s
  exact ⟨1,fun x => |edgeCoefficient N x-x|,hi,by intros; simp⟩

/-- The excluded zero dimension has zero error; positivity of dimension is an
essential hypothesis of the obstruction, not an implicit convention. -/
theorem zero_dimension_control :
    (∀ x : ℝ, edgeCoefficient 0 x-x=0) ∧
      ∃ (η : ℝ) (b : ℝ → ℝ), 0 < η ∧ IntegrableOn b (Ioi 1) ∧
        ∀ x, 1 ≤ x → |edgeCoefficient 0 x-x| ≤ η*b x := by
  have hz (x : ℝ) : edgeCoefficient 0 x-x=0 := by
    norm_num [edgeCoefficient]
  exact ⟨hz,1,fun _ => 0,by norm_num,integrableOn_zero,by intro x hx; rw [hz]; simp⟩

/-- A growing literal-model all-binder example: actual ODE, positive amplitude,
positive scale, positive density, compact error and both infinite-tail
obstructions at the same dimension. No mode-convergence premise is assumed. -/
theorem physical_all_binder_joint_probe (n : ℕ /- [definition] -/) :
    0 < edgeAmplitude (n+1) ∧ 0 < edgeScale (n+1) ∧
      0 < RMTFoundations.TracyWidom.GUEHermite.hermiteDensity (n+1) (fun i => (i.val:ℝ)) ∧
      (∀ x, HasDerivAt (edgeMode (n+1)) (edgeSlope (n+1) x) x) ∧
      (∀ x, HasDerivAt (edgeSlope (n+1))
        (edgeCoefficient (n+1) x*edgeMode (n+1) x) x) ∧
      (∀ x : ℝ, |x| ≤ 3 → |edgeCoefficient (n+1) x-x| ≤
        3^2/4*((n+1:ℕ):ℝ)^(-2/3:ℝ)+1/2*((n+1:ℕ):ℝ)^(-1/3:ℝ)) ∧
      Tendsto (fun x : ℝ => edgeCoefficient (n+1) x-x) atTop atTop ∧
      (∀ s : ℝ, ¬ ∃ η : ℝ, ∀ x, s ≤ x → |edgeCoefficient (n+1) x-x| ≤ η) ∧
      (∀ s : ℝ, ¬ ∃ (η : ℝ) (b : ℝ → ℝ), IntegrableOn b (Ioi s) ∧
        ∀ x, s ≤ x → |edgeCoefficient (n+1) x-x| ≤ η*b x) := by
  have H := edge_mode_all_binder_joint_probe n
  exact ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2,
    fun x hx => edge_coefficient_compact_error (n+1) 3 x (by norm_num) hx,
    error_tendsto_atTop (n+1) (by omega),no_sup_tail_budget (n+1) (by omega),
    no_integrable_tail_budget (n+1) (by omega)⟩

/-- A numerical point is used only as an exact kernel-checked counterinstance. -/
theorem dimension_one_counterinstance :
    0 < edgeScale 1 ∧ 0 < edgeAmplitude 1 ∧
      edgeCoefficient 1 4-4 = (7/2:ℝ) ∧
      (1:ℝ) < |edgeCoefficient 1 4-4| ∧
      ¬ ∃ (η : ℝ) (b : ℝ → ℝ), IntegrableOn b (Ioi 1) ∧
        ∀ x, 1 ≤ x → |edgeCoefficient 1 x-x| ≤ η*b x := by
  refine ⟨edgeScale_pos 1 (by omega),Real.rpow_pos_of_pos (by norm_num) _,?_,?_,
    no_integrable_tail_budget 1 (by omega) 1⟩
  · norm_num [edgeCoefficient]
  · norm_num [edgeCoefficient]
end RMTFoundations.TracyWidom.HermitePerturbationObstruction

#print axioms RMTFoundations.TracyWidom.HermitePerturbationObstruction.error_identity
#print axioms RMTFoundations.TracyWidom.HermitePerturbationObstruction.error_tendsto_atTop
#print axioms RMTFoundations.TracyWidom.HermitePerturbationObstruction.no_sup_tail_budget
#print axioms RMTFoundations.TracyWidom.HermitePerturbationObstruction.no_integrable_tail_budget
#print axioms RMTFoundations.TracyWidom.HermitePerturbationObstruction.physical_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.HermitePerturbationObstruction.dimension_one_counterinstance
#print axioms RMTFoundations.TracyWidom.HermitePerturbationObstruction.absolute_error_not_integrable
#print axioms RMTFoundations.TracyWidom.HermitePerturbationObstruction.zero_dimension_control
