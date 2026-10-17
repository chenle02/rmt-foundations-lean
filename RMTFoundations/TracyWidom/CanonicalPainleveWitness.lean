import RMTFoundations.TracyWidom.PhysicalPainleveII
import RMTFoundations.TracyWidom.HMNormalization
import RMTFoundations.TracyWidom.IntegralRepresentations
import RMTFoundations.TracyWidom.PhysicalResponseRepresentative



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.CanonicalPainleveWitness

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.ResolventDiagonal
open RMTFoundations.TracyWidom.AiryBoundaryDerivative RMTFoundations.TracyWidom.ResponseDerivative
open RMTFoundations.TracyWidom.PhysicalPainleveII RMTFoundations.TracyWidom.HMNormalization
open RMTFoundations.TracyWidom.IntegralRepresentations RMTFoundations.TracyWidom.PhysicalResponseRepresentative

/-- The canonical physical Fredholm coordinate jointly realizes Painleve II,
the relative Airy normalization and both genuine Tracy--Widom tail formulas.
The source, derivative source and response are nonzero in the same actual model.
This states existence with the right Airy normalization; it does not assert
uniqueness among arbitrary global Painleve II solutions. -/
theorem canonical_painleveII_tracyWidom_witness :
    airyBoundaryVector 0 ≠ 0 ∧ airyBoundaryDerivative 0 ≠ 0 ∧ responseVector 0 ≠ 0 ∧
      0 < resolventU 0 ∧
      ∃ q : ℝ → ℝ,
        q = resolventQ ∧
        (∀ s : ℝ, q s = physicalResponseRepresentative s 0) ∧
        (∀ s : ℝ, Continuous (physicalResponseRepresentative s)) ∧
        (∀ s : ℝ, (fun x => physicalResponseRepresentative s x) =ᵐ[halfLineMeasure]
          responseVector s) ∧
        (∀ s : ℝ, q s = airyAiReal s + inner ℝ (boundaryKernelRow s) (responseVector s)) ∧
        (∀ s : ℝ, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
        Tendsto (fun s : ℝ => q s/airyAiReal s) atTop (𝓝 1) ∧
        (∀ s : ℝ,
          IntegrableOn q (Ioi s) ∧
          IntegrableOn (fun t => (q t)^2) (Ioi s) ∧
          IntegrableOn (fun t => (t-s)*(q t)^2) (Ioi s) ∧
          TW2R s = Real.exp (-(∫ t in Ioi s, (t-s)*(q t)^2)) ∧
          TW1R s^2 = TW2R s*Real.exp (-(∫ t in Ioi s, q t))) := by
  refine ⟨airyBoundaryVector_ne_zero 0,airyBoundaryDerivative_zero_ne,
    response_derivative_all_binder_joint_probe.2.2.1,airy_inverse_square_boundary_positive 0,
    resolventQ,rfl,(fun s => (physicalResponseRepresentative_endpoint s).symm),
    physicalResponseRepresentative_continuous,physicalResponseRepresentative_apply_ae,
    resolventQ_eq_scalar_endpoint,hasDerivAt_deriv_resolventQ,
    resolventQ_relative_Airy_atTop,?_⟩
  intro s
  exact ⟨integrableOn_resolventQ s,(resolventQ_square_tail_integrals s).1,
    (resolventQ_square_tail_integrals s).2.2.1,TW2R_eq_exp_negative_weighted_square_tail s,
    TW1R_sq_eq_TW2R_mul_exp_negative_tail s⟩

/-- The same actual witness with first differentiability explicitly exported. -/
theorem canonical_painleveII_classical_tracyWidom_witness :
    airyBoundaryVector 0 ≠ 0 ∧ airyBoundaryDerivative 0 ≠ 0 ∧ responseVector 0 ≠ 0 ∧
      0 < resolventU 0 ∧
      ∃ q : ℝ → ℝ,
        q = resolventQ ∧
        Differentiable ℝ q ∧
        (∀ s : ℝ, q s = physicalResponseRepresentative s 0) ∧
        (∀ s : ℝ, Continuous (physicalResponseRepresentative s)) ∧
        (∀ s : ℝ, (fun x => physicalResponseRepresentative s x) =ᵐ[halfLineMeasure]
          responseVector s) ∧
        (∀ s : ℝ, q s = airyAiReal s + inner ℝ (boundaryKernelRow s) (responseVector s)) ∧
        (∀ s : ℝ, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
        Tendsto (fun s : ℝ => q s/airyAiReal s) atTop (𝓝 1) ∧
        (∀ s : ℝ,
          IntegrableOn q (Ioi s) ∧
          IntegrableOn (fun t => (q t)^2) (Ioi s) ∧
          IntegrableOn (fun t => (t-s)*(q t)^2) (Ioi s) ∧
          TW2R s = Real.exp (-(∫ t in Ioi s, (t-s)*(q t)^2)) ∧
          TW1R s^2 = TW2R s*Real.exp (-(∫ t in Ioi s, q t))) := by
  rcases canonical_painleveII_tracyWidom_witness with
    ⟨ha,hb,hQ,hu,q,hqe,hend,hcont,hae,hscalar,hode,hasym,htails⟩
  refine ⟨ha,hb,hQ,hu,q,hqe,?_,hend,hcont,hae,hscalar,hode,hasym,htails⟩
  rw [hqe]
  intro s
  exact (RMTFoundations.TracyWidom.EndpointCalculus.hasDerivAt_resolventQ s).differentiableAt

end RMTFoundations.TracyWidom.CanonicalPainleveWitness

#print axioms RMTFoundations.TracyWidom.CanonicalPainleveWitness.canonical_painleveII_tracyWidom_witness

#print axioms RMTFoundations.TracyWidom.CanonicalPainleveWitness.canonical_painleveII_classical_tracyWidom_witness
