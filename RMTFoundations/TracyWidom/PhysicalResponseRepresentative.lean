import RMTFoundations.TracyWidom.AiryWeightedResponse
import RMTFoundations.TracyWidom.ResolventDiagonal
import RMTFoundations.TracyWidom.AiryEndpointRowDerivative



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.PhysicalResponseRepresentative

open MeasureTheory Filter Set
open scoped Topology InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.Fredholm
open RMTFoundations.TWOneBounds RMTFoundations.TracyWidom.AiryWeightedKernel
open RMTFoundations.TracyWidom.AiryWeightedResponse RMTFoundations.TracyWidom.ResponseDerivative
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.ResolventDiagonal
open RMTFoundations.TracyWidom.AiryEndpointRowDerivative

/-- The scalar representative of the genuine inverse Airy-boundary response. -/
noncomputable def physicalResponseRepresentative
    (s x : ℝ) -- [definition]
    : ℝ := airyAiReal (s+x) +
      ∫ y, airyKernelIntegral (x+s) (y+s)*(responseVector s) y ∂halfLineMeasure

/-- Its defining scalar integral is absolutely integrable at every real coordinate. -/
theorem physicalResponseRepresentative_integrable
    (s x : ℝ) -- [definition]
    : Integrable (fun y => airyKernelIntegral (x+s) (y+s)*(responseVector s) y)
      halfLineMeasure := integrable_AiryKernelResponse s x (responseVector s)

/-- The scalar representative coincides almost everywhere with the actual L² response. -/
theorem physicalResponseRepresentative_apply_ae
    (s : ℝ) -- [definition]
    : (fun x => physicalResponseRepresentative s x) =ᵐ[halfLineMeasure] responseVector s := by
  filter_upwards [responseVector_eq_source_add_kernel_ae s,
    airyBoundaryVector_apply_ae s, airyKernelShift_apply_ae s (responseVector s)] with x hQ ha hK
  unfold physicalResponseRepresentative
  rw [hQ,ha,hK]

/-- The canonical q is the endpoint of this scalar representative, not an arbitrary Lp evaluation. -/
theorem physicalResponseRepresentative_endpoint
    (s : ℝ) -- [definition]
    : physicalResponseRepresentative s 0 = resolventQ s := by
  rw [resolventQ_eq_scalar_endpoint]
  simp only [physicalResponseRepresentative,add_zero,zero_add]
  apply congrArg (fun z : ℝ => airyAiReal s + z)
  rw [real_inner_comm]
  change (∫ y, airyKernelIntegral s (y+s)*(responseVector s) y ∂halfLineMeasure) =
    inner ℝ (responseVector s) (airyEndpointRow s)
  rw [airyEndpointRow_pairing]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    change airyKernelIntegral s (y+s)*(responseVector s) y =
      airyKernelIntegral (y+s) s*(responseVector s) y
    rw [airyKernelIntegral_symm])

/-- Every actual L² Airy-kernel image has a continuous scalar integral representative. -/
theorem airyKernelResponse_continuous
    (s : ℝ) -- [definition]
    (f : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Continuous (fun x : ℝ => ∫ y, airyKernelIntegral (x+s) (y+s)*f y ∂halfLineMeasure) := by
  obtain ⟨D,hD,hb⟩ := shiftedKernel_exp_bound s
  apply continuous_iff_continuousAt.mpr
  intro x₀
  have hlow : ∀ᶠ x : ℝ in 𝓝 x₀, x₀-1 ≤ x :=
    eventually_ge_nhds (by linarith : x₀-1 < x₀)
  apply continuousAt_of_dominated (bound := fun y : ℝ =>
    (D*Real.exp (-(x₀-1)))*(Real.exp (-y)*|f y|))
  · apply Eventually.of_forall
    intro x
    have hk : Continuous (fun y : ℝ => airyKernelIntegral (x+s) (y+s)) := by
      have hp : Continuous (fun y : ℝ => (x+s,y+s)) :=
        continuous_const.prodMk (continuous_id.add continuous_const)
      simpa only [Function.comp_def] using K_Ai_continuous.comp hp
    exact hk.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f)
  · filter_upwards [hlow] with x hx
    apply ae_of_all
    intro y
    simp only [Real.norm_eq_abs,abs_mul]
    calc |airyKernelIntegral (x+s) (y+s)| *|f y| ≤
        (D*Real.exp (-x)*Real.exp (-y))*|f y| :=
          mul_le_mul_of_nonneg_right (hb x y) (abs_nonneg _)
      _ ≤ (D*Real.exp (-(x₀-1)))*(Real.exp (-y)*|f y|) := by
        have he : Real.exp (-x) ≤ Real.exp (-(x₀-1)) := Real.exp_le_exp.mpr (by linarith)
        calc _ = (D*Real.exp (-x))*(Real.exp (-y)*|f y|) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left he hD.le) (by positivity)
  · exact (integrable_expWeight_mul_abs f).const_mul _
  · apply ae_of_all
    intro y
    have hk : Continuous (fun x : ℝ => airyKernelIntegral (x+s) (y+s)) := by
      have hp : Continuous (fun x : ℝ => (x+s,y+s)) :=
        (continuous_id.add continuous_const).prodMk continuous_const
      simpa only [Function.comp_def] using K_Ai_continuous.comp hp
    exact (hk.mul continuous_const).continuousAt

/-- The physical response has a genuine continuous scalar representative for every real shift. -/
theorem physicalResponseRepresentative_continuous
    (s : ℝ) -- [definition]
    : Continuous (physicalResponseRepresentative s) :=
  (RMTFoundations.AiryBounds.Ai_continuous.comp (continuous_const.add continuous_id)).add
    (airyKernelResponse_continuous s (responseVector s))

/-- The nonzero physical model jointly realizes continuity, integral existence and both links. -/
theorem physical_response_representative_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧ responseVector 0 ≠ 0 ∧
      (∀ s x : ℝ, Integrable (fun y => airyKernelIntegral (x+s) (y+s)*(responseVector s) y)
        halfLineMeasure) ∧
      (∀ s : ℝ, (fun x => physicalResponseRepresentative s x) =ᵐ[halfLineMeasure] responseVector s) ∧
      (∀ s : ℝ, physicalResponseRepresentative s 0 = resolventQ s) ∧
      (∀ s : ℝ, Continuous (physicalResponseRepresentative s)) :=
  ⟨airyBoundaryVector_ne_zero 0,response_derivative_all_binder_joint_probe.2.2.1,
    physicalResponseRepresentative_integrable,physicalResponseRepresentative_apply_ae,
    physicalResponseRepresentative_endpoint,physicalResponseRepresentative_continuous⟩

end RMTFoundations.TracyWidom.PhysicalResponseRepresentative
#print axioms RMTFoundations.TracyWidom.PhysicalResponseRepresentative.physicalResponseRepresentative
#print axioms RMTFoundations.TracyWidom.PhysicalResponseRepresentative.physicalResponseRepresentative_integrable
#print axioms RMTFoundations.TracyWidom.PhysicalResponseRepresentative.physicalResponseRepresentative_apply_ae
#print axioms RMTFoundations.TracyWidom.PhysicalResponseRepresentative.physicalResponseRepresentative_endpoint
#print axioms RMTFoundations.TracyWidom.PhysicalResponseRepresentative.airyKernelResponse_continuous
#print axioms RMTFoundations.TracyWidom.PhysicalResponseRepresentative.physicalResponseRepresentative_continuous
#print axioms RMTFoundations.TracyWidom.PhysicalResponseRepresentative.physical_response_representative_joint_probe
