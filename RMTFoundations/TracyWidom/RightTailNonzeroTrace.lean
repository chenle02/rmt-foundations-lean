import RMTFoundations.TracyWidom.LeftTail
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Filter
open scoped Topology
open RMTFoundations.Airy RMTFoundations.AiryKernel
open RMTFoundations.TWLeftTail RMTFoundations.Fredholm

/-- Literal physical positive-contraction binders have a strictly positive trace together. -/
theorem rightTail_nonzero_trace_spectral_joint_probe :
    ∃ a : ℕ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≤ 1) ∧
      HasProd (fun i => 1-a i) (TW2R (-1)) ∧
      HasSum a (airyTraceIntegral (-1)) ∧ 0 < airyTraceIntegral (-1) := by
  obtain ⟨b,hb,hAi,hUnit,hPositive,hNorm,hCompressions,hSum,hTrace,hBounds,hLimit⟩ :=
    airy_left_endpoint_joint_probe
  obtain ⟨a,h0,h1,hp,ht⟩ := TW2R_spectral_bridge_of_contraction (-1) hNorm
  exact ⟨a,h0,h1,hp,ht,hTrace⟩

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.rightTail_nonzero_trace_spectral_joint_probe
