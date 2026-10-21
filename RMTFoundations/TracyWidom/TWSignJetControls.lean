import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.TWSignJetControls
/-- Positive Hamiltonian and positive F1 logarithmic slope do not determine
the sign of a PII endpoint jet. This is a pointwise counterinstance, not a
normalized global PII solution. -/
theorem negative_jet_counterinstance :
    ∃ s q dq ddq u p v : ℝ,
      s<0 ∧ q<0 ∧ dq ≠ 0 ∧ 0<u ∧ 0<q+u ∧
      dq=p-u*q ∧ ddq=s*q+2*q^3 ∧ u^2-2*v=q^2 ∧
      u=dq^2-s*q^2-q^4 := by
  refine ⟨-4,-1,1,2,4,-3,15/2,?_⟩
  norm_num
/-- A simple zero also satisfies those scalar identities. Neither quadratic
positivity nor monotonic determinant slope excludes crossing zero. -/
theorem simple_zero_jet_counterinstance :
    ∃ s q dq ddq u p v : ℝ,
      s<0 ∧ q=0 ∧ dq ≠ 0 ∧ 0<u ∧ 0<q+u ∧
      dq=p-u*q ∧ ddq=s*q+2*q^3 ∧ u^2-2*v=q^2 ∧
      u=dq^2-s*q^2-q^4 := by
  refine ⟨-4,0,1,0,1,1,1/2,?_⟩
  norm_num
end RMTFoundations.TracyWidom.TWSignJetControls
#print axioms RMTFoundations.TracyWidom.TWSignJetControls.negative_jet_counterinstance
#print axioms RMTFoundations.TracyWidom.TWSignJetControls.simple_zero_jet_counterinstance
