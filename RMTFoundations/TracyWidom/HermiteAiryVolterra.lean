import RMTFoundations.TracyWidom.PerturbedAiryVolterra
import RMTFoundations.TracyWidom.HermiteEdgeReduction
import RMTFoundations.Airy.Core
import RMTFoundations.Airy.ODE
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteAiryVolterra
open Real MeasureTheory intervalIntegral
open RMTFoundations.TracyWidom.HermiteEdgeReduction RMTFoundations.TracyWidom.HermiteEdgeScale
open RMTFoundations.Airy RMTFoundations.TracyWidom.PerturbedAiryVolterra

noncomputable def airyW : ℝ :=
  airyAiReal 0*deriv airyBiReal 0-deriv airyAiReal 0*airyBiReal 0
lemma airyW_pos : 0 < airyW := by
  unfold airyW
  exact sub_pos.mpr (lt_trans (mul_neg_of_neg_of_pos deriv_airyAiReal_zero_neg airyBiReal_zero_pos)
    (mul_pos airyAiReal_zero_pos deriv_airyBiReal_zero_pos))
lemma bi_hasDerivAt (x : ℝ /- [definition] -/) :
    HasDerivAt airyBiReal (deriv airyBiReal x) x :=
  (hasDerivAt_airyBiReal x).differentiableAt.hasDerivAt
lemma bi_slope_hasDerivAt (x : ℝ /- [definition] -/) :
    HasDerivAt (deriv airyBiReal) (x*airyBiReal x) x := by
  have h := iteratedDeriv_two_airyBiReal x
  rw [show (2:ℕ)=1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one] at h
  simpa only [h] using (hasDerivAt_deriv_airyBiReal x).differentiableAt.hasDerivAt
lemma airyW_at (x : ℝ /- [definition] -/) :
    airyAiReal x*deriv airyBiReal x-deriv airyAiReal x*airyBiReal x=airyW := by
  exact RMTFoundations.Airy.airyWronskian_eq
    ⟨hasDerivAt_airyAiReal',hasDerivAt_deriv_airyAiReal'⟩
    ⟨bi_hasDerivAt,bi_slope_hasDerivAt⟩ x 0

/-- Exact Duhamel representation of the actual rescaled Hermite mode. All ODE,
continuity and nonvanishing-Wronskian premises are supplied by  proofs. -/
theorem edge_mode_volterra (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    edgeMode N x =
      ((deriv airyBiReal 0*edgeMode N 0-airyBiReal 0*edgeSlope N 0)*airyAiReal x +
        (airyAiReal 0*edgeSlope N 0-deriv airyAiReal 0*edgeMode N 0)*airyBiReal x +
        airyBiReal x*(∫ t in 0..x, airyAiReal t*(edgeCoefficient N t-t)*edgeMode N t) -
        airyAiReal x*(∫ t in 0..x, airyBiReal t*(edgeCoefficient N t-t)*edgeMode N t))/airyW := by
  have hq : Continuous (edgeCoefficient N) := by unfold edgeCoefficient; fun_prop
  exact variation_of_constants (edgeMode N) (edgeSlope N)
    airyAiReal (deriv airyAiReal) airyBiReal (deriv airyBiReal) (edgeCoefficient N) id
    (edgeMode_hasDerivAt N) (edgeSlope_hasDerivAt N hN)
    hasDerivAt_airyAiReal' hasDerivAt_deriv_airyAiReal'
    bi_hasDerivAt bi_slope_hasDerivAt hq continuous_id airyW x airyW_pos.ne' (airyW_at x)

/-- Complete growing literal-model example; not an assumed initial-data limit. -/
theorem edge_volterra_joint_probe (n : ℕ /- [definition] -/) :
    0 < airyW ∧ 0 < edgeAmplitude (n+1) ∧ 0 < edgeScale (n+1) ∧
      0 < RMTFoundations.TracyWidom.GUEHermite.hermiteDensity (n+1) (fun i => (i.val:ℝ)) ∧
      ∀ x : ℝ, edgeMode (n+1) x =
        ((deriv airyBiReal 0*edgeMode (n+1) 0-airyBiReal 0*edgeSlope (n+1) 0)*airyAiReal x +
          (airyAiReal 0*edgeSlope (n+1) 0-deriv airyAiReal 0*edgeMode (n+1) 0)*airyBiReal x +
          airyBiReal x*(∫ t in 0..x, airyAiReal t*(edgeCoefficient (n+1) t-t)*edgeMode (n+1) t) -
          airyAiReal x*(∫ t in 0..x, airyBiReal t*(edgeCoefficient (n+1) t-t)*edgeMode (n+1) t))/airyW := by
  have H := edge_mode_all_binder_joint_probe n
  exact ⟨airyW_pos,H.1,H.2.1,H.2.2.1,edge_mode_volterra (n+1) (by omega)⟩
end RMTFoundations.TracyWidom.HermiteAiryVolterra

#print axioms RMTFoundations.TracyWidom.HermiteAiryVolterra.airyW
#print axioms RMTFoundations.TracyWidom.HermiteAiryVolterra.airyW_pos
#print axioms RMTFoundations.TracyWidom.HermiteAiryVolterra.bi_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteAiryVolterra.bi_slope_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteAiryVolterra.airyW_at
#print axioms RMTFoundations.TracyWidom.HermiteAiryVolterra.edge_mode_volterra
#print axioms RMTFoundations.TracyWidom.HermiteAiryVolterra.edge_volterra_joint_probe
