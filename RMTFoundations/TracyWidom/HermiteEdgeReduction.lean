import RMTFoundations.TracyWidom.HermiteEdgeODE
import RMTFoundations.TracyWidom.HermiteEdgeScale
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteEdgeReduction
open RMTFoundations.TracyWidom.GUEHermite RMTFoundations.TracyWidom.HermiteEdgeODE RMTFoundations.TracyWidom.HermiteEdgeScale
noncomputable def edgeAmplitude (N : ℕ /- [definition] -/) : ℝ :=
  (N : ℝ)^(1/12 : ℝ)
noncomputable def edgeMode (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ :=
  affineMode N (edgeAmplitude N) (2 * Real.sqrt N) (edgeScale N) x
noncomputable def edgeSlope (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ :=
  affineSlope N (edgeAmplitude N) (2 * Real.sqrt N) (edgeScale N) x
lemma edgeMode_hasDerivAt (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : HasDerivAt (edgeMode N) (edgeSlope N x) x :=
  affineMode_hasDerivAt N _ _ _ x
/-- Actual Hermite edge mode, not a free solution of an approximate ODE. -/
theorem edgeSlope_hasDerivAt (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    HasDerivAt (edgeSlope N) (edgeCoefficient N x * edgeMode N x) x := by
  have h := affineSlope_hasDerivAt N (edgeAmplitude N) (2 * Real.sqrt N) (edgeScale N) x
  change HasDerivAt (edgeSlope N)
    ((edgeScale N)^2 * ((edgePoint N x)^2/4 - (N : ℝ) - 1/2) * edgeMode N x) x at h
  rw [edge_coefficient_identity N hN x] at h
  exact h
/-- Complete growing, nondegenerate joint probe: literal modes, positive scales,
positive density, and the exact ODE all supplied together by terms. -/
theorem edge_mode_all_binder_joint_probe (n : ℕ /- [definition] -/) :
    0 < edgeAmplitude (n+1) ∧ 0 < edgeScale (n+1) ∧
      0 < hermiteDensity (n+1) (fun i => (i.val : ℝ)) ∧
      (∀ x, HasDerivAt (edgeMode (n+1)) (edgeSlope (n+1) x) x) ∧
      (∀ x, HasDerivAt (edgeSlope (n+1))
        (edgeCoefficient (n+1) x * edgeMode (n+1) x) x) := by
  refine ⟨Real.rpow_pos_of_pos (by positivity) _, edgeScale_pos _ (by omega),
    hermite_density_all_binder_joint_probe.2 n, ?_, ?_⟩
  · intro x; exact edgeMode_hasDerivAt _ x
  · intro x; exact edgeSlope_hasDerivAt _ (by omega) x
end RMTFoundations.TracyWidom.HermiteEdgeReduction

#print axioms RMTFoundations.TracyWidom.HermiteEdgeReduction.edgeAmplitude
#print axioms RMTFoundations.TracyWidom.HermiteEdgeReduction.edgeMode
#print axioms RMTFoundations.TracyWidom.HermiteEdgeReduction.edgeSlope
#print axioms RMTFoundations.TracyWidom.HermiteEdgeReduction.edgeMode_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteEdgeReduction.edgeSlope_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteEdgeReduction.edge_mode_all_binder_joint_probe
