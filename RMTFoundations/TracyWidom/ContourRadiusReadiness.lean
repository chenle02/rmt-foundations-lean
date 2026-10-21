import RMTFoundations.TracyWidom.ContourEdgePowers
import RMTFoundations.TracyWidom.ContourRadiusAlgebra
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ContourRadiusReadiness
open Real
open RMTFoundations.TracyWidom.ContourEdgePowers RMTFoundations.TracyWidom.ContourRadiusAlgebra
/-- The chosen radius lies strictly below the turning point for every requested halfline. -/
theorem radius_readiness (N : ℕ /- [definition] -/)
    (s y : ℝ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (hd : edgeDelta N ≤ (1/2:ℝ) /- [standing] -/)
    (hs : edgeDelta N*|s| ≤ 1 /- [standing] -/)
    (hy : s ≤ y /- [standing] -/) :
    0 < sqrt (N:ℝ)*(1-edgeDelta N) ∧
    0 < (N:ℝ)*edgeDelta N/2 ∧
    -1 ≤ edgeDelta N*s ∧
    (N:ℝ)*edgeDelta N/2 ≤
      (sqrt (N:ℝ)*(1-edgeDelta N))*
        (sqrt (N:ℝ)*(2+(edgeDelta N)^2*y)-2*(sqrt (N:ℝ)*(1-edgeDelta N))) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast hN
  have hp := edgeDelta_pos N hN
  have hlow : -1 ≤ edgeDelta N*s := by
    have H := mul_le_mul_of_nonneg_left (neg_abs_le s) hp.le
    nlinarith
  have hy' : -1 ≤ edgeDelta N*y :=
    hlow.trans (mul_le_mul_of_nonneg_left hy hp.le)
  have hd1 : 0 < 1-edgeDelta N := by linarith
  refine ⟨mul_pos (sqrt_pos.mpr hn) hd1,by positivity,hlow,?_⟩
  rw [radius_gap_identity _ _ _ hn.le]
  have H := mul_le_mul (show (1/2:ℝ) ≤ 1-edgeDelta N by linarith)
    (show (1:ℝ) ≤ 2+edgeDelta N*y by linarith) (by norm_num) (by linarith)
  have H' := mul_le_mul_of_nonneg_left H (mul_nonneg hn.le hp.le)
  nlinarith
/-- Actual scales satisfy all premises for arbitrarily large positive dimensions and every endpoint. -/
theorem readiness_joint_probe (s : ℝ /- [definition] -/)
    (k : ℕ /- [definition] -/) :
    ∃ N : ℕ, k < N ∧ 0 < N ∧ edgeDelta N ≤ (1/2:ℝ) ∧ edgeDelta N*|s| ≤ 1 ∧
      ∀ y : ℝ, s ≤ y →
      0 < sqrt (N:ℝ)*(1-edgeDelta N) ∧ 0 < (N:ℝ)*edgeDelta N/2 ∧
      -1 ≤ edgeDelta N*s ∧ (N:ℝ)*edgeDelta N/2 ≤
        (sqrt (N:ℝ)*(1-edgeDelta N))*
          (sqrt (N:ℝ)*(2+(edgeDelta N)^2*y)-2*(sqrt (N:ℝ)*(1-edgeDelta N))) := by
  obtain ⟨K,hK,h⟩ := endpoint_threshold s
  let N := max K (k+1)
  have hKN : K ≤ N := le_max_left _ _
  have hn : 0 < N := by omega
  exact ⟨N,by dsimp [N];omega,hn,(h N hKN).2.1,(h N hKN).2.2,
    fun y hy => radius_readiness N s y hn (h N hKN).2.1 (h N hKN).2.2 hy⟩
end RMTFoundations.TracyWidom.ContourRadiusReadiness

#print axioms RMTFoundations.TracyWidom.ContourRadiusReadiness.radius_readiness
#print axioms RMTFoundations.TracyWidom.ContourRadiusReadiness.readiness_joint_probe
