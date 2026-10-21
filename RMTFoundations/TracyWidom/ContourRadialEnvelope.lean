import RMTFoundations.TracyWidom.ContourRadialLog
import RMTFoundations.TracyWidom.ContourEdgePowers
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ContourRadialEnvelope
open Real
open RMTFoundations.TracyWidom.ContourRadialLog RMTFoundations.TracyWidom.ContourEdgePowers
/-- A uniform radial bound with an exponential envelope on the entire requested halfline. -/
theorem radial_envelope (N : ℕ /- [definition] -/)
    (s y : ℝ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (hd : edgeDelta N ≤ (1/2:ℝ) /- [standing] -/)
    (hs : -1 ≤ edgeDelta N*s /- [standing] -/)
    (hy : s ≤ y /- [standing] -/) :
    exp (2*radial (N:ℝ) (edgeDelta N) y) ≤
      exp (2*((2/3:ℝ)-s))*exp (-(y-s)) := by
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hp := edgeDelta_pos N hN
  have H := radial_upper (N:ℝ) (edgeDelta N) s y hn hp.le hd
    (dimension_delta_cube N hN) hs hy
  rw [←exp_add]
  apply exp_le_exp.mpr
  linarith
/-- Growing positive dimensions and every halfline endpoint satisfy the complete radial premises. -/
theorem radial_envelope_joint_probe (s : ℝ /- [definition] -/)
    (k : ℕ /- [definition] -/) :
    ∃ N : ℕ, k < N ∧ 0 < N ∧ edgeDelta N ≤ (1/2:ℝ) ∧
      -1 ≤ edgeDelta N*s ∧ ∀ y : ℝ, s ≤ y →
        exp (2*radial (N:ℝ) (edgeDelta N) y) ≤
          exp (2*((2/3:ℝ)-s))*exp (-(y-s)) := by
  obtain ⟨K,hK,h⟩ := endpoint_threshold s
  let N := max K (k+1)
  have hKN : K ≤ N := le_max_left _ _
  have hn : 0 < N := by omega
  have hp := edgeDelta_pos N hn
  have hs : -1 ≤ edgeDelta N*s := by
    have H := mul_le_mul_of_nonneg_left (neg_abs_le s) hp.le
    have HH := (h N hKN).2.2
    nlinarith
  exact ⟨N,by dsimp [N];omega,hn,(h N hKN).2.1,hs,
    fun y hy => radial_envelope N s y hn (h N hKN).2.1 hs hy⟩
end RMTFoundations.TracyWidom.ContourRadialEnvelope

#print axioms RMTFoundations.TracyWidom.ContourRadialEnvelope.radial_envelope
#print axioms RMTFoundations.TracyWidom.ContourRadialEnvelope.radial_envelope_joint_probe
