import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ContourRadialLog
open Set Real
noncomputable def correction (d : ℝ /- [definition] -/) : ℝ :=
  -log (1-d)-d-d^2/2-(2/3:ℝ)*d^3
lemma correction_hasDerivAt (d : ℝ /- [definition] -/)
    (hd : d < 1 /- [standing] -/) :
    HasDerivAt correction (1/(1-d)-1-d-2*d^2) d := by
  have hn : 1-d ≠ 0 := ne_of_gt (by linarith)
  have H := (((((hasDerivAt_const d 1).sub (hasDerivAt_id d)).log hn).neg.sub
    (hasDerivAt_id d)).sub ((hasDerivAt_pow 2 d).div_const 2)).sub
      ((hasDerivAt_pow 3 d).const_mul (2/3:ℝ))
  convert H using 1 <;> first | rfl | (dsimp [correction]; ring)
/-- Cubic radial correction on the honest positive-radius range. -/
theorem radial_log_bound (d : ℝ /- [definition] -/)
    (hd0 : 0 ≤ d /- [standing] -/)
    (hd1 : d ≤ (1/2:ℝ) /- [standing] -/) :
    -log (1-d)-d-d^2/2 ≤ (2/3:ℝ)*d^3 := by
  have hc : ContinuousOn correction (Icc 0 (1/2:ℝ)) := by
    intro t ht
    exact (correction_hasDerivAt t (by linarith [ht.2])).continuousAt.continuousWithinAt
  have hm : AntitoneOn correction (Icc 0 (1/2:ℝ)) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc
    · intro t ht
      have hi : t ∈ Ioo 0 (1/2:ℝ) := by simpa only [interior_Icc] using ht
      exact (correction_hasDerivAt t (by linarith [hi.2])).differentiableAt.differentiableWithinAt
    intro t ht
    have hi : t ∈ Ioo 0 (1/2:ℝ) := by simpa only [interior_Icc] using ht
    rw [(correction_hasDerivAt t (by linarith [hi.2])).deriv]
    have hp : 0 < 1-t := by linarith [hi.2]
    have hsq := sq_nonneg t
    have hmul : 0 ≤ t^2*(1-2*t) := mul_nonneg hsq (by linarith [hi.2])
    have H : 1/(1-t) ≤ 1+t+2*t^2 := by
      apply (div_le_iff₀ hp).mpr
      nlinarith
    linarith
  have H := hm ⟨by norm_num,by norm_num⟩ ⟨hd0,hd1⟩ hd0
  norm_num [correction] at H
  linarith
/-- Strictly interior, nonzero radius parameters satisfy all binders jointly. -/
theorem radial_joint_probe (k : ℕ /- [definition] -/) :
    ∃ d : ℝ, 0 < d ∧ d ≤ (1/2:ℝ) ∧
      -log (1-d)-d-d^2/2 ≤ (2/3:ℝ)*d^3 := by
  let d : ℝ := 1/((k:ℝ)+2)
  have hp : 0 < (k:ℝ)+2 := by positivity
  have hd0 : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ (1/2:ℝ) := by
    dsimp [d]
    apply (div_le_iff₀ hp).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  exact ⟨d,hd0,hd1,radial_log_bound d hd0.le hd1⟩
noncomputable def radial (N d y : ℝ /- [definition] -/) : ℝ :=
  N*(-log (1-d)-d-d^2/2-y*d^3-y^2*d^4/4)
/-- The contour exponent decays uniformly on the ENTIRE requested half-line. -/
theorem radial_upper (N d s y : ℝ /- [definition] -/)
    (hN : 0 ≤ N /- [standing] -/)
    (hd0 : 0 ≤ d /- [standing] -/)
    (hd1 : d ≤ (1/2:ℝ) /- [standing] -/)
    (hprod : N*d^3=1 /- [standing] -/)
    (hds : -1 ≤ d*s /- [standing] -/)
    (hsy : s ≤ y /- [standing] -/) :
    radial N d y ≤ (2/3-s)-(1/2:ℝ)*(y-s) := by
  have hlog := mul_le_mul_of_nonneg_left (radial_log_bound d hd0 hd1) hN
  have hquartic : 0 ≤ N*s^2*d^4/4 := by positivity
  have hsbound : radial N d s ≤ 2/3-s := by
    calc
      _ = N*(-log (1-d)-d-d^2/2)-s*(N*d^3)-N*s^2*d^4/4 := by dsimp [radial]; ring
      _ ≤ N*((2/3:ℝ)*d^3)-s*(N*d^3) := by linarith
      _ = 2/3-s := by
        rw [show N*((2/3:ℝ)*d^3)=(2/3:ℝ)*(N*d^3) by ring,hprod]
        ring
  have hd4 : N*d^4=d := by
    calc
      _ = (N*d^3)*d := by ring
      _ = d := by rw [hprod,one_mul]
  have hyd := mul_le_mul_of_nonneg_left hsy hd0
  have hfloor : (1/2:ℝ) ≤ 1+d*(y+s)/4 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hfloor (sub_nonneg.mpr hsy)
  calc
    _ = radial N d s-(y-s)*(N*d^3)-(y^2-s^2)*(N*d^4)/4 := by dsimp [radial]; ring
    _ = radial N d s-(y-s)*(1+d*(y+s)/4) := by rw [hprod,hd4]; ring
    _ ≤ radial N d s-(1/2:ℝ)*(y-s) := by nlinarith
    _ ≤ (2/3-s)-(1/2:ℝ)*(y-s) := sub_le_sub_right hsbound _
/-- Genuine nonzero contour parameters satisfy all seven analytic binders jointly. -/
theorem radial_upper_joint_probe (k : ℕ /- [definition] -/) :
    ∃ N d : ℝ, 0 < N ∧ 0 < d ∧ d ≤ (1/2:ℝ) ∧ N*d^3=1 ∧
      -1 ≤ d*(-1) ∧ ∀ y : ℝ, -1 ≤ y →
        radial N d y ≤ (2/3-(-1))-(1/2:ℝ)*(y-(-1)) := by
  let d : ℝ := 1/((k:ℝ)+2)
  let N : ℝ := ((k:ℝ)+2)^3
  have ha : 0 < (k:ℝ)+2 := by positivity
  have hd0 : 0 < d := by dsimp [d]; positivity
  have hd1 : d ≤ (1/2:ℝ) := by
    dsimp [d]
    apply (div_le_iff₀ ha).mpr
    nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  have hN : 0 < N := by dsimp [N]; positivity
  have hp : N*d^3=1 := by dsimp [N,d]; field_simp
  have hs : -1 ≤ d*(-1) := by linarith
  exact ⟨N,d,hN,hd0,hd1,hp,hs,fun y hy => radial_upper N d (-1) y hN.le hd0.le hd1 hp hs hy⟩
end RMTFoundations.TracyWidom.ContourRadialLog

#print axioms RMTFoundations.TracyWidom.ContourRadialLog.correction
#print axioms RMTFoundations.TracyWidom.ContourRadialLog.correction_hasDerivAt
#print axioms RMTFoundations.TracyWidom.ContourRadialLog.radial_log_bound
#print axioms RMTFoundations.TracyWidom.ContourRadialLog.radial_joint_probe
#print axioms RMTFoundations.TracyWidom.ContourRadialLog.radial
#print axioms RMTFoundations.TracyWidom.ContourRadialLog.radial_upper
#print axioms RMTFoundations.TracyWidom.ContourRadialLog.radial_upper_joint_probe
