import RMTFoundations.TracyWidom.HMPositiveRatioBarrier
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMPositiveRatioSharpBarrier
open RMTFoundations.TracyWidom.HMPositiveRatioBarrier
/-- The pointwise reflected-PII local-minimum barrier with its sharp finite-t
correction. This does not assume global PII or a physical positive branch. -/
theorem squaredRatio_local_min_critical_lower
    (y : ℝ → ℝ /- [definition] -/)
    (t : ℝ /- [definition] -/)
    (hy : Differentiable ℝ y /- [standing] -/)
    (hyy : HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t /- [standing] -/)
    (ht : 0 < t /- [standing] -/)
    (hp : 0 < y t /- [standing] -/)
    (hm : IsLocalMin (squaredRatio y) t /- [standing] -/)
    : 1/2-1/(8*t^3) ≤ squaredRatio y t := by
  have htne : t ≠ 0 := ht.ne'
  have hd := hm.hasDerivAt_eq_zero (squaredRatio_hasDerivAt y t hy htne)
  have hjet : 2*t*deriv y t=y t := by
    field_simp at hd
    nlinarith
  have hsecond := squaredRatio_second_deriv y t hy hyy htne
  have hstationary : deriv (deriv (squaredRatio y)) t =
      (2*(y t)^2/t)*(2*(y t)^2-t+1/(4*t^2)) := by
    rw [hsecond]
    field_simp
    nlinarith [sq_nonneg (2*t*deriv y t-y t)]
  have hn := local_min_second_deriv_nonnegative (squaredRatio y) t
    (squaredRatio_hasDerivAt y t hy htne).continuousAt hm
  rw [hstationary] at hn
  have hfactor : 0 < 2*(y t)^2/t := by positivity
  have hb : 0 ≤ 2*(y t)^2-t+1/(4*t^2) := by
    by_contra h
    have hneg : 2*(y t)^2-t+1/(4*t^2)<0 := lt_of_not_ge h
    exact (not_le_of_gt (mul_neg_of_pos_of_neg hfactor hneg)) hn
  change 1/2-1/(8*t^3) ≤ (y t)^2/t
  apply (le_div_iff₀ ht).2
  have hid : (1/2-1/(8*t^3))*t = (t-1/(4*t^2))/2 := by
    field_simp [htne]
    ring
  rw [hid]
  linarith
/-- Literal unbundled adapter for the squared-ratio expression. -/
theorem positive_local_min_square_lower
    (y : ℝ → ℝ /- [definition] -/)
    (t : ℝ /- [definition] -/)
    (hy : Differentiable ℝ y /- [standing] -/)
    (hyy : HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t /- [standing] -/)
    (ht : 0 < t /- [standing] -/)
    (hp : 0 < y t /- [standing] -/)
    (hm : IsLocalMin (squaredRatio y) t /- [standing] -/)
    : 1/2-1/(8*t^3) ≤ (y t)^2/t :=
  squaredRatio_local_min_critical_lower y t hy hyy ht hp hm
/-- The polynomial local-minimum example supplies EVERY
pointwise-PII and positivity binder by terms on the same nonconstant model. -/
theorem sharp_local_min_all_binder_joint_probe :
    ∃ (y : ℝ → ℝ) (t : ℝ), Differentiable ℝ y ∧
      HasDerivAt (deriv y) (y t*(2*(y t)^2-t)) t ∧ 0 < t ∧ 0 < y t ∧
      IsLocalMin (squaredRatio y) t ∧ 0 < deriv (deriv (squaredRatio y)) t ∧
      1/2-1/(8*t^3) ≤ squaredRatio y t ∧ 1/2-1/(8*t^3) ≤ (y t)^2/t := by
  obtain ⟨y,t,hy,hyy,ht,hp,_,hm,_,_,h2,_,_⟩ := local_calculus_all_binder_joint_probe
  have ht0 : 0 < t := by linarith
  exact ⟨y,t,hy,hyy,ht0,hp,hm,h2,
    squaredRatio_local_min_critical_lower y t hy hyy ht0 hp hm,
    positive_local_min_square_lower y t hy hyy ht0 hp hm⟩
end RMTFoundations.TracyWidom.HMPositiveRatioSharpBarrier
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioSharpBarrier.squaredRatio_local_min_critical_lower
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioSharpBarrier.positive_local_min_square_lower
#print axioms RMTFoundations.TracyWidom.HMPositiveRatioSharpBarrier.sharp_local_min_all_binder_joint_probe
