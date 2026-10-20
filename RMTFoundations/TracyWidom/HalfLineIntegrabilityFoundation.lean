import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HalfLineIntegrabilityFoundation
open Set Filter MeasureTheory Real
open scoped Topology
/-- Unit mass cannot be integrable on an infinite real right half-line. -/
lemma const_tail_not_integrable (s : ℝ /- [definition] -/) :
    ¬ IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi s) := by
  simp [IntegrableOn, integrable_const_iff_isFiniteMeasure, isFiniteMeasure_iff]

/-- Eventual unit lower norm rules out an L1 tail, without continuity assumptions. -/
theorem not_integrable_of_eventually_one_le_norm
    (f : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hf : ∀ᶠ x : ℝ in atTop, 1 ≤ ‖f x‖ /- [standing] -/) :
    ¬ IntegrableOn f (Ioi s) := by
  intro hi
  obtain ⟨R,hR⟩ := eventually_atTop.1 hf
  let T := max s R
  have htail : IntegrableOn f (Ioi T) := hi.mono_set (by
    intro x hx
    change T < x at hx
    exact lt_of_le_of_lt (show s ≤ T from le_max_left s R) hx)
  have hunit : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi T) := by
    apply htail.norm.mono' (by fun_prop)
    exact ae_restrict_of_forall_mem measurableSet_Ioi (by
      intro x hx
      simp only [norm_one]
      change T < x at hx
      exact hR x ((show R ≤ T from le_max_right s R).trans hx.le))
  exact const_tail_not_integrable T hunit

/-- A function tending to positive infinity admits no integrable pointwise
majorant on a full half-line, even after an arbitrary fixed amplitude scaling. -/
theorem no_integrable_envelope
    (q : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hq : Tendsto q atTop atTop /- [standing] -/) :
    ¬ ∃ (η : ℝ) (b : ℝ → ℝ), IntegrableOn b (Ioi s) ∧
      ∀ x, s ≤ x → |q x| ≤ η*b x := by
  rintro ⟨η,b,hb,hbound⟩
  have hnorm : ∀ᶠ x : ℝ in atTop, 1 ≤ ‖η*b x‖ := by
    filter_upwards [hq.eventually_ge_atTop 1,eventually_ge_atTop s] with x hx hs
    exact (hx.trans (le_abs_self _)).trans ((hbound x hs).trans (le_abs_self _))
  exact not_integrable_of_eventually_one_le_norm (fun x => η*b x) s
    hnorm (hb.const_mul η)

/-- A nonconstant positive quadratic jointly realizes the actual unit-lower-norm
premise on an infinite positive tail. All hypotheses of the obstruction hold on this example. -/
theorem halfline_joint_probe :
    ∃ f : ℝ → ℝ, f 1 ≠ f 2 ∧
      (∀ᶠ x : ℝ in atTop, 1 ≤ ‖f x‖) ∧ ¬ IntegrableOn f (Ioi 1) := by
  let f : ℝ → ℝ := fun x => x^2+1
  have hf : ∀ᶠ x : ℝ in atTop, 1 ≤ ‖f x‖ := by
    apply Filter.Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (by dsimp [f]; positivity)]
    dsimp [f]; nlinarith [sq_nonneg x]
  exact ⟨f,by norm_num [f],hf,not_integrable_of_eventually_one_le_norm f 1 hf⟩
/-- The envelope-obstruction binders are satisfiable for the identity function
at a strictly positive endpoint; the impossible envelope is in the conclusion. -/
theorem divergence_joint_probe :
    ∃ q : ℝ → ℝ, q 1 ≠ q 2 ∧ Tendsto q atTop atTop ∧
      ¬ ∃ (η : ℝ) (b : ℝ → ℝ), IntegrableOn b (Ioi 1) ∧
        ∀ x, 1 ≤ x → |q x| ≤ η*b x := by
  exact ⟨id,by norm_num,tendsto_id,no_integrable_envelope id 1 tendsto_id⟩
end RMTFoundations.TracyWidom.HalfLineIntegrabilityFoundation

#print axioms RMTFoundations.TracyWidom.HalfLineIntegrabilityFoundation.const_tail_not_integrable
#print axioms RMTFoundations.TracyWidom.HalfLineIntegrabilityFoundation.not_integrable_of_eventually_one_le_norm
#print axioms RMTFoundations.TracyWidom.HalfLineIntegrabilityFoundation.no_integrable_envelope
#print axioms RMTFoundations.TracyWidom.HalfLineIntegrabilityFoundation.halfline_joint_probe
#print axioms RMTFoundations.TracyWidom.HalfLineIntegrabilityFoundation.divergence_joint_probe
