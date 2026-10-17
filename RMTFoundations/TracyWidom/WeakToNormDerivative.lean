import Mathlib



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom

open MeasureTheory
open scoped InnerProductSpace

/-- A continuous operator-valued weak derivative determines a genuine norm
 derivative. No norm continuity of K is assumed. This is generic calculus;
 the actual Airy derivative family must still be proved norm continuous. -/
theorem hasDerivAt_operator_of_pairings
    {E : Type*} -- [definition]
    [NormedAddCommGroup E] -- [standing]
    [InnerProductSpace ℝ E] -- [standing]
    [CompleteSpace E] -- [standing]
    (K D : ℝ → E →L[ℝ] E) -- [definition]
    (hD : Continuous D) -- [standing]
    (hweak : ∀ (x y : E) (s : ℝ),
      HasDerivAt (fun t => inner ℝ x (K t y)) (inner ℝ x (D s y)) s) -- [standing]
    (s : ℝ) -- [definition]
    : HasDerivAt K (D s) s := by
  let J : ℝ → E →L[ℝ] E := fun t => ∫ u in (0 : ℝ)..t, D u
  have hJ (t : ℝ) : HasDerivAt J (D t) t :=
    intervalIntegral.integral_hasDerivAt_right (hD.intervalIntegrable 0 t)
      hD.stronglyMeasurable.stronglyMeasurableAtFilter hD.continuousAt
  have hp (x y : E) (t : ℝ) :
      HasDerivAt (fun r => inner ℝ x (J r y)) (inner ℝ x (D t y)) t := by
    have hjy := (hJ t).clm_apply (hasDerivAt_const t y)
    convert! (innerSL ℝ x).hasFDerivAt.comp_hasDerivAt t hjy using 1 <;>
      simp [Function.comp_def]
  have hz (x y : E) (t : ℝ) :
      HasDerivAt (fun r => inner ℝ x (K r y) - inner ℝ x (J r y)) 0 t := by
    simpa using (hweak x y t).fun_sub (hp x y t)
  have he (t : ℝ) : K t = J t + K 0 := by
    ext y
    apply ext_inner_left ℝ
    intro x
    have hc := is_const_of_deriv_eq_zero
      (fun r => (hz x y r).differentiableAt) (fun r => (hz x y r).deriv) t 0
    simp only [J, intervalIntegral.integral_same, ContinuousLinearMap.zero_apply,
      inner_zero_right, sub_zero] at hc
    simp only [ContinuousLinearMap.add_apply, inner_add_right]
    linarith
  have hf : K = fun t => J t + K 0 := funext he
  rw [hf]
  exact (hJ s).add_const (K 0)

/-- Every binder is realized simultaneously on the nonzero real Hilbert space.
K is a nonconstant scalar multiple of the identity and D is nonzero. -/
theorem operator_pairings_joint_probe :
    let K : ℝ → ℝ →L[ℝ] ℝ := fun t => t • 1
    let D : ℝ → ℝ →L[ℝ] ℝ := fun _ => 1
    Continuous D ∧
      (∀ (x y s : ℝ), HasDerivAt (fun t => inner ℝ x (K t y))
        (inner ℝ x (D s y)) s) ∧
      K 1 ≠ 0 ∧ D 1 ≠ 0 ∧ HasDerivAt K (D 1) 1 := by
  dsimp
  have hd : Continuous (fun _ : ℝ => (1 : ℝ →L[ℝ] ℝ)) := continuous_const
  have hw (x y s : ℝ) : HasDerivAt
      (fun t => inner ℝ x ((t • (1 : ℝ →L[ℝ] ℝ)) y))
      (inner ℝ x ((1 : ℝ →L[ℝ] ℝ) y)) s := by
    convert! (hasDerivAt_id s).mul_const (y * x) using 1 <;>
      simp [mul_assoc, mul_comm, mul_left_comm]
  have hn : (1 : ℝ →L[ℝ] ℝ) ≠ 0 := by
    intro h
    have hx := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) h
    norm_num at hx
  refine ⟨hd, hw, ?_, hn, ?_⟩
  · simpa using hn
  · exact hasDerivAt_operator_of_pairings _ _ hd hw 1

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.hasDerivAt_operator_of_pairings
#print axioms RMTFoundations.TracyWidom.operator_pairings_joint_probe
