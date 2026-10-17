import Mathlib



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom

/-- Generic calculus; the physical Airy operator derivative is a separate obligation. -/
theorem hasDerivAt_inverse_one_sub
    {A : Type*} -- [definition]
    [NormedRing A] -- [standing]
    [NormedAlgebra ℝ A] -- [standing]
    [CompleteSpace A] -- [standing]
    (K : ℝ → A) -- [definition]
    (K' : A) -- [definition]
    (s : ℝ) -- [definition]
    (hK : HasDerivAt K K' s) -- [standing]
    (hu : IsUnit (1 - K s)) -- [standing]
    : HasDerivAt (fun t => Ring.inverse (1 - K t))
        (Ring.inverse (1 - K s) * K' * Ring.inverse (1 - K s)) s := by
  rcases hu with ⟨u, hu⟩
  have hD : HasDerivAt (fun t => 1 - K t) (-K') s := by
    simpa using hK.const_sub 1
  have hI := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hI
  have h := hI.comp_hasDerivAt s hD
  simpa only [Function.comp_def, neg_apply, ContinuousLinearMap.mulLeftRight_apply,
    mul_neg, neg_mul, neg_neg, ← Ring.inverse_unit u, hu] using h

/-- A resolvent times a differentiable algebra-valued source. -/
theorem hasDerivAt_resolvent_mul
    {A : Type*} -- [definition]
    [NormedRing A] -- [standing]
    [NormedAlgebra ℝ A] -- [standing]
    [CompleteSpace A] -- [standing]
    (K a : ℝ → A) -- [definition]
    (K' a' : A) -- [definition]
    (s : ℝ) -- [definition]
    (hK : HasDerivAt K K' s) -- [standing]
    (ha : HasDerivAt a a' s) -- [standing]
    (hu : IsUnit (1 - K s)) -- [standing]
    : HasDerivAt (fun t => Ring.inverse (1 - K t) * a t)
        ((Ring.inverse (1 - K s) * K' * Ring.inverse (1 - K s)) * a s +
          Ring.inverse (1 - K s) * a') s := by
  exact (hasDerivAt_inverse_one_sub K K' s hK hu).mul ha

/-- Joint nondegenerate instance for every data and standing binder above. -/
theorem resolvent_differentiation_joint_probe :
    let K : ℝ → ℝ := fun t => t
    let a : ℝ → ℝ := fun t => t * t
    let s : ℝ := 1 / 2
    HasDerivAt K 1 s ∧ HasDerivAt a 1 s ∧ IsUnit (1 - K s) ∧
      K s ≠ 0 ∧ a s ≠ 0 ∧ Ring.inverse (1 - K s) = 2 ∧
      HasDerivAt (fun t => Ring.inverse (1 - K t)) 4 s ∧
      HasDerivAt (fun t => Ring.inverse (1 - K t) * a t) 3 s := by
  dsimp
  have hk : HasDerivAt (fun t : ℝ => t) 1 (1 / 2) := hasDerivAt_id (1 / 2)
  have ha : HasDerivAt (fun t : ℝ => t * t) 1 (1 / 2) := by
    convert! hk.mul hk using 1 <;> norm_num
  have hu : IsUnit (1 - (1 / 2 : ℝ)) := isUnit_iff_ne_zero.mpr (by norm_num)
  have hi : Ring.inverse (1 - (1 / 2 : ℝ)) = 2 := by norm_num
  refine ⟨hk, ha, hu, by norm_num, by norm_num, hi, ?_, ?_⟩
  · convert! hasDerivAt_inverse_one_sub (fun t : ℝ => t) 1 (1 / 2) hk hu using 1 <;>
      norm_num [hi]
  · convert! hasDerivAt_resolvent_mul (fun t : ℝ => t)
      (fun t : ℝ => t * t) 1 1 (1 / 2) hk ha hu using 1 <;> norm_num [hi]

/-- Applying a differentiable resolvent to a differentiable Banach-space source. -/
theorem hasDerivAt_resolvent_apply
    {E : Type*} -- [definition]
    [NormedAddCommGroup E] -- [standing]
    [NormedSpace ℝ E] -- [standing]
    [CompleteSpace E] -- [standing]
    (K : ℝ → E →L[ℝ] E) -- [definition]
    (a : ℝ → E) -- [definition]
    (K' : E →L[ℝ] E) -- [definition]
    (a' : E) -- [definition]
    (s : ℝ) -- [definition]
    (hK : HasDerivAt K K' s) -- [standing]
    (ha : HasDerivAt a a' s) -- [standing]
    (hu : IsUnit (1 - K s)) -- [standing]
    : HasDerivAt (fun t => (Ring.inverse (1 - K t)) (a t))
        ((Ring.inverse (1 - K s) * K' * Ring.inverse (1 - K s)) (a s) +
          (Ring.inverse (1 - K s)) a') s := by
  exact (hasDerivAt_inverse_one_sub K K' s hK hu).clm_apply ha

/-- All action binders realized by nonzero scalar multiples of the identity on the real line. -/
theorem resolvent_application_joint_probe :
    let K : ℝ → ℝ →L[ℝ] ℝ := fun t => t • 1
    let a : ℝ → ℝ := fun t => t * t
    let s : ℝ := 1 / 2
    HasDerivAt K 1 s ∧ HasDerivAt a 1 s ∧ IsUnit (1 - K s) ∧
      K s ≠ 0 ∧ a s ≠ 0 ∧ Ring.inverse (1 - K s) = (2 : ℝ) • 1 ∧
      HasDerivAt (fun t => (Ring.inverse (1 - K t)) (a t)) 3 s := by
  dsimp
  have hid : HasDerivAt (fun t : ℝ => t) 1 (1 / 2) := hasDerivAt_id (1 / 2)
  have hk : HasDerivAt (fun t : ℝ => t • (1 : ℝ →L[ℝ] ℝ)) 1 (1 / 2) := by
    simpa using hid.smul_const (1 : ℝ →L[ℝ] ℝ)
  have ha : HasDerivAt (fun t : ℝ => t * t) 1 (1 / 2) := by
    convert! hid.mul hid using 1 <;> norm_num
  let u : (ℝ →L[ℝ] ℝ)ˣ := {
    val := (1 / 2 : ℝ) • 1
    inv := (2 : ℝ) • 1
    val_inv := by ext <;> simp <;> ring
    inv_val := by ext <;> simp <;> ring }
  have huval : (u : ℝ →L[ℝ] ℝ) = 1 - (1 / 2 : ℝ) • 1 := by
    ext
    simp [u]
    ring
  have hu : IsUnit (1 - (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) := ⟨u, huval⟩
  have hi : Ring.inverse (1 - (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ)) = (2 : ℝ) • 1 := by
    rw [← huval, Ring.inverse_unit]
    rfl
  have hne : (1 / 2 : ℝ) • (1 : ℝ →L[ℝ] ℝ) ≠ 0 := by
    intro h
    have hx := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) h
    norm_num at hx
  refine ⟨hk, ha, hu, hne, by norm_num, hi, ?_⟩
  convert! hasDerivAt_resolvent_apply (fun t : ℝ => t • (1 : ℝ →L[ℝ] ℝ))
      (fun t : ℝ => t * t) 1 1 (1 / 2) hk ha hu using 1 <;> norm_num [hi]

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.hasDerivAt_inverse_one_sub
#print axioms RMTFoundations.TracyWidom.hasDerivAt_resolvent_mul
#print axioms RMTFoundations.TracyWidom.resolvent_differentiation_joint_probe
#print axioms RMTFoundations.TracyWidom.hasDerivAt_resolvent_apply
#print axioms RMTFoundations.TracyWidom.resolvent_application_joint_probe
