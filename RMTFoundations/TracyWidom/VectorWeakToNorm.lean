import Mathlib



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom

open MeasureTheory

/-- A continuous Hilbert-valued weak derivative identifies the original curve
with its Bochner primitive. No prior norm continuity of the curve is assumed.
This generic pilot does not identify a physical Airy row or its derivative. -/
theorem vector_eq_primitive_of_pairings
    {E : Type*} -- [definition]
    [NormedAddCommGroup E] -- [standing]
    [InnerProductSpace ℝ E] -- [standing]
    [CompleteSpace E] -- [standing]
    (f d : ℝ → E) -- [definition]
    (hd : Continuous d) -- [standing]
    (hweak : ∀ (v : E) (t : ℝ), HasDerivAt (fun r => inner ℝ v (f r))
      (inner ℝ v (d t)) t) -- [standing]
    (s : ℝ) -- [definition]
    : f s = (∫ u in (0 : ℝ)..s, d u) + f 0 := by
  let J : ℝ → E := fun t => ∫ u in (0 : ℝ)..t, d u
  have hJ (t : ℝ) : HasDerivAt J (d t) t :=
    intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable 0 t)
      hd.stronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt
  have hp (v : E) (t : ℝ) : HasDerivAt (fun r => inner ℝ v (J r))
      (inner ℝ v (d t)) t := by
    convert! (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt t (hJ t) using 1 <;>
      simp [Function.comp_def]
  have hz (v : E) (t : ℝ) : HasDerivAt
      (fun r => inner ℝ v (f r) - inner ℝ v (J r)) 0 t := by
    simpa using (hweak v t).fun_sub (hp v t)
  change f s = J s + f 0
  apply ext_inner_left ℝ
  intro v
  have hc := is_const_of_deriv_eq_zero
    (fun r => (hz v r).differentiableAt) (fun r => (hz v r).deriv) s 0
  simp only [J, intervalIntegral.integral_same, inner_zero_right, sub_zero] at hc
  simp only [inner_add_right]
  linarith

/-- Scalar-pairing derivatives and a continuous derivative family imply the
genuine norm derivative of a Hilbert-valued curve. Completeness is used for
the Bochner primitive, not assumed through a hidden bundle. -/
theorem hasDerivAt_vector_of_pairings
    {E : Type*} -- [definition]
    [NormedAddCommGroup E] -- [standing]
    [InnerProductSpace ℝ E] -- [standing]
    [CompleteSpace E] -- [standing]
    (f d : ℝ → E) -- [definition]
    (hd : Continuous d) -- [standing]
    (hweak : ∀ (v : E) (t : ℝ), HasDerivAt (fun r => inner ℝ v (f r))
      (inner ℝ v (d t)) t) -- [standing]
    (s : ℝ) -- [definition]
    : HasDerivAt f (d s) s := by
  have hf : f = fun t => (∫ u in (0 : ℝ)..t, d u) + f 0 :=
    funext (fun t => vector_eq_primitive_of_pairings f d hd hweak t)
  rw [hf]
  exact (intervalIntegral.integral_hasDerivAt_right (hd.intervalIntegrable 0 s)
    hd.stronglyMeasurable.stronglyMeasurableAtFilter hd.continuousAt).add_const (f 0)

/-- Every binder is satisfied simultaneously on the nonzero real Hilbert
space by the nonconstant affine curve `f(t)=t+1` and nonzero derivative `d=1`.
The primitive identity and upgraded derivative are consequences, not premises. -/
theorem vector_pairings_joint_probe
    : let f : ℝ → ℝ := fun t => t + 1
      let d : ℝ → ℝ := fun _ => 1
      Continuous d ∧
        (∀ (v t : ℝ), HasDerivAt (fun r => inner ℝ v (f r))
          (inner ℝ v (d t)) t) ∧
        f 0 ≠ 0 ∧ f 1 ≠ 0 ∧ d 1 ≠ 0 ∧
        f 1 = (∫ u in (0 : ℝ)..1, d u) + f 0 ∧
        HasDerivAt f (d 1) 1 := by
  dsimp
  have hd : Continuous (fun _ : ℝ => (1 : ℝ)) := continuous_const
  have hw (v t : ℝ) : HasDerivAt (fun r => inner ℝ v (r + 1))
      (inner ℝ v (1 : ℝ)) t := by
    convert! ((hasDerivAt_id t).add_const 1).mul_const v using 1 <;>
      simp [Real.inner_apply, mul_comm]
  refine ⟨hd, hw, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · exact vector_eq_primitive_of_pairings (fun t : ℝ => t + 1)
      (fun _ : ℝ => 1) hd hw 1
  · exact hasDerivAt_vector_of_pairings (fun t : ℝ => t + 1)
      (fun _ : ℝ => 1) hd hw 1

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.vector_eq_primitive_of_pairings
#print axioms RMTFoundations.TracyWidom.hasDerivAt_vector_of_pairings
#print axioms RMTFoundations.TracyWidom.vector_pairings_joint_probe
