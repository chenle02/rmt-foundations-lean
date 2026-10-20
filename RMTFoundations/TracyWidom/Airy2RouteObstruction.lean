import RMTFoundations.TracyWidom.Airy2
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2
open MeasureTheory Set Filter
open scoped Topology Matrix
open RMTFoundations.Airy RMTFoundations.AiryKernel

/-- At a positive spatial point the forward diagonal-space block is strictly positive. -/
theorem forward_diagonal_space_pos
    (t r x : ℝ /- [definition] -/)
    (ht : r < t /- [standing] -/)
    (hx : 0 ≤ x /- [standing] -/) :
    0 < extendedAiryKernel t r x x := by
  rw [extendedAiryKernel_forward t r x x ht.le]
  change 0 < ∫ u, Real.exp (-(t-r)*u) * airyAiReal (x+u) * airyAiReal (x+u)
    ∂halfLineMeasure
  have hi := Ai_weighted_product_integrable (t-r) x x 1 (sub_pos.mpr ht)
  simp only [one_mul] at hi
  rw [integral_pos_iff_support_of_nonneg
    (fun u => by
      change 0 ≤ Real.exp (-(t-r)*u) * airyAiReal (x+u) * airyAiReal (x+u)
      simpa only [pow_two, mul_assoc] using
        mul_nonneg (Real.exp_nonneg (-(t-r)*u)) (sq_nonneg (airyAiReal (x+u)))) hi]
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support
      (fun u => Real.exp (-(t-r)*u) * airyAiReal (x+u) * airyAiReal (x+u)) := by
    intro u hu
    exact (mul_pos (mul_pos (Real.exp_pos _) (airyAiReal_pos_of_nonneg (add_nonneg hx hu.1.le)))
      (airyAiReal_pos_of_nonneg (add_nonneg hx hu.1.le))).ne'
  have hvol : 0 < halfLineMeasure (Ioo (0 : ℝ) 1) := by
    simp [halfLineMeasure, Measure.restrict_apply measurableSet_Ioo,
      Set.inter_eq_left.mpr (show Ioo (0 : ℝ) 1 ⊆ Ioi 0 from fun _ h => h.1), Real.volume_Ioo]
  exact lt_of_lt_of_le hvol (measure_mono hsub)

/-- The reverse diagonal-space block is nonpositive, since it is minus a weighted square. -/
theorem backward_diagonal_space_nonpos
    (t r x : ℝ /- [definition] -/)
    (ht : r < t /- [standing] -/) :
    extendedAiryKernel r t x x ≤ 0 := by
  rw [extendedAiryKernel_backward r t x x ht]
  apply neg_nonpos.mpr
  apply integral_nonneg
  intro u
  change 0 ≤ Real.exp (-(t-r)*u) * airyAiReal (x-u) * airyAiReal (x-u)
  simpa only [pow_two, mul_assoc] using
    mul_nonneg (Real.exp_nonneg (-(t-r)*u)) (sq_nonneg (airyAiReal (x-u)))

/-- The actual physical extended kernel is asymmetric at distinct times. -/
theorem extendedAiryKernel_physical_asymmetry
    (t r x : ℝ /- [definition] -/)
    (ht : r < t /- [standing] -/)
    (hx : 0 ≤ x /- [standing] -/) :
    extendedAiryKernel r t x x < extendedAiryKernel t r x x := by
  exact lt_of_le_of_lt (backward_diagonal_space_nonpos t r x ht)
    (forward_diagonal_space_pos t r x ht hx)

/-- A genuine two-time sample of the physical kernel is not a symmetric matrix.
This obstructs the Hermitian positive-contraction matrix route, not the Airy2 law. -/
theorem physical_sample_not_symmetric :
    ¬ (∀ i j : Fin 2,
      extendedAiryKernel (i.val : ℝ) (j.val : ℝ) 1 1 =
      extendedAiryKernel (j.val : ℝ) (i.val : ℝ) 1 1) := by
  intro h
  have hne := (extendedAiryKernel_physical_asymmetry 1 0 1 (by norm_num) (by norm_num)).ne
  exact hne (by simpa using h 0 1)

/-- The genuine physical two-time point sample is not Hermitian. -/
theorem physical_sample_not_hermitian :
    ¬ Matrix.IsHermitian (fun i j : Fin 2 =>
      extendedAiryKernel (i.val : ℝ) (j.val : ℝ) 1 1) := by
  intro h
  apply physical_sample_not_symmetric
  intro i j
  have he := congrFun (congrFun h.eq j) i
  change star (extendedAiryKernel (i.val : ℝ) (j.val : ℝ) 1 1) =
    extendedAiryKernel (j.val : ℝ) (i.val : ℝ) 1 1 at he
  simpa only [star_trivial] using he

/-- It consequently fails the positive semidefinite matrix hypothesis needed
by the one-time determinant order theorem. This is a point sample, not a compression. -/
theorem physical_sample_not_posSemidef :
    ¬ Matrix.PosSemidef (fun i j : Fin 2 =>
      extendedAiryKernel (i.val : ℝ) (j.val : ℝ) 1 1) := by
  intro h
  exact physical_sample_not_hermitian h.isHermitian

/-- Every binder is realized jointly on nonzero physical data and two distinct times. -/
theorem physical_signs_all_binder_joint_probe :
    airyAiReal 0 ≠ 0 ∧ (0 : ℝ) < 1 ∧ (0 : ℝ) ≤ 1 ∧
    0 < extendedAiryKernel 1 0 1 1 ∧
    extendedAiryKernel 0 1 1 1 ≤ 0 ∧
    extendedAiryKernel 0 1 1 1 ≠ extendedAiryKernel 1 0 1 1 ∧
    ¬ Matrix.IsHermitian (fun i j : Fin 2 =>
      extendedAiryKernel (i.val : ℝ) (j.val : ℝ) 1 1) ∧
    ¬ Matrix.PosSemidef (fun i j : Fin 2 =>
      extendedAiryKernel (i.val : ℝ) (j.val : ℝ) 1 1) := by
  exact ⟨airyAiReal_zero_pos.ne', by norm_num, by norm_num,
    forward_diagonal_space_pos 1 0 1 (by norm_num) (by norm_num),
    backward_diagonal_space_nonpos 1 0 1 (by norm_num),
    (extendedAiryKernel_physical_asymmetry 1 0 1 (by norm_num) (by norm_num)).ne,
    physical_sample_not_hermitian, physical_sample_not_posSemidef⟩

end RMTFoundations.TracyWidom.Airy2
#print axioms RMTFoundations.TracyWidom.Airy2.forward_diagonal_space_pos
#print axioms RMTFoundations.TracyWidom.Airy2.backward_diagonal_space_nonpos
#print axioms RMTFoundations.TracyWidom.Airy2.extendedAiryKernel_physical_asymmetry
#print axioms RMTFoundations.TracyWidom.Airy2.physical_sample_not_symmetric
#print axioms RMTFoundations.TracyWidom.Airy2.physical_signs_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2.physical_sample_not_hermitian
#print axioms RMTFoundations.TracyWidom.Airy2.physical_sample_not_posSemidef
