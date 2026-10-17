import RMTFoundations.TracyWidom.OrderOneMonotone


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set
open scoped InnerProductSpace
open RMTFoundations.Airy RMTFoundations.TWOneBounds RMTFoundations.TWOneMonotone

/-- A strict contraction cannot cancel a nonzero vector. -/
theorem add_contraction_apply_ne_zero
    {E : Type* /- [definition] -/}
    [NormedAddCommGroup E /- [standing] -/]
    [NormedSpace ℝ E /- [standing] -/]
    (B : E →L[ℝ] E /- [definition] -/)
    (hB : ‖B‖ < 1 /- [standing] -/)
    (g : E /- [definition] -/)
    (hg : g ≠ 0 /- [standing] -/) : g + B g ≠ 0 := by
  intro he
  have hb : B g = -g := by
    apply eq_neg_iff_add_eq_zero.mpr
    simpa only [add_comm] using he
  have hn := B.le_opNorm g
  rw [hb, norm_neg] at hn
  have hp : 0 < ‖g‖ := norm_pos_iff.mpr hg
  nlinarith

/-- The physical completed-square vector never vanishes at any real shift. -/
theorem airy_completed_square_ne_zero
    (s : ℝ /- [definition] -/) :
    airyBoundaryVector s + airyHankelShift s (airyBoundaryVector s) ≠ 0 :=
  add_contraction_apply_ne_zero (airyHankelShift s)
    (norm_airyHankelShift_lt_one s) (airyBoundaryVector s) (airyBoundaryVector_ne_zero s)

/-- The retained squared norm makes the existing rational-endpoint estimate strict. -/
theorem airy_boundary_positive_left
    (s : ℝ /- [definition] -/)
    (hs : s ≤ (-27/5 : ℝ) /- [standing] -/) :
    0 < airyAiReal s + inner ℝ (airyBoundaryVector s)
      (Ring.inverse (1-airyHankelShift s) (airyBoundaryVector s)) := by
  have he : (20/27 : ℝ) ≤ airyEnergy s :=
    airy_left_endpoint_energy_rational.1.trans (Airy_square_energy_antitone hs)
  have hsneg : s < 0 := by linarith
  have ht : 4 ≤ (-s)*airyEnergy s := by
    calc (4:ℝ) ≤ (-s)*(20/27) := by nlinarith only [hs]
         _ ≤ (-s)*airyEnergy s := mul_le_mul_of_nonneg_left he (by linarith)
  have hb : 0 ≤ airyAiReal s + airyEnergy s/2 :=
    scalar_oscillator_energy_sign (airyAiReal s) (deriv airyAiReal s) s hsneg ht
  have hn : 0 < ‖airyBoundaryVector s + airyHankelShift s (airyBoundaryVector s)‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (airy_completed_square_ne_zero s))
  linarith [airy_square_one_term_lower s]

/-- Both generic standing fields and the physical far-left certificate hold jointly. -/
theorem contraction_strict_all_binder_joint_probe :
    ∃ B : ℝ →L[ℝ] ℝ, ∃ g : ℝ,
    ‖B‖ < 1 ∧ g ≠ 0 ∧ B g ≠ 0 ∧ g + B g ≠ 0 ∧
    airyBoundaryVector (-6) ≠ 0 ∧ (-6:ℝ) ≤ -27/5 ∧
    0 < airyAiReal (-6) + inner ℝ (airyBoundaryVector (-6))
      (Ring.inverse (1-airyHankelShift (-6)) (airyBoundaryVector (-6))) := by
  let B : ℝ →L[ℝ] ℝ := (1/2:ℝ) • ContinuousLinearMap.id ℝ ℝ
  have hn : ‖B‖ < 1 := by norm_num [B,norm_smul,ContinuousLinearMap.norm_id]
  refine ⟨B,1,hn,by norm_num,?_,add_contraction_apply_ne_zero B hn 1 (by norm_num),
    airyBoundaryVector_ne_zero (-6),by norm_num,airy_boundary_positive_left (-6) (by norm_num)⟩
  norm_num [B]
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.add_contraction_apply_ne_zero
#print axioms RMTFoundations.TracyWidom.airy_completed_square_ne_zero
#print axioms RMTFoundations.TracyWidom.airy_boundary_positive_left
#print axioms RMTFoundations.TracyWidom.contraction_strict_all_binder_joint_probe
