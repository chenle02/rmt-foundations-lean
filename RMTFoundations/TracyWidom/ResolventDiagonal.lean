import RMTFoundations.TracyWidom.ResolventCoordinates
import RMTFoundations.TracyWidom.AiryBoundaryContinuity



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.ResolventDiagonal

open MeasureTheory InnerProductSpace
open RMTFoundations.Airy RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.AiryBoundaryContinuity

/-- The physical zero-endpoint Airy-square kernel row as an L2 vector. -/
noncomputable def boundaryKernelRow
    (s : ℝ) -- [definition]
    : Lp ℝ 2 halfLineMeasure := airyHankelShift s (airyBoundaryVector s)

/-- The canonical inverse of the genuine Hankel square commutes with Hankel. -/
theorem airyKernelResolvent_commutes_hankel
    (s : ℝ) -- [definition]
    (x : Lp ℝ 2 halfLineMeasure) -- [definition]
    : Ring.inverse (1 - airyKernelShift s) (airyHankelShift s x) =
      airyHankelShift s (Ring.inverse (1 - airyKernelShift s) x) := by
  have hr := congrArg (airyHankelShift s)
    (contraction_ringInverse_right (airyKernelShift s)
      (norm_airyKernelShift_lt_one s) x)
  simp only [map_sub, airyKernelShift, ContinuousLinearMap.comp_apply] at hr
  have hl := contraction_ringInverse_left (airyKernelShift s)
    (norm_airyKernelShift_lt_one s)
    (airyHankelShift s (Ring.inverse (1 - airyKernelShift s) x))
  simp only [airyKernelShift, ContinuousLinearMap.comp_apply] at hl
  rw [hr] at hl
  exact hl

/-- The canonical diagonal u is precisely the scalar diagonal-resolvent formula. -/
theorem resolventU_eq_scalar_diagonal
    (s : ℝ) -- [definition]
    : resolventU s = airyEnergy s + inner ℝ (boundaryKernelRow s)
      (Ring.inverse (1 - airyKernelShift s) (boundaryKernelRow s)) := by
  let T := Ring.inverse (1 - airyKernelShift s)
  let a := airyBoundaryVector s
  have hr := contraction_ringInverse_right (airyKernelShift s)
    (norm_airyKernelShift_lt_one s) a
  have he : T a = a + airyKernelShift s (T a) := by
    change T a - airyKernelShift s (T a) = a at hr
    exact (sub_eq_iff_eq_add).mp hr
  change inner ℝ a (T a) = _
  rw [he, inner_add_right]
  have hs := (isSelfAdjoint_airyHankelShift s).isSymmetric a (airyHankelShift s (T a))
  have hc := airyKernelResolvent_commutes_hankel s a
  change T (airyHankelShift s a) = airyHankelShift s (T a) at hc
  rw [airyBoundaryVector_inner_self]
  change airyEnergy s + inner ℝ a (airyHankelShift s (airyHankelShift s (T a))) = _
  apply congrArg (fun z : ℝ => airyEnergy s + z)
  calc
    inner ℝ a (airyHankelShift s (airyHankelShift s (T a))) =
        inner ℝ (airyHankelShift s a) (airyHankelShift s (T a)) := hs.symm
    _ = inner ℝ (airyHankelShift s a) (T (airyHankelShift s a)) :=
      congrArg (inner ℝ (airyHankelShift s a)) hc.symm

/-- The canonical endpoint response equals the row-based scalar representative. -/
theorem resolventQ_eq_scalar_endpoint
    (s : ℝ) -- [definition]
    : resolventQ s = airyAiReal s + inner ℝ (boundaryKernelRow s)
      (Ring.inverse (1 - airyKernelShift s) (airyBoundaryVector s)) := by
  unfold resolventQ boundaryKernelRow
  exact congrArg (fun z : ℝ => airyAiReal s + z)
    ((isSelfAdjoint_airyHankelShift s).isSymmetric (airyBoundaryVector s)
      (Ring.inverse (1 - airyKernelShift s) (airyBoundaryVector s))).symm

/-- Every object occurs jointly in the genuine positive shift-zero model. -/
theorem scalar_diagonal_all_binder_joint_probe
    : airyBoundaryVector 0 ≠ 0 ∧ 0 < airyEnergy 0 ∧ 0 < resolventU 0 ∧
      resolventU 0 = airyEnergy 0 + inner ℝ (boundaryKernelRow 0)
        (Ring.inverse (1 - airyKernelShift 0) (boundaryKernelRow 0)) ∧
      resolventQ 0 = airyAiReal 0 + inner ℝ (boundaryKernelRow 0)
        (Ring.inverse (1 - airyKernelShift 0) (airyBoundaryVector 0)) ∧
      (∀ x, Ring.inverse (1 - airyKernelShift 0) (airyHankelShift 0 x) =
        airyHankelShift 0 (Ring.inverse (1 - airyKernelShift 0) x)) := by
  exact ⟨airyBoundaryVector_ne_zero 0, airyEnergy_pos 0,
    airy_inverse_square_boundary_positive 0, resolventU_eq_scalar_diagonal 0,
    resolventQ_eq_scalar_endpoint 0, airyKernelResolvent_commutes_hankel 0⟩

end RMTFoundations.TracyWidom.ResolventDiagonal

#print axioms RMTFoundations.TracyWidom.ResolventDiagonal.boundaryKernelRow
#print axioms RMTFoundations.TracyWidom.ResolventDiagonal.airyKernelResolvent_commutes_hankel
#print axioms RMTFoundations.TracyWidom.ResolventDiagonal.resolventU_eq_scalar_diagonal
#print axioms RMTFoundations.TracyWidom.ResolventDiagonal.resolventQ_eq_scalar_endpoint
#print axioms RMTFoundations.TracyWidom.ResolventDiagonal.scalar_diagonal_all_binder_joint_probe
