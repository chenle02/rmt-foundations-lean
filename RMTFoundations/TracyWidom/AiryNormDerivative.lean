import RMTFoundations.TracyWidom.AiryBoundaryContinuity
import RMTFoundations.TracyWidom.WeakToNormDerivative
import RMTFoundations.TracyWidom.ResolventDifferentiation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.AiryNormDerivative

open MeasureTheory
open scoped InnerProductSpace
open RMTFoundations.Airy RMTFoundations.TWOneBounds RMTFoundations.AiryDistribution
open RMTFoundations.TracyWidom.AiryBoundaryContinuity RMTFoundations.TracyWidom

/-- The genuine shifted Airy square has the rank-one derivative in operator norm.
This upgrades the weak pairing derivative using actual row continuity. -/
theorem hasDerivAt_airyKernelShift_norm
    (s : ℝ) -- [definition]
    : HasDerivAt airyKernelShift
        (-InnerProductSpace.rankOne ℝ (airyBoundaryVector s) (airyBoundaryVector s)) s := by
  apply hasDerivAt_operator_of_pairings airyKernelShift
    (fun t => -InnerProductSpace.rankOne ℝ (airyBoundaryVector t) (airyBoundaryVector t))
    airyBoundaryRankOne_continuous
  intro x y t
  convert! hasDerivAt_airyKernelShift_pairing x y t using 1 <;>
    simp [InnerProductSpace.rankOne_apply, real_inner_smul_right, real_inner_comm,
      mul_comm, mul_left_comm, mul_assoc]

/-- The inverse regularity uses the genuine strict contraction. -/
theorem airyKernelShift_one_sub_isUnit
    (s : ℝ) -- [definition]
    : IsUnit (1 - airyKernelShift s) := by
  exact ⟨Units.oneSub (airyKernelShift s) (norm_airyKernelShift_lt_one s), rfl⟩

/-- Actual operator-norm derivative of the canonical Airy square resolvent.
No differentiability or inverse assumptions are added to the physical adapter. -/
theorem hasDerivAt_airyKernelResolvent_norm
    (s : ℝ) -- [definition]
    : HasDerivAt (fun t => Ring.inverse (1 - airyKernelShift t))
        (Ring.inverse (1 - airyKernelShift s) *
          (-InnerProductSpace.rankOne ℝ (airyBoundaryVector s) (airyBoundaryVector s)) *
          Ring.inverse (1 - airyKernelShift s)) s := by
  exact hasDerivAt_inverse_one_sub airyKernelShift
    (-InnerProductSpace.rankOne ℝ (airyBoundaryVector s) (airyBoundaryVector s)) s
    (hasDerivAt_airyKernelShift_norm s) (airyKernelShift_one_sub_isUnit s)

/-- All adapter binders occur in one nonzero actual Airy model at zero. -/
theorem airy_norm_derivative_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧ 0 < airyEnergy 0 ∧ ‖airyKernelShift 0‖ < 1 ∧
      IsUnit (1 - airyKernelShift 0) ∧
      HasDerivAt airyKernelShift
        (-InnerProductSpace.rankOne ℝ (airyBoundaryVector 0) (airyBoundaryVector 0)) 0 ∧
      HasDerivAt (fun t => Ring.inverse (1 - airyKernelShift t))
        (Ring.inverse (1 - airyKernelShift 0) *
          (-InnerProductSpace.rankOne ℝ (airyBoundaryVector 0) (airyBoundaryVector 0)) *
          Ring.inverse (1 - airyKernelShift 0)) 0 :=
  ⟨airyBoundaryVector_ne_zero 0, airyEnergy_pos 0, norm_airyKernelShift_lt_one 0,
    airyKernelShift_one_sub_isUnit 0, hasDerivAt_airyKernelShift_norm 0,
    hasDerivAt_airyKernelResolvent_norm 0⟩


/-- The canonical inverse is symmetric on the genuine Hilbert space. -/
theorem airyKernelResolvent_symmetric
    (s : ℝ) -- [definition]
    (x y : Lp ℝ 2 halfLineMeasure) -- [definition]
    : inner ℝ (Ring.inverse (1 - airyKernelShift s) x) y =
        inner ℝ x (Ring.inverse (1 - airyKernelShift s) y) := by
  let R := Ring.inverse (1 - airyKernelShift s)
  have hx := contraction_ringInverse_right (airyKernelShift s)
    (norm_airyKernelShift_lt_one s) x
  have hy := contraction_ringInverse_right (airyKernelShift s)
    (norm_airyKernelShift_lt_one s) y
  have hs := (isSelfAdjoint_airyKernelShift s).isSymmetric (R x) (R y)
  calc
    inner ℝ (R x) y = inner ℝ (R x) (R y - airyKernelShift s (R y)) :=
      congrArg (inner ℝ (R x)) hy.symm
    _ = inner ℝ (R x - airyKernelShift s (R x)) (R y) := by
      rw [inner_sub_right, inner_sub_left]
      convert! congrArg (fun t : ℝ => inner ℝ (R x) (R y) - t) hs.symm using 1
    _ = inner ℝ x (R y) := congrArg (fun w => inner ℝ w (R y)) hx

/-- The actual inverse derivative factors through its actual response vector. -/
theorem airyKernelResolvent_rankOne_identity
    (s : ℝ) -- [definition]
    : Ring.inverse (1 - airyKernelShift s) *
          (-InnerProductSpace.rankOne ℝ (airyBoundaryVector s) (airyBoundaryVector s)) *
          Ring.inverse (1 - airyKernelShift s) =
        -InnerProductSpace.rankOne ℝ
          (Ring.inverse (1 - airyKernelShift s) (airyBoundaryVector s))
          (Ring.inverse (1 - airyKernelShift s) (airyBoundaryVector s)) := by
  ext x
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.neg_apply,
    InnerProductSpace.rankOne_apply, map_neg, map_smul]
  rw [← airyKernelResolvent_symmetric s (airyBoundaryVector s) x]

/-- Genuine operator-norm rank-one response formula for the inverse curve. -/
theorem hasDerivAt_airyKernelResolvent_rankOne
    (s : ℝ) -- [definition]
    : HasDerivAt (fun t => Ring.inverse (1 - airyKernelShift t))
        (-InnerProductSpace.rankOne ℝ
          (Ring.inverse (1 - airyKernelShift s) (airyBoundaryVector s))
          (Ring.inverse (1 - airyKernelShift s) (airyBoundaryVector s))) s := by
  simpa only [airyKernelResolvent_rankOne_identity] using hasDerivAt_airyKernelResolvent_norm s

/-- The response, symmetry and derivative coexist on a nonzero actual instance. -/
theorem airy_resolvent_rankOne_joint_probe :
    airyBoundaryVector 0 ≠ 0 ∧
      Ring.inverse (1 - airyKernelShift 0) (airyBoundaryVector 0) ≠ 0 ∧
      inner ℝ (Ring.inverse (1 - airyKernelShift 0) (airyBoundaryVector 0))
        (airyBoundaryVector 0) =
        inner ℝ (airyBoundaryVector 0)
          (Ring.inverse (1 - airyKernelShift 0) (airyBoundaryVector 0)) ∧
      HasDerivAt (fun t => Ring.inverse (1 - airyKernelShift t))
        (-InnerProductSpace.rankOne ℝ
          (Ring.inverse (1 - airyKernelShift 0) (airyBoundaryVector 0))
          (Ring.inverse (1 - airyKernelShift 0) (airyBoundaryVector 0))) 0 := by
  have hn : Ring.inverse (1 - airyKernelShift 0) (airyBoundaryVector 0) ≠ 0 := by
    intro hz
    have h := contraction_ringInverse_right (airyKernelShift 0)
      (norm_airyKernelShift_lt_one 0) (airyBoundaryVector 0)
    have ha : airyBoundaryVector 0 = 0 := by simpa [hz] using h.symm
    exact airyBoundaryVector_ne_zero 0 ha
  exact ⟨airyBoundaryVector_ne_zero 0, hn,
    airyKernelResolvent_symmetric 0 (airyBoundaryVector 0) (airyBoundaryVector 0),
    hasDerivAt_airyKernelResolvent_rankOne 0⟩

end RMTFoundations.TracyWidom.AiryNormDerivative

#print axioms RMTFoundations.TracyWidom.AiryNormDerivative.hasDerivAt_airyKernelShift_norm
#print axioms RMTFoundations.TracyWidom.AiryNormDerivative.airyKernelShift_one_sub_isUnit
#print axioms RMTFoundations.TracyWidom.AiryNormDerivative.hasDerivAt_airyKernelResolvent_norm
#print axioms RMTFoundations.TracyWidom.AiryNormDerivative.airy_norm_derivative_joint_probe
#print axioms RMTFoundations.TracyWidom.AiryNormDerivative.airyKernelResolvent_symmetric
#print axioms RMTFoundations.TracyWidom.AiryNormDerivative.airyKernelResolvent_rankOne_identity
#print axioms RMTFoundations.TracyWidom.AiryNormDerivative.hasDerivAt_airyKernelResolvent_rankOne
#print axioms RMTFoundations.TracyWidom.AiryNormDerivative.airy_resolvent_rankOne_joint_probe
