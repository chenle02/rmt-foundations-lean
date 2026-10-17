import RMTFoundations.TracyWidom.OrderOneMonotone



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom.ResolventCoordinates

open MeasureTheory
open scoped InnerProductSpace
open RMTFoundations.Airy RMTFoundations.AiryBounds RMTFoundations.AiryKernel
open RMTFoundations.TWOneBounds RMTFoundations.TWOneMonotone

/-- The scalar u coordinate, using the canonical square-kernel inverse. -/
noncomputable def resolventU
    (s : ℝ) -- [definition]
    : ℝ := inner ℝ (airyBoundaryVector s)
      (Ring.inverse (1 - airyKernelShift s) (airyBoundaryVector s))

/-- The endpoint response q; not the diagonal resolvent u. Endpoint evaluation
of the continuous response remains a separate analytic identification. -/
noncomputable def resolventQ
    (s : ℝ) -- [definition]
    : ℝ := airyAiReal s + inner ℝ (airyBoundaryVector s)
      (airyHankelShift s (Ring.inverse (1 - airyKernelShift s) (airyBoundaryVector s)))

/-- The determinant derivative in Tracy--Widom coordinates. -/
theorem hasDerivAt_TW1R_coordinates
    (s : ℝ) -- [definition]
    : HasDerivAt TW1R (TW1R s * (resolventQ s + resolventU s) / 2) s := by
  simpa only [resolventQ, resolventU, airy_boundary_resolvent_parity_identity] using
    hasDerivAt_TW1R_canonical_resolvent s

/-- The logarithmic derivative has no positivity or inverse hypothesis. -/
theorem hasDerivAt_log_TW1R_coordinates
    (s : ℝ) -- [definition]
    : HasDerivAt (fun t => Real.log (TW1R t))
      ((resolventQ s + resolventU s) / 2) s := by
  have hn : TW1R s ≠ 0 := (TW1R_positive_bounds s).1.ne'
  convert (hasDerivAt_TW1R_coordinates s).log hn using 1
  field_simp

/-- The factor two in the GOE representation is fixed by the actual square. -/
theorem hasDerivAt_log_TW1R_sq_coordinates
    (s : ℝ) -- [definition]
    : HasDerivAt (fun t => Real.log (TW1R t ^ 2))
      (resolventQ s + resolventU s) s := by
  have he : (fun t => Real.log (TW1R t ^ 2)) =
      (fun t => (2 : ℝ) * Real.log (TW1R t)) := by
    funext t
    rw [Real.log_pow]
    norm_num
  rw [he]
  convert! (hasDerivAt_log_TW1R_coordinates s).const_mul 2 using 1 <;> ring

/-- All canonical determinant and inverse objects occur jointly in a nonzero
physical Airy instance. There is no bundle or event assumption. -/
theorem coordinates_joint_probe
    : airyBoundaryVector 0 ≠ 0 ∧ 0 < TW1R 0 ∧ TW1R 0 < 1 ∧
      0 < resolventU 0 ∧
      HasDerivAt (fun t => Real.log (TW1R t ^ 2))
        (resolventQ 0 + resolventU 0) 0 := by
  exact ⟨airyBoundaryVector_ne_zero 0, (TW1R_positive_bounds 0).1,
    TW1R_lt_one 0, airy_inverse_square_boundary_positive 0,
    hasDerivAt_log_TW1R_sq_coordinates 0⟩

end RMTFoundations.TracyWidom.ResolventCoordinates

#print axioms RMTFoundations.TracyWidom.ResolventCoordinates.resolventU
#print axioms RMTFoundations.TracyWidom.ResolventCoordinates.resolventQ
#print axioms RMTFoundations.TracyWidom.ResolventCoordinates.hasDerivAt_TW1R_coordinates
#print axioms RMTFoundations.TracyWidom.ResolventCoordinates.hasDerivAt_log_TW1R_coordinates
#print axioms RMTFoundations.TracyWidom.ResolventCoordinates.hasDerivAt_log_TW1R_sq_coordinates
#print axioms RMTFoundations.TracyWidom.ResolventCoordinates.coordinates_joint_probe
