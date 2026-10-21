import RMTFoundations.TracyWidom.TWCoordinateSmooth
import RMTFoundations.TracyWidom.TWDensityRegularity1
import RMTFoundations.TracyWidom.TWDensityRegularity2
set_option autoImplicit false

namespace RMTFoundations.TracyWidom.TWDensitySmooth
open scoped ContDiff
open RMTFoundations.TracyWidom
open RMTFoundations.Airy RMTFoundations.AiryKernel RMTFoundations.TWOneBounds
open RMTFoundations.TracyWidom.ResolventCoordinates RMTFoundations.TracyWidom.ResolventDiagonal
open RMTFoundations.TracyWidom.TWCoordinateSmooth RMTFoundations.TracyWidom.TWDensityRegularity1

/-- The physical GOE and GUE CDFs have every finite differentiability order. -/
theorem cdfs_contDiff_nat
    (n : ℕ /- [definition] -/) :
    ContDiff ℝ n TW1R ∧ ContDiff ℝ n TW2R := by
  induction n with
  | zero => exact ⟨contDiff_zero.mpr TW1R_continuous, contDiff_zero.mpr TW2R_continuous⟩
  | succ n ih =>
    obtain ⟨hq,hp,hu,hv⟩ := coordinates_contDiff_nat n
    have he1 : deriv TW1R = fun s => TW1R s * (resolventQ s + resolventU s) / 2 :=
      funext fun s => (hasDerivAt_TW1R_coordinates s).deriv
    have he2 : deriv TW2R = fun s => TW2R s * resolventU s :=
      funext fun s => (TW2R_hasDerivAt s).deriv
    simp only [Nat.cast_succ]
    refine ⟨contDiff_succ_iff_deriv.mpr ⟨TW1R_differentiable, ?_, ?_⟩,
      contDiff_succ_iff_deriv.mpr ⟨TW2R_differentiable, ?_, ?_⟩⟩
    · simp
    · rw [he1]
      exact (ih.1.mul (hq.add hu)).div_const 2
    · simp
    · rw [he2]
      exact ih.2.mul hu

/-- Both actual CDFs are smooth globally. -/
theorem cdfs_contDiff_infty : ContDiff ℝ ∞ TW1R ∧ ContDiff ℝ ∞ TW2R :=
  ⟨contDiff_infty.mpr (fun n => (cdfs_contDiff_nat n).1),
    contDiff_infty.mpr (fun n => (cdfs_contDiff_nat n).2)⟩

/-- The strictly positive GOE and GUE densities are smooth globally. -/
theorem densities_contDiff_infty : ContDiff ℝ ∞ TW1Density ∧ ContDiff ℝ ∞ TW2Density := by
  obtain ⟨hq,hp,hu,hv⟩ := coordinates_contDiff_infty
  have he : (fun s => TW1R s * (resolventQ s + resolventU s) / 2) = TW1Density :=
    funext fun s => (TW1Density_eq_coordinates s).symm
  constructor
  · rw [← he]
    exact (cdfs_contDiff_infty.1.mul (hq.add hu)).div_const 2
  · exact cdfs_contDiff_infty.2.mul hu

/-- Smoothness and positive physical densities jointly hold at all real shifts. -/
theorem smooth_density_all_binder_joint_probe :
    (∀ s : ℝ, airyBoundaryVector s ≠ 0 ∧ 0 < TW1Density s ∧ 0 < TW2Density s) ∧
    (∀ n : ℕ, ContDiff ℝ n TW1R ∧ ContDiff ℝ n TW2R) ∧
    ContDiff ℝ ∞ TW1R ∧ ContDiff ℝ ∞ TW2R ∧
    ContDiff ℝ ∞ TW1Density ∧ ContDiff ℝ ∞ TW2Density :=
  ⟨fun s => ⟨airyBoundaryVector_ne_zero s, TW1Density_positive s, TW2Density_positive s⟩,
    cdfs_contDiff_nat, cdfs_contDiff_infty.1, cdfs_contDiff_infty.2,
    densities_contDiff_infty⟩

/-- Smoothness of the physical GOE CDF. -/
theorem TW1R_contDiff_infty : ContDiff ℝ ∞ TW1R := cdfs_contDiff_infty.1

/-- Smoothness of the physical GUE CDF. -/
theorem TW2R_contDiff_infty : ContDiff ℝ ∞ TW2R := cdfs_contDiff_infty.2

/-- Smoothness of the physical GOE density. -/
theorem TW1Density_contDiff_infty : ContDiff ℝ ∞ TW1Density := densities_contDiff_infty.1

/-- Smoothness of the physical GUE density. -/
theorem TW2Density_contDiff_infty : ContDiff ℝ ∞ TW2Density := densities_contDiff_infty.2

end RMTFoundations.TracyWidom.TWDensitySmooth

#print axioms RMTFoundations.TracyWidom.TWDensitySmooth.cdfs_contDiff_nat
#print axioms RMTFoundations.TracyWidom.TWDensitySmooth.cdfs_contDiff_infty
#print axioms RMTFoundations.TracyWidom.TWDensitySmooth.densities_contDiff_infty
#print axioms RMTFoundations.TracyWidom.TWDensitySmooth.smooth_density_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.TWDensitySmooth.TW1R_contDiff_infty
#print axioms RMTFoundations.TracyWidom.TWDensitySmooth.TW2R_contDiff_infty
#print axioms RMTFoundations.TracyWidom.TWDensitySmooth.TW1Density_contDiff_infty
#print axioms RMTFoundations.TracyWidom.TWDensitySmooth.TW2Density_contDiff_infty
