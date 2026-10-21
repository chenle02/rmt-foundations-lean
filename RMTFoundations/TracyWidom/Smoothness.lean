import RMTFoundations.TracyWidom.Functions
import RMTFoundations.TracyWidom.TWDensitySmooth
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Smoothness
open scoped ContDiff
open RMTFoundations.TracyWidom

/-- Both canonical real Tracy-Widom distribution functions are globally smooth. -/
theorem cdfs : ContDiff ℝ ∞ TW1R ∧ ContDiff ℝ ∞ TW2R :=
  TWDensitySmooth.cdfs_contDiff_infty

/-- Both canonical, strictly positive probability densities are globally smooth. -/
theorem densities : ContDiff ℝ ∞ TW1Density ∧ ContDiff ℝ ∞ TW2Density :=
  TWDensitySmooth.densities_contDiff_infty

/-- Smooth CDFs and positive smooth densities hold jointly on the actual Airy model. -/
theorem all_binder_joint_probe :
    (∀ s : ℝ, 0 < TW1Density s ∧ 0 < TW2Density s) ∧
    ContDiff ℝ ∞ TW1R ∧ ContDiff ℝ ∞ TW2R ∧
    ContDiff ℝ ∞ TW1Density ∧ ContDiff ℝ ∞ TW2Density :=
  ⟨fun s => ⟨TW1Density_positive s,TW2Density_positive s⟩,
    cdfs.1,cdfs.2,densities⟩
end RMTFoundations.TracyWidom.Smoothness

#print axioms RMTFoundations.TracyWidom.Smoothness.cdfs
#print axioms RMTFoundations.TracyWidom.Smoothness.densities
#print axioms RMTFoundations.TracyWidom.Smoothness.all_binder_joint_probe
