import RMTFoundations.TracyWidom.Smoothness
import RMTFoundations.TracyWidom.TW4SecondOrder
set_option autoImplicit false
open scoped ContDiff
open RMTFoundations.TracyWidom
example : ContDiff ℝ ∞ TW1R ∧ ContDiff ℝ ∞ TW2R := Smoothness.cdfs
example : ContDiff ℝ ∞ TW1Density ∧ ContDiff ℝ ∞ TW2Density := Smoothness.densities
example : ContDiff ℝ 2 TW4R := TW4R_contDiff_two
