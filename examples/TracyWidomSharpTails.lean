import RMTFoundations.TracyWidom.TW1SharpRightTail
import RMTFoundations.TracyWidom.TW2RightTail
import RMTFoundations.TracyWidom.TW4Regularity
import RMTFoundations.TracyWidom.GUEDensity
set_option autoImplicit false
open MeasureTheory RMTFoundations.TracyWidom

example : ContDiff ℝ 1 TW4R := TW4R_contDiff_one
example (N : ℕ /- [definition] -/) :
    (∫ x : Fin N → ℝ, GUEProjection.gueDensity N x
      ∂Measure.pi (fun _ => (volume : Measure ℝ))) = 1 := GUEProjection.gue_density_integral N
