import RMTFoundations.TracyWidom.Painleve
import RMTFoundations.TracyWidom.Regularity
import RMTFoundations.TracyWidom.TailBounds
open RMTFoundations.TracyWidom MeasureTheory Set

example : StrictMono TW1R := strictMono_TW1R
example : ContDiff ℝ 1 TW2R := contDiff_TW2R
example (s : ℝ /- [definition] -/) : 0 < TW1Density s := TW1Density_positive s
example (s : ℝ /- [definition] -/) :
    TW2R s = Real.exp (-(∫ t in Ioi s, (t-s)*(Painleve.q t)^2)) :=
  Painleve.TW2R_integral_formula s
example (p : ℝ /- [definition] -/) (hp0 : 0 < p /- [standing] -/)
    (hp1 : p < 1 /- [standing] -/) : ∃! s, TW2R s = p :=
  TW2R_quantile_exists_unique p hp0 hp1
