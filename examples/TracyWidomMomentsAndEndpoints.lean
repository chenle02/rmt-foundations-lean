import RMTFoundations.TracyWidom.Moments
import RMTFoundations.TracyWidom.OrderFourEndpoints
import RMTFoundations.TracyWidom.Airy2
import RMTFoundations.TracyWidom.GUEIdentification
open RMTFoundations.TracyWidom MeasureTheory Filter
open scoped Topology

example (p : ℝ /- [definition] -/) (hp : 0 ≤ p /- [standing] -/) :
    Integrable (fun x : ℝ => |x|^p) TW1Measure := TW1_absolute_moment_integrable p hp
example : Continuous TW4R := continuous_TW4R
example (q : ℝ /- [definition] -/) (h0 : 0 < q /- [standing] -/)
    (h1 : q < 1 /- [standing] -/) : ∃ s : ℝ, TW4R s = q := TW4R_level_exists q h0 h1
example (t s : ℝ /- [definition] -/) : Airy2.oneTimeFredholm t s = TW2 s :=
  Airy2.oneTimeFredholm_eq_TW2 t s
example (F : ℝ → ℝ /- [definition] -/)
    (hGUE : GUEIdentification.GUELimit F /- [standing] -/)
    (hFredholm : GUEIdentification.GUELimit TW2R /- [standing] -/) : F = TW2R :=
  GUEIdentification.gaussian_unitary_limit_eq_TW2R F hGUE hFredholm
