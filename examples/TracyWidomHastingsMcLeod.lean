import RMTFoundations.TracyWidom.HastingsMcLeod
set_option autoImplicit false
open Filter RMTFoundations.TracyWidom
open scoped Topology

example : ∃! q : ℝ → ℝ, Differentiable ℝ q ∧
    (∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s) ∧
    Tendsto (fun s => q s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) :=
  HastingsMcLeod.exists_unique

example
    (q : ℝ → ℝ /- [definition] -/)
    (hq : Differentiable ℝ q /- [standing] -/)
    (hqq : ∀ s, HasDerivAt (deriv q) (s*q s+2*(q s)^3) s /- [standing] -/)
    (hnq : Tendsto (fun s => q s/RMTFoundations.Airy.airyAiReal s) atTop (𝓝 1) /- [standing] -/) :
    q=Painleve.q := HastingsMcLeod.eq_canonical q hq hqq hnq
