import RMTFoundations.Stieltjes.Defs
import RMTFoundations.Stieltjes.HalfPlane
import RMTFoundations.Stieltjes.RealAxis
import RMTFoundations.Stieltjes.SelfConsistent
import RMTFoundations.Stieltjes.Semicircle

/-
* `RMTFoundations.Stieltjes.Defs` — the wrapper `stieltjes` around mathlib's
  `MeasureTheory.resolventTransform`, and the pointwise facts about the kernel
  `(x - z)⁻¹`.
* `RMTFoundations.Stieltjes.HalfPlane` — Herglotz positivity `0 < (m z).im`,
  the bound `‖m z‖ ≤ μ(ℝ) / z.im`, and analyticity on the upper half-plane.
* `RMTFoundations.Stieltjes.RealAxis` — the transform is real on the real axis
  and increases on closed intervals disjoint from the support.
* `RMTFoundations.Stieltjes.SelfConsistent` — the Dyson equation
  `m = (-z + a * m)⁻¹`, its quadratic form, the semicircle identity
  `m ^ 2 + z * m + 1 = 0`, uniqueness with positive imaginary part, and the
  exact stability identity with its quantitative consequences.

## What is NOT in this layer

There is no semicircle *measure* here, and the value of the Stieltjes transform
of any specific measure is never computed: the link between the semicircle law
and the quadratic identity is stated only as algebra about a hypothetical
solution.  There is no Stieltjes inversion, no Herglotz representation, no
existence theory for the self-consistent equation, and no edge-regime
(square-root) analysis.

-/
