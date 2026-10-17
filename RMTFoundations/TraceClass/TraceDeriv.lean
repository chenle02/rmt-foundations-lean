import RMTFoundations.TraceClass.Fredholm
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# The trace is the derivative of the Fredholm determinant at the identity

This file gives the precise analytic form of the informal statement
`det (1 + t K) = 1 + t * tr K + O(t ^ 2)`:

* `hasDerivAt_det_one_add_smul` : over a nontrivially normed field, the map
  `t ↦ det (1 + t • K)` is differentiable at `0` with derivative `tr K`;
* `deriv_det_one_add_smul` : the same statement phrased with `deriv`;
* `isBigO_det_one_add_smul_remainder` : the remainder
  `det (1 + t • K) - 1 - t * tr K` is `O(t ^ 2)` as `t → 0`.

The purely algebraic counterpart, valid over any commutative ring and with an
explicit remainder rather than a `O`, is
`RMTFoundations.TraceClass.det_one_add_smul_sub_eq_sq_mul` in `Fredholm.lean`.

## What is NOT proved here

* No statement about `log det` versus `tr log`.  That identity needs either a
  convergent logarithm series (hence a norm bound on `K`, and a normed algebra
  structure on matrices, none of which is set up here) or the functional
  calculus.  What is available here is only the first-order term.
* No differentiability of `K ↦ det (1 + K)` as a function of the matrix, and no
  higher derivatives.
* Nothing infinite-dimensional.
-/

namespace RMTFoundations.TraceClass

open Matrix Polynomial Filter Asymptotics

variable {n : Type* /- [definition] -/ } [DecidableEq n /- [definition] -/ ] [Fintype n /- [definition] -/ ]
variable {𝕜 : Type* /- [definition] -/ } [NontriviallyNormedField 𝕜 /- [definition] -/ ]

/-- **The derivative of the Fredholm determinant at the identity is the trace.**
`t ↦ det (1 + t • K)` is differentiable at `0`, with derivative `tr K`. -/
theorem hasDerivAt_det_one_add_smul (K : Matrix n n 𝕜 /- [definition] -/ ) :
    HasDerivAt (fun t : 𝕜 => det (1 + t • K)) K.trace 0 := by
  have h : (fun t : 𝕜 => det (1 + t • K)) =
      fun t : 𝕜 => (det (1 + (X : 𝕜[X]) • K.map C)).eval t := by
    funext t
    exact (eval_det_one_add_X_smul K t).symm
  rw [h, ← Matrix.derivative_det_one_add_X_smul K]
  exact Polynomial.hasDerivAt _ 0

theorem differentiableAt_det_one_add_smul (K : Matrix n n 𝕜 /- [definition] -/ ) :
    DifferentiableAt 𝕜 (fun t : 𝕜 => det (1 + t • K)) 0 :=
  (hasDerivAt_det_one_add_smul K).differentiableAt

theorem deriv_det_one_add_smul (K : Matrix n n 𝕜 /- [definition] -/ ) :
    deriv (fun t : 𝕜 => det (1 + t • K)) 0 = K.trace :=
  (hasDerivAt_det_one_add_smul K).deriv

/-- The remainder in `det (1 + t • K) = 1 + t * tr K + O(t ^ 2)` really is
`O(t ^ 2)` as `t → 0`. -/
theorem isBigO_det_one_add_smul_remainder (K : Matrix n n 𝕜 /- [definition] -/ ) :
    (fun t : 𝕜 => det (1 + t • K) - 1 - t * K.trace) =O[nhds (0 : 𝕜)] fun t : 𝕜 => t ^ 2 := by
  set g : 𝕜[X] := (det (1 + (X : 𝕜[X]) • K.map C)).divX.divX with hg
  have hrw : (fun t : 𝕜 => det (1 + t • K) - 1 - t * K.trace) = fun t : 𝕜 => g.eval t * t ^ 2 := by
    funext t
    rw [Matrix.det_one_add_smul t K, hg]
    ring
  rw [hrw]
  have htend : Tendsto (fun t : 𝕜 => g.eval t) (nhds 0) (nhds (g.eval 0)) :=
    (g.continuous.tendsto 0)
  have hb : (fun t : 𝕜 => g.eval t) =O[nhds (0 : 𝕜)] (1 : 𝕜 → 𝕜) := htend.isBigO_one 𝕜
  simpa using hb.mul (isBigO_refl (fun t : 𝕜 => t ^ 2) (nhds (0 : 𝕜)))

end RMTFoundations.TraceClass

#print axioms RMTFoundations.TraceClass.hasDerivAt_det_one_add_smul
#print axioms RMTFoundations.TraceClass.differentiableAt_det_one_add_smul
#print axioms RMTFoundations.TraceClass.deriv_det_one_add_smul
#print axioms RMTFoundations.TraceClass.isBigO_det_one_add_smul_remainder
