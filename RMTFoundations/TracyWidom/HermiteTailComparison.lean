import RMTFoundations.TracyWidom.ODEMaximumPrinciple
import RMTFoundations.TracyWidom.HermiteGaussianDecay
import RMTFoundations.TracyWidom.HermiteEdgeReduction
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteTailComparison
open Filter Topology Real
open RMTFoundations.TracyWidom.GUEHermite RMTFoundations.TracyWidom.HermiteEdgeODE
open RMTFoundations.TracyWidom.HermiteEdgeScale RMTFoundations.TracyWidom.HermiteEdgeReduction
open RMTFoundations.TracyWidom.HermiteGaussianDecay
open RMTFoundations.TracyWidom.ODEMaximumPrinciple

/-- Uniform positive coefficient floor, for every positive dimension. -/
lemma edgeCoefficient_halfline_floor (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hx : 1 ≤ x /- [standing] -/) : (1/2:ℝ) ≤ edgeCoefficient N x := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp := rpow_le_one_of_one_le_of_nonpos hN1 (show (-1/3:ℝ) ≤ 0 by norm_num)
  have hpos : 0 ≤ x^2/4*(N:ℝ)^(-2/3:ℝ) := by positivity
  unfold edgeCoefficient
  linarith

/-- Decay of the literal scaled mode, derived rather than assumed. -/
lemma edgeMode_tendsto (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) : Tendsto (edgeMode N) atTop (𝓝 0) :=
  affine_hermiteMode_tendsto N (edgeAmplitude N) (2*sqrt N) (edgeScale N)
    (edgeScale_pos N hN)

/-- Actual Hermite tail comparison with a dimension-independent exponential rate.
The boundary amplitude is literal and is not asserted to be uniformly bounded. -/
theorem edgeMode_relative_tail
    (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hx : 1 ≤ x /- [standing] -/) :
    |edgeMode N x| ≤ |edgeMode N 1| *exp (-(1/2:ℝ)*(x-1)) := by
  apply absolute_exponential_tail (edgeMode N) (edgeSlope N) (edgeCoefficient N)
    (edgeMode_hasDerivAt N) (edgeSlope_hasDerivAt N hN) 1 (1/2) (by norm_num)
    ?_ (edgeMode_tendsto N hN) x hx
  intro t ht
  have H := edgeCoefficient_halfline_floor N hN t ht
  norm_num at *
  linarith

/-- The neighboring mode uses the SAME N-dependent point and amplitude. -/
noncomputable def previousMode (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ :=
  affineMode (N-1) (edgeAmplitude N) (2*sqrt N) (edgeScale N) x
noncomputable def previousSlope (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ :=
  affineSlope (N-1) (edgeAmplitude N) (2*sqrt N) (edgeScale N) x
lemma previousMode_hasDerivAt (N : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : HasDerivAt (previousMode N) (previousSlope N x) x :=
  affineMode_hasDerivAt (N-1) _ _ _ x
lemma previousSlope_hasDerivAt (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    HasDerivAt (previousSlope N)
      ((edgeCoefficient N x+(edgeScale N)^2)*previousMode N x) x := by
  have H := affineSlope_hasDerivAt (N-1) (edgeAmplitude N) (2*sqrt N) (edgeScale N) x
  have hcast : ((N-1:ℕ):ℝ) = (N:ℝ)-1 := by
    rw [Nat.cast_sub (show 1 ≤ N by omega),Nat.cast_one]
  have hq : (edgeScale N)^2 * ((edgePoint N x)^2/4 - ((N-1:ℕ):ℝ) - 1/2) =
      edgeCoefficient N x+(edgeScale N)^2 := by
    rw [hcast]
    calc
      _ = (edgeScale N)^2*((edgePoint N x)^2/4-(N:ℝ)-1/2)+(edgeScale N)^2 := by ring
      _ = _ := by rw [edge_coefficient_identity N hN x]
  change HasDerivAt (previousSlope N)
    ((edgeScale N)^2*((edgePoint N x)^2/4-((N-1:ℕ):ℝ)-1/2)*previousMode N x) x at H
  rw [hq] at H
  exact H
lemma previousMode_tendsto (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/) : Tendsto (previousMode N) atTop (𝓝 0) :=
  affine_hermiteMode_tendsto (N-1) (edgeAmplitude N) (2*sqrt N) (edgeScale N)
    (edgeScale_pos N hN)

/-- Adjacent Hermite mode tail, on the same edge scale and at the same points. -/
theorem previousMode_relative_tail
    (N : ℕ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hx : 1 ≤ x /- [standing] -/) :
    |previousMode N x| ≤ |previousMode N 1| *exp (-(1/2:ℝ)*(x-1)) := by
  apply absolute_exponential_tail (previousMode N) (previousSlope N)
    (fun t => edgeCoefficient N t+(edgeScale N)^2)
    (previousMode_hasDerivAt N) (previousSlope_hasDerivAt N hN) 1 (1/2) (by norm_num)
    ?_ (previousMode_tendsto N hN) x hx
  intro t ht
  have H := edgeCoefficient_halfline_floor N hN t ht
  nlinarith [sq_nonneg (edgeScale N)]

/-- Joint witness supplies both literal modes, both ODEs and both infinite-tail
limits on the same growing positive dimensions, with strictly positive density. -/
theorem hermite_relative_tail_joint_probe (n : ℕ /- [definition] -/) :
    0 < edgeAmplitude (n+1) ∧ 0 < edgeScale (n+1) ∧
    0 < hermiteDensity (n+1) (fun i => (i.val:ℝ)) ∧
    (∀ x, HasDerivAt (edgeMode (n+1)) (edgeSlope (n+1) x) x) ∧
    (∀ x, HasDerivAt (edgeSlope (n+1)) (edgeCoefficient (n+1) x*edgeMode (n+1) x) x) ∧
    Tendsto (edgeMode (n+1)) atTop (𝓝 0) ∧
    (∀ x, HasDerivAt (previousMode (n+1)) (previousSlope (n+1) x) x) ∧
    (∀ x, HasDerivAt (previousSlope (n+1))
      ((edgeCoefficient (n+1) x+(edgeScale (n+1))^2)*previousMode (n+1) x) x) ∧
    Tendsto (previousMode (n+1)) atTop (𝓝 0) ∧
    (∀ x, 1 ≤ x → (1/2:ℝ) ≤ edgeCoefficient (n+1) x) ∧
    (∀ x, 1 ≤ x → |edgeMode (n+1) x| ≤ |edgeMode (n+1) 1| *exp (-(1/2:ℝ)*(x-1))) ∧
    (∀ x, 1 ≤ x → |previousMode (n+1) x| ≤ |previousMode (n+1) 1| *exp (-(1/2:ℝ)*(x-1))) := by
  have H := edge_mode_all_binder_joint_probe n
  refine ⟨H.1,H.2.1,H.2.2.1,H.2.2.2.1,H.2.2.2.2,
    edgeMode_tendsto _ (by omega),previousMode_hasDerivAt _,
    previousSlope_hasDerivAt _ (by omega),previousMode_tendsto _ (by omega),?_,?_,?_⟩
  · intro x hx; exact edgeCoefficient_halfline_floor _ (by omega) x hx
  · intro x hx; exact edgeMode_relative_tail _ (by omega) x hx
  · intro x hx; exact previousMode_relative_tail _ (by omega) x hx

end RMTFoundations.TracyWidom.HermiteTailComparison

#print axioms RMTFoundations.TracyWidom.HermiteTailComparison.edgeCoefficient_halfline_floor
#print axioms RMTFoundations.TracyWidom.HermiteTailComparison.edgeMode_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteTailComparison.edgeMode_relative_tail
#print axioms RMTFoundations.TracyWidom.HermiteTailComparison.previousMode
#print axioms RMTFoundations.TracyWidom.HermiteTailComparison.previousSlope
#print axioms RMTFoundations.TracyWidom.HermiteTailComparison.previousMode_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteTailComparison.previousSlope_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteTailComparison.previousMode_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteTailComparison.previousMode_relative_tail
#print axioms RMTFoundations.TracyWidom.HermiteTailComparison.hermite_relative_tail_joint_probe
