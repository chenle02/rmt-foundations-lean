import RMTFoundations.TracyWidom.GUEHermite
import RMTFoundations.TracyWidom.PolynomialGaussianDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteGaussianDecay
open Filter Topology Real
open RMTFoundations.TracyWidom.GUEHermite RMTFoundations.TracyWidom.PolynomialGaussianDecay

/-- Fixed-index decay is proved from the actual polynomial--Gaussian formula. -/
theorem hermiteMode_tendsto (N : ℕ /- [definition] -/) :
    Tendsto (hermiteMode N) atTop (𝓝 0) := by
  have H := (polynomial_gaussian_tendsto (realHermite N) (1/4) (by norm_num)).const_mul
    (hermiteNormalizer N)
  convert H using 1
  · funext x
    dsimp [hermiteMode,gaussianWeight,hpoly]
    rw [show -x^2/4 = -(1/4:ℝ)*x^2 by ring]
    ring
  · simp

/-- Every positive affine edge scale preserves the literal Hermite decay. -/
theorem affine_hermiteMode_tendsto
    (N : ℕ /- [definition] -/)
    (A b δ : ℝ /- [definition] -/)
    (hδ : 0 < δ /- [standing] -/) :
    Tendsto (fun x : ℝ => A*hermiteMode N (b+δ*x)) atTop (𝓝 0) := by
  have hd : Tendsto (fun x : ℝ => δ*x) atTop atTop := tendsto_id.const_mul_atTop hδ
  have hx : Tendsto (fun x : ℝ => b+δ*x) atTop atTop := by
    simpa only [add_comm] using tendsto_atTop_add_const_right atTop b hd
  simpa only [Function.comp_def,mul_zero] using ((hermiteMode_tendsto N).comp hx).const_mul A

/-- All decay binders have a growing positive-scale, nonzero-polynomial witness. -/
theorem hermite_decay_joint_probe (n : ℕ /- [definition] -/) :
    0 < ((n+1:ℕ):ℝ)^(-1/6:ℝ) ∧
    realHermite (n+1) ≠ 0 ∧
    Tendsto (fun x : ℝ => ((n+1:ℕ):ℝ)^(1/12:ℝ) *
      hermiteMode (n+1) (2*sqrt (n+1)+((n+1:ℕ):ℝ)^(-1/6:ℝ)*x)) atTop (𝓝 0) := by
  have hp : 0 < ((n+1:ℕ):ℝ)^(-1/6:ℝ) := rpow_pos_of_pos (by positivity) _
  refine ⟨hp,?_,affine_hermiteMode_tendsto _ _ _ _ hp⟩
  exact ((Polynomial.hermite_monic (n+1)).map (Int.castRingHom ℝ)).ne_zero

end RMTFoundations.TracyWidom.HermiteGaussianDecay

#print axioms RMTFoundations.TracyWidom.HermiteGaussianDecay.hermiteMode_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteGaussianDecay.affine_hermiteMode_tendsto
#print axioms RMTFoundations.TracyWidom.HermiteGaussianDecay.hermite_decay_joint_probe
