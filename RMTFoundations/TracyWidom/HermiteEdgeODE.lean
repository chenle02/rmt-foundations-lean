import RMTFoundations.TracyWidom.GUEHermite
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteEdgeODE
open Polynomial
open RMTFoundations.TracyWidom.GUEHermite

/-- Exact Hermite differential equation, before taking an asymptotic limit. -/
theorem hermite_polynomial_ode (n : ℕ /- [definition] -/) :
    derivative (derivative (hermite n)) =
      X * derivative (hermite n) - C (n : ℤ) * hermite n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [hermite_derivative_succ, derivative_mul, derivative_C, zero_mul, zero_add,
      hermite_succ n]
    ring

theorem realHermite_polynomial_ode (n : ℕ /- [definition] -/) :
    derivative (derivative (realHermite n)) =
      X * derivative (realHermite n) - C (n : ℝ) * realHermite n := by
  have h := congrArg (fun p : Polynomial ℤ => p.map (Int.castRingHom ℝ))
    (hermite_polynomial_ode n)
  simpa [realHermite, Polynomial.derivative_map] using h

noncomputable def polySlope (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ := (derivative (realHermite n)).eval x

noncomputable def modeSlope (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : ℝ :=
  gaussianWeight x * hermiteNormalizer n * (polySlope n x - x / 2 * hpoly n x)

lemma hpoly_hasDerivAt (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : HasDerivAt (hpoly n) (polySlope n x) x := by
  exact (realHermite n).hasDerivAt x

lemma gaussianWeight_hasDerivAt (x : ℝ /- [definition] -/) :
    HasDerivAt gaussianWeight (gaussianWeight x * (-x / 2)) x := by
  have h := (((hasDerivAt_id x).pow 2).neg.div_const 4).exp
  convert h using 1
  · rfl
  · dsimp [gaussianWeight]
    ring

lemma hermiteMode_hasDerivAt (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : HasDerivAt (hermiteMode n) (modeSlope n x) x := by
  have h := (gaussianWeight_hasDerivAt x).mul
    ((hpoly_hasDerivAt n x).const_mul (hermiteNormalizer n))
  convert h using 1 <;> first | rfl | (dsimp [hermiteMode, modeSlope]; ring)

/-- The normalized oscillator satisfies phi'' = (x²/4 - n - 1/2) phi. -/
lemma modeSlope_hasDerivAt (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    HasDerivAt (modeSlope n)
      ((x^2 / 4 - (n : ℝ) - 1 / 2) * hermiteMode n x) x := by
  have hp := (derivative (realHermite n)).hasDerivAt x
  have hp2 : (derivative (derivative (realHermite n))).eval x =
      x * polySlope n x - (n : ℝ) * hpoly n x := by
    rw [realHermite_polynomial_ode]
    simp [polySlope, hpoly]
  have h := ((gaussianWeight_hasDerivAt x).mul_const (hermiteNormalizer n)).mul
    (hp.sub (((hasDerivAt_id x).div_const 2).mul (hpoly_hasDerivAt n x)))
  convert h using 1 <;> try rfl
  all_goals
    dsimp only [Pi.sub_apply, Pi.mul_apply, id_eq]
    rw [hp2]
    dsimp [modeSlope, hermiteMode, polySlope]
    ring

/-- An arbitrary amplitude is retained: the ODE alone cannot normalize the limit. -/
noncomputable def affineMode (n : ℕ /- [definition] -/)
    (amplitude center scale x : ℝ /- [definition] -/) : ℝ :=
  amplitude * hermiteMode n (center + scale * x)

noncomputable def affineSlope (n : ℕ /- [definition] -/)
    (amplitude center scale x : ℝ /- [definition] -/) : ℝ :=
  amplitude * scale * modeSlope n (center + scale * x)

lemma affineMode_hasDerivAt (n : ℕ /- [definition] -/)
    (amplitude center scale x : ℝ /- [definition] -/) :
    HasDerivAt (affineMode n amplitude center scale)
      (affineSlope n amplitude center scale x) x := by
  have h := ((hermiteMode_hasDerivAt n (center + scale * x)).comp x
    ((hasDerivAt_id x).const_mul scale |>.const_add center)).const_mul amplitude
  convert h using 1 <;> first | rfl | (dsimp [affineMode, affineSlope]; ring)

lemma affineSlope_hasDerivAt (n : ℕ /- [definition] -/)
    (amplitude center scale x : ℝ /- [definition] -/) :
    HasDerivAt (affineSlope n amplitude center scale)
      (scale^2 * ((center + scale * x)^2 / 4 - (n : ℝ) - 1 / 2) *
        affineMode n amplitude center scale x) x := by
  have h := ((modeSlope_hasDerivAt n (center + scale * x)).comp x
    ((hasDerivAt_id x).const_mul scale |>.const_add center)).const_mul (amplitude * scale)
  convert h using 1 <;> first | rfl | (dsimp [affineMode, affineSlope]; ring)

/-- Joint probe has no analytic premise; every mode n+1 uses the same growing scale. -/
theorem affine_all_binder_joint_probe (n : ℕ /- [definition] -/) :
    ∃ amplitude center scale : ℝ, 0 < amplitude ∧ 0 < scale ∧
      center = 2 * Real.sqrt (n+1) ∧
      (∀ x, HasDerivAt (affineMode (n+1) amplitude center scale)
        (affineSlope (n+1) amplitude center scale x) x) ∧
      (∀ x, HasDerivAt (affineSlope (n+1) amplitude center scale)
        (scale^2 * ((center + scale*x)^2/4 - (n+1 : ℕ) - 1/2) *
          affineMode (n+1) amplitude center scale x) x) := by
  refine ⟨1, 2 * Real.sqrt (n+1), 1 / ((n+1 : ℕ) : ℝ), by norm_num,
    by positivity, rfl, ?_, ?_⟩
  · intro x; exact affineMode_hasDerivAt _ _ _ _ _
  · intro x; exact affineSlope_hasDerivAt _ _ _ _ _

end RMTFoundations.TracyWidom.HermiteEdgeODE

#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.hermite_polynomial_ode
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.realHermite_polynomial_ode
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.polySlope
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.modeSlope
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.hpoly_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.gaussianWeight_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.hermiteMode_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.modeSlope_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.affineMode
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.affineSlope
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.affineMode_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.affineSlope_hasDerivAt
#print axioms RMTFoundations.TracyWidom.HermiteEdgeODE.affine_all_binder_joint_probe
