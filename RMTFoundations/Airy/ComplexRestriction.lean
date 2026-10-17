import RMTFoundations.Airy.ODE
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Restricting complex Airy solutions to the real line

The real part of a complex Airy solution, restricted to real arguments, solves the real
Airy equation. The derivative conversion is mathlib's `HasDerivAt.real_of_complex`.

This file supplies an interface for complex Airy constructions in other packages without
importing those packages or choosing a normalization. In particular, these statements do not
identify a solution with the classical Ai or Bi functions, nor prove any asymptotics.
-/

namespace RMTFoundations.Airy

/-- Complex Airy derivative identities along the real axis give a real Airy solution after
taking real parts. No assumption that the complex values are real is needed. -/
theorem airySolution_realRestriction {f df : ℂ → ℂ /- [definition] -/ }
    (hf : ∀ x : ℝ, HasDerivAt f (df x) (x : ℂ)  /- [standing] -/ )
    (hdf : ∀ x : ℝ, HasDerivAt df ((x : ℂ) * f x) (x : ℂ)  /- [standing] -/ ) :
    IsAirySolution (fun x : ℝ => (f x).re) (fun x : ℝ => (df x).re) where
  hasDerivAt_left x := (hf x).real_of_complex
  hasDerivAt_right x := by
    simpa using (hdf x).real_of_complex

/-- A complex Airy solution on the whole plane restricts, by taking real parts, to a real
Airy solution. This form accepts derivative theorems for entire complex Airy functions directly. -/
theorem airySolution_realRestriction_of_complex {f df : ℂ → ℂ /- [definition] -/ }
    (hf : ∀ z : ℂ, HasDerivAt f (df z) z /- [standing] -/ )
    (hdf : ∀ z : ℂ, HasDerivAt df (z * f z) z /- [standing] -/ ) :
    IsAirySolution (fun x : ℝ => (f x).re) (fun x : ℝ => (df x).re) :=
  airySolution_realRestriction (fun x => hf x) (fun x => hdf x)

end RMTFoundations.Airy

#print axioms RMTFoundations.Airy.airySolution_realRestriction
#print axioms RMTFoundations.Airy.airySolution_realRestriction_of_complex
