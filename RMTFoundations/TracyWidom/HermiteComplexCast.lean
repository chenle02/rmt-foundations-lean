import RMTFoundations.TracyWidom.GUEHermite
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteComplexCast
open Polynomial
open RMTFoundations.TracyWidom.GUEHermite
lemma aeval_real_complex (p : Polynomial ℤ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    aeval (x:ℂ) p = ((aeval x p : ℝ):ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add,map_add,Complex.ofReal_add,hp,hq]
  | monomial n a => simp [Polynomial.aeval_def,Polynomial.eval₂_monomial]
lemma hpoly_aeval (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : hpoly n x = aeval x (hermite n) := by
  simp only [hpoly,realHermite,eval_map,aeval_def,algebraMap_int_eq]
lemma complex_hpoly (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) : aeval (x:ℂ) (hermite n) = (hpoly n x:ℂ) := by
  rw [aeval_real_complex,hpoly_aeval]
/-- The bridge retains the literal monic integer polynomial in growing dimensions. -/
theorem complex_cast_joint_probe (k : ℕ /- [definition] -/) :
    ∃ n : ℕ, k < n ∧ hermite n ≠ 0 ∧ ∀ x : ℝ,
      aeval (x:ℂ) (hermite n) = (hpoly n x:ℂ) := by
  exact ⟨k+1,by omega,(hermite_monic (k+1)).ne_zero,complex_hpoly (k+1)⟩
end RMTFoundations.TracyWidom.HermiteComplexCast

#print axioms RMTFoundations.TracyWidom.HermiteComplexCast.aeval_real_complex
#print axioms RMTFoundations.TracyWidom.HermiteComplexCast.hpoly_aeval
#print axioms RMTFoundations.TracyWidom.HermiteComplexCast.complex_hpoly
#print axioms RMTFoundations.TracyWidom.HermiteComplexCast.complex_cast_joint_probe
