import RMTFoundations.TracyWidom.HermiteEdgeKernel
import Mathlib.Tactic
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HermiteKernelTranslation
open Polynomial Finset
open RMTFoundations.TracyWidom.GUEHermite RMTFoundations.TracyWidom.HermiteEdgeODE RMTFoundations.TracyWidom.HermiteEdgeKernel

/-- Raising formula for the literal normalized oscillator. -/
theorem modeSlope_upper (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    modeSlope n x = x/2*hermiteMode n x-
      Real.sqrt ((n+1 : ℕ) : ℝ)*hermiteMode (n+1) x := by
  have hp : hpoly (n+1) x = x*hpoly n x-polySlope n x := by
    simp only [hpoly,polySlope,realHermite,hermite_succ,Polynomial.map_sub,
      Polynomial.map_mul,Polynomial.map_X,Polynomial.derivative_map,
      Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_X]
  have hn := sqrt_mul_hermiteNormalizer_succ n
  have hh := congrArg (fun z : ℝ => gaussianWeight x*z*hpoly (n+1) x) hn
  unfold modeSlope hermiteMode
  rw [hp]
  rw [hp] at hh
  nlinarith [hh]

/-- Symmetric lowering/raising expression, including degree zero. -/
theorem modeSlope_symmetric (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    modeSlope n x =
      (Real.sqrt (n : ℝ)*hermiteMode (n-1) x-
        Real.sqrt ((n+1 : ℕ) : ℝ)*hermiteMode (n+1) x)/2 := by
  cases n with
  | zero =>
    have hu := modeSlope_upper 0 x
    have hx : hermiteMode 1 x = x*hermiteMode 0 x := by
      have hn := sqrt_mul_hermiteNormalizer_succ 0
      norm_num at hn
      simp only [hermiteMode,hpoly_zero,hpoly_one]
      rw [hn]
      ring
    norm_num at hu ⊢
    rw [hx] at hu ⊢
    linarith
  | succ n =>
    have hl := modeSlope_lower n x
    have hu := modeSlope_upper (n+1) x
    simp only [Nat.add_sub_cancel] at *
    linarith

noncomputable def pairDerivative (k : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) : ℝ :=
  modeSlope k x*hermiteMode k y+hermiteMode k x*modeSlope k y
noncomputable def boundaryPair (k : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) : ℝ :=
  hermiteMode k x*hermiteMode (k-1) y+hermiteMode (k-1) x*hermiteMode k y

/-- The derivative terms telescope with the exact endpoint coefficient. -/
theorem pairDerivative_telescope (k : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    pairDerivative k x y = Real.sqrt (k : ℝ)/2*boundaryPair k x y-
      Real.sqrt ((k+1 : ℕ) : ℝ)/2*boundaryPair (k+1) x y := by
  unfold pairDerivative boundaryPair
  rw [modeSlope_symmetric k x,modeSlope_symmetric k y]
  simp only [Nat.add_sub_cancel]
  ring

theorem kernel_derivative_sum (N : ℕ /- [definition] -/)
    (x y : ℝ /- [definition] -/) :
    (∑ k ∈ Finset.range N, pairDerivative k x y) =
      -(Real.sqrt (N : ℝ)/2)*boundaryPair N x y := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih,pairDerivative_telescope]
    ring

/-- The genuine Hermite projection kernel has this simultaneous spatial derivative. -/
theorem hermiteKernel_translation_hasDerivAt
    (N : ℕ /- [definition] -/)
    (x y t : ℝ /- [definition] -/) :
    HasDerivAt (fun u => hermiteKernel N (x+u) (y+u))
      (-(Real.sqrt (N : ℝ)/2)*boundaryPair N (x+t) (y+t)) t := by
  have hd (k : Fin N) : HasDerivAt
      (fun u => hermiteMode k.val (x+u)*hermiteMode k.val (y+u))
      (pairDerivative k.val (x+t) (y+t)) t := by
    have hx := (hermiteMode_hasDerivAt k.val (x+t)).comp t
      ((hasDerivAt_id t).const_add x)
    have hy := (hermiteMode_hasDerivAt k.val (y+t)).comp t
      ((hasDerivAt_id t).const_add y)
    convert hx.mul hy using 1 <;> first | rfl | (simp [pairDerivative])
  have hh := HasDerivAt.sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin N))) => hd k)
  convert hh using 1 <;> try rfl
  · ext u
    simp [hermiteKernel]
  · have hs := Fin.sum_univ_eq_sum_range (fun k : ℕ => pairDerivative k (x+t) (y+t)) N
    exact (hs.trans (kernel_derivative_sum N (x+t) (y+t))).symm

end RMTFoundations.TracyWidom.HermiteKernelTranslation

#print axioms RMTFoundations.TracyWidom.HermiteKernelTranslation.modeSlope_upper
#print axioms RMTFoundations.TracyWidom.HermiteKernelTranslation.modeSlope_symmetric
#print axioms RMTFoundations.TracyWidom.HermiteKernelTranslation.pairDerivative
#print axioms RMTFoundations.TracyWidom.HermiteKernelTranslation.boundaryPair
#print axioms RMTFoundations.TracyWidom.HermiteKernelTranslation.pairDerivative_telescope
#print axioms RMTFoundations.TracyWidom.HermiteKernelTranslation.kernel_derivative_sum
#print axioms RMTFoundations.TracyWidom.HermiteKernelTranslation.hermiteKernel_translation_hasDerivAt
