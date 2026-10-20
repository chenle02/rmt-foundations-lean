import RMTFoundations.TracyWidom.HermiteCauchyBound
import RMTFoundations.TracyWidom.ContourRadiusReadiness
import RMTFoundations.TracyWidom.ContourPreviousRatio
import RMTFoundations.TracyWidom.ContourRadialEnvelope
import RMTFoundations.TracyWidom.ContourNormalization
import RMTFoundations.TracyWidom.HermiteSquareNormalization
import RMTFoundations.TracyWidom.HermiteFiniteEnvelope
import Mathlib.Tactic
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.HermiteUniformTail
open Real
open RMTFoundations.TracyWidom.GUEHermite RMTFoundations.TracyWidom.HermiteEdgeODE
open RMTFoundations.TracyWidom.HermiteEdgeScale RMTFoundations.TracyWidom.HermiteEdgeReduction
open RMTFoundations.TracyWidom.HermiteTailComparison RMTFoundations.TracyWidom.HermiteFiniteEnvelope
open RMTFoundations.TracyWidom.ContourEdgePowers RMTFoundations.TracyWidom.ContourRadialLog
open RMTFoundations.TracyWidom.ContourRadiusReadiness RMTFoundations.TracyWidom.ContourPreviousRatio
open RMTFoundations.TracyWidom.ContourRadialEnvelope RMTFoundations.TracyWidom.ContourNormalization
open RMTFoundations.TracyWidom.HermiteCauchyBound RMTFoundations.TracyWidom.HermiteSquareNormalization
/-- Both modes use the SAME N-dependent center, scale and amplitude. -/
theorem large_dimension_square_tail (N : ℕ /- [definition] -/)
    (s y : ℝ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (hd : edgeDelta N ≤ (1/2:ℝ) /- [standing] -/)
    (hs : edgeDelta N*|s| ≤ 1 /- [standing] -/)
    (hy : s ≤ y /- [standing] -/) :
    (edgeMode N y)^2 ≤ (2*exp 1/sqrt (2*Real.pi))*
      exp (2*((2/3:ℝ)-s))*exp (-(y-s)) ∧
    (previousMode N y)^2 ≤ (2*exp 1/sqrt (2*Real.pi))*
      exp (2*((2/3:ℝ)-s))*exp (-(y-s)) := by
  let d := edgeDelta N
  let r := sqrt (N:ℝ)*(1-d)
  let x := sqrt (N:ℝ)*(2+d^2*y)
  let h := (N:ℝ)*d/2
  have H := radius_readiness N s y hN hd hs hy
  have hr : 0 < r := H.1
  have hh : 0 < h := H.2.1
  have hg : h ≤ r*(x-2*r) := H.2.2.2
  have hd1 : d < 1 := by dsimp [d];linarith
  have hx : edgePoint N y=x := by
    rw [edgePoint,edgeScale_delta N hN]
    dsimp [x,d]
    ring
  have hcur := normalized_coefficient_bound N (edgeAmplitude N) r h x (hpoly N x)
    hr hh (hermite_cauchy_bound N x r h hr hh hg)
  have hprev := normalized_coefficient_bound (N-1) (edgeAmplitude N) r h x (hpoly (N-1) x)
    hr hh (hermite_cauchy_bound (N-1) x r h hr hh hg)
  have hecur : (edgeMode N y)^2 =
      (edgeAmplitude N)^2*(hpoly N x)^2*exp (-x^2/2)/(sqrt (2*Real.pi)*(N.factorial:ℝ)) := by
    have he : edgeMode N y=edgeAmplitude N*hermiteMode N x := by
      change edgeAmplitude N*hermiteMode N (edgePoint N y)=_
      rw [hx]
    rw [he,scaled_hermiteMode_square]
  have heprev : (previousMode N y)^2 =
      (edgeAmplitude N)^2*(hpoly (N-1) x)^2*exp (-x^2/2)/
        (sqrt (2*Real.pi)*((N-1).factorial:ℝ)) := by
    have he : previousMode N y=edgeAmplitude N*hermiteMode (N-1) x := by
      change edgeAmplitude N*hermiteMode (N-1) (edgePoint N y)=_
      rw [hx]
    rw [he,scaled_hermiteMode_square]
  have hmain : ((edgeAmplitude N)^2*exp (2*x*r-r^2-x^2/2)/(sqrt (2*Real.pi)*h))*
      ((N.factorial:ℝ)/r^(2*N)) ≤
      (2*exp 1/sqrt (2*Real.pi))*exp (2*radial (N:ℝ) d y) :=
    radial_normalization_bound N hN y hd1
  have hratio := previous_factorial_le N hN d (edgeDelta_pos N hN).le hd1
  have hprev' := hprev.trans (mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ (edgeAmplitude N)^2*exp (2*x*r-r^2-x^2/2)/(sqrt (2*Real.pi)*h) by positivity))
  have hrad := mul_le_mul_of_nonneg_left
    (radial_envelope N s y hN hd H.2.2.1 hy)
    (show 0 ≤ 2*exp 1/sqrt (2*Real.pi) by positivity)
  rw [hecur,heprev]
  exact ⟨hcur.trans (hmain.trans (by simpa only [mul_assoc] using hrad)),
    hprev'.trans (hmain.trans (by simpa only [mul_assoc] using hrad))⟩
noncomputable def contourConstant (s : ℝ /- [definition] -/) : ℝ :=
  sqrt (2*exp 1/sqrt (2*Real.pi))*exp ((2/3:ℝ)-s)
lemma contourConstant_pos (s : ℝ /- [definition] -/) : 0 < contourConstant s := by
  dsimp [contourConstant]
  positivity
lemma contourConstant_square (s y : ℝ /- [definition] -/) :
    (contourConstant s*exp (-(1/2:ℝ)*(y-s)))^2 =
      (2*exp 1/sqrt (2*Real.pi))*exp (2*((2/3:ℝ)-s))*exp (-(y-s)) := by
  rw [mul_pow,contourConstant,mul_pow,sq_sqrt (by positivity),←exp_nat_mul,←exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  congr 1
  congr 1
  ring
/-- The Cauchy estimate produces a common absolute envelope at all sufficiently large dimensions. -/
theorem large_dimension_tail (N : ℕ /- [definition] -/)
    (s y : ℝ /- [definition] -/)
    (hN : 0 < N /- [standing] -/)
    (hd : edgeDelta N ≤ (1/2:ℝ) /- [standing] -/)
    (hs : edgeDelta N*|s| ≤ 1 /- [standing] -/)
    (hy : s ≤ y /- [standing] -/) :
    |edgeMode N y| ≤ contourConstant s*exp (-(1/2:ℝ)*(y-s)) ∧
    |previousMode N y| ≤ contourConstant s*exp (-(1/2:ℝ)*(y-s)) := by
  have H := large_dimension_square_tail N s y hN hd hs hy
  have hB : 0 ≤ contourConstant s*exp (-(1/2:ℝ)*(y-s)) :=
    mul_nonneg (contourConstant_pos s).le (exp_pos _).le
  constructor
  · apply (sq_le_sq₀ (abs_nonneg _) hB).mp
    rw [sq_abs,contourConstant_square]
    exact H.1
  · apply (sq_le_sq₀ (abs_nonneg _) hB).mp
    rw [sq_abs,contourConstant_square]
    exact H.2
/-- Uniform-in-N exponential tails of the literal neighboring scaled Hermite functions.
The endpoint is arbitrary; finite dimensions are included, not silently excluded. -/
theorem uniform_halfline_tail (s : ℝ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ y : ℝ, s ≤ y →
      |edgeMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) ∧
      |previousMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) := by
  obtain ⟨K,hK,h⟩ := endpoint_threshold s
  obtain ⟨B,hB,hb⟩ := finite_dimensions_envelope K s
  let C := max B (contourConstant s)
  refine ⟨C,hB.trans_le (le_max_left _ _),?_⟩
  intro N hN y hy
  by_cases hNK : K ≤ N
  · have H := large_dimension_tail N s y hN (h N hNK).2.1 (h N hNK).2.2 hy
    exact ⟨H.1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le),
      H.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (exp_pos _).le)⟩
  · have H := hb N hN (by omega) y hy
    exact ⟨H.1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le),
      H.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (exp_pos _).le)⟩
/-- Every endpoint and arbitrarily large positive dimensions satisfy the complete tail interface. -/
theorem uniform_tail_joint_probe (s : ℝ /- [definition] -/)
    (k : ℕ /- [definition] -/) :
    ∃ C : ℝ, 0 < C ∧ (∀ N : ℕ, 0 < N → ∀ y : ℝ, s ≤ y →
      |edgeMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s)) ∧
      |previousMode N y| ≤ C*exp (-(1/2:ℝ)*(y-s))) ∧
      ∃ N : ℕ, k < N ∧ 0 < N ∧ Polynomial.hermite N ≠ 0 := by
  obtain ⟨C,hC,h⟩ := uniform_halfline_tail s
  exact ⟨C,hC,h,k+1,by omega,by omega,(Polynomial.hermite_monic (k+1)).ne_zero⟩
/-- All readiness hypotheses of both large-dimension theorems hold jointly on the actual family. -/
theorem large_dimension_joint_probe (s : ℝ /- [definition] -/)
    (k : ℕ /- [definition] -/) :
    ∃ N : ℕ, k < N ∧ 0 < N ∧ edgeDelta N ≤ (1/2:ℝ) ∧ edgeDelta N*|s| ≤ 1 ∧
      ∀ y : ℝ, s ≤ y →
      |edgeMode N y| ≤ contourConstant s*exp (-(1/2:ℝ)*(y-s)) ∧
      |previousMode N y| ≤ contourConstant s*exp (-(1/2:ℝ)*(y-s)) := by
  obtain ⟨K,hK,h⟩ := endpoint_threshold s
  let N := max K (k+1)
  have hKN : K ≤ N := le_max_left _ _
  have hn : 0 < N := by omega
  exact ⟨N,by dsimp [N];omega,hn,(h N hKN).2.1,(h N hKN).2.2,
    fun y hy => large_dimension_tail N s y hn (h N hKN).2.1 (h N hKN).2.2 hy⟩
end RMTFoundations.TracyWidom.HermiteUniformTail

#print axioms RMTFoundations.TracyWidom.HermiteUniformTail.large_dimension_square_tail
#print axioms RMTFoundations.TracyWidom.HermiteUniformTail.contourConstant
#print axioms RMTFoundations.TracyWidom.HermiteUniformTail.contourConstant_pos
#print axioms RMTFoundations.TracyWidom.HermiteUniformTail.contourConstant_square
#print axioms RMTFoundations.TracyWidom.HermiteUniformTail.large_dimension_tail
#print axioms RMTFoundations.TracyWidom.HermiteUniformTail.uniform_halfline_tail
#print axioms RMTFoundations.TracyWidom.HermiteUniformTail.uniform_tail_joint_probe
#print axioms RMTFoundations.TracyWidom.HermiteUniformTail.large_dimension_joint_probe
