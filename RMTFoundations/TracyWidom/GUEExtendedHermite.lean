import RMTFoundations.TracyWidom.GUEHermiteKernel
import Mathlib.Tactic

set_option autoImplicit false

namespace RMTFoundations.TracyWidom.GUEExtendedHermite

open Finset
open RMTFoundations.TracyWidom.GUEProjection

/-- The occupied finite-rank part in the probabilists' Hermite convention.
The time factor agrees with BCR2015 Section 4.1, p.46; spatial coordinates
are multiplied by sqrt(2) from that source's oscillator convention. -/
noncomputable def occupiedKernel (N : ℕ /- [definition] -/)
    (t r x y : ℝ /- [definition] -/) : ℝ :=
  ∑ k : Fin N, Real.exp ((k.val : ℝ) * (t-r)) *
    hermiteFunction k.val x * hermiteFunction k.val y

/-- Explicit symmetric OU kernel after conjugation to Lebesgue measure.
For tau < 0, q = exp(tau) lies in (0,1); the expression is the physical
Mehler kernel in the  probabilists' Hermite normalization.
No identity with its infinite Hermite series is assumed in this module. -/
noncomputable def mehlerKernel (tau x y : ℝ /- [definition] -/) : ℝ :=
  let q := Real.exp tau
  Real.exp (-((1+q^2)*(x^2+y^2)-4*q*x*y)/(4*(1-q^2))) /
    Real.sqrt (2*Real.pi*(1-q^2))

/-- Physical occupied-sum-minus-OU-subtraction expression. Identification
with the BCR unoccupied Hermite series and its determinantal probability
law remain separate obligations, not hypotheses of this definition. -/
noncomputable def extendedHermiteKernel (N : ℕ /- [definition] -/)
    (t x r y : ℝ /- [definition] -/) : ℝ :=
  occupiedKernel N t r x y - if t < r then mehlerKernel (t-r) x y else 0

lemma occupiedKernel_diagonal (N : ℕ /- [definition] -/)
    (t x y : ℝ /- [definition] -/) :
    occupiedKernel N t t x y = hermiteKernel N x y := by
  simp [occupiedKernel, hermiteKernel]

lemma extendedHermiteKernel_diagonal (N : ℕ /- [definition] -/)
    (t x y : ℝ /- [definition] -/) :
    extendedHermiteKernel N t x t y = hermiteKernel N x y := by
  simp [extendedHermiteKernel, occupiedKernel_diagonal]

lemma occupiedKernel_translation (N : ℕ /- [definition] -/)
    (t r a x y : ℝ /- [definition] -/) :
    occupiedKernel N (t+a) (r+a) x y = occupiedKernel N t r x y := by
  unfold occupiedKernel
  congr 1
  ext k
  congr 2
  ring

lemma extendedHermiteKernel_translation (N : ℕ /- [definition] -/)
    (t r a x y : ℝ /- [definition] -/) :
    extendedHermiteKernel N (t+a) x (r+a) y = extendedHermiteKernel N t x r y := by
  have hd : t+a-(r+a) = t-r := by ring
  simp only [extendedHermiteKernel, occupiedKernel_translation, hd,
    add_lt_add_iff_right]

lemma extendedHermiteKernel_later (N : ℕ /- [definition] -/)
    (t r x y : ℝ /- [definition] -/)
    (htr : r ≤ t /- [standing] -/) :
    extendedHermiteKernel N t x r y = occupiedKernel N t r x y := by
  simp [extendedHermiteKernel, not_lt.mpr htr]

lemma extendedHermiteKernel_earlier (N : ℕ /- [definition] -/)
    (t r x y : ℝ /- [definition] -/)
    (htr : t < r /- [standing] -/) :
    extendedHermiteKernel N t x r y =
      occupiedKernel N t r x y - mehlerKernel (t-r) x y := by
  simp [extendedHermiteKernel, htr]

lemma occupiedKernel_zero (t r x y : ℝ /- [definition] -/) :
    occupiedKernel 0 t r x y = 0 := by
  simp [occupiedKernel]

lemma extendedHermiteKernel_zero (t r x y : ℝ /- [definition] -/) :
    extendedHermiteKernel 0 t x r y =
      if t < r then -mehlerKernel (t-r) x y else 0 := by
  simp only [extendedHermiteKernel, occupiedKernel_zero]
  split_ifs <;> simp

lemma occupiedKernel_one (t r x y : ℝ /- [definition] -/) :
    occupiedKernel 1 t r x y = hermiteFunction 0 x * hermiteFunction 0 y := by
  simp [occupiedKernel]

lemma extendedHermiteKernel_one (t r x y : ℝ /- [definition] -/) :
    extendedHermiteKernel 1 t x r y = hermiteFunction 0 x * hermiteFunction 0 y -
      if t < r then mehlerKernel (t-r) x y else 0 := by
  rw [extendedHermiteKernel, occupiedKernel_one]

lemma occupiedKernel_spatial_symmetry (N : ℕ /- [definition] -/)
    (t r x y : ℝ /- [definition] -/) :
    occupiedKernel N t r x y = occupiedKernel N t r y x := by
  unfold occupiedKernel
  apply Finset.sum_congr rfl
  intro k hk
  ring

lemma mehlerKernel_spatial_symmetry (tau x y : ℝ /- [definition] -/) :
    mehlerKernel tau x y = mehlerKernel tau y x := by
  unfold mehlerKernel
  congr 2
  ring

lemma mehlerKernel_pos (tau x y : ℝ /- [definition] -/)
    (htau : tau < 0 /- [standing] -/) :
    0 < mehlerKernel tau x y := by
  have hq : Real.exp tau < 1 := Real.exp_lt_one_iff.mpr htau
  have hp : 0 < Real.exp tau := Real.exp_pos tau
  have hs : 0 < 1-(Real.exp tau)^2 := by nlinarith
  unfold mehlerKernel
  exact div_pos (Real.exp_pos _) (Real.sqrt_pos.2 (by positivity))

lemma extendedHermiteKernel_spatial_symmetry (N : ℕ /- [definition] -/)
    (t r x y : ℝ /- [definition] -/) :
    extendedHermiteKernel N t x r y = extendedHermiteKernel N t y r x := by
  simp only [extendedHermiteKernel, occupiedKernel_spatial_symmetry N t r x y,
    mehlerKernel_spatial_symmetry (t-r) x y]

lemma hermiteFunction_zero_pos (x : ℝ /- [definition] -/) :
    0 < hermiteFunction 0 x := by
  simp only [hermiteFunction, Polynomial.hermite_zero, map_one, one_mul]
  exact div_pos (Real.exp_pos _) (hermiteNorm_pos 0)

lemma extendedHermiteKernel_one_diagonal_pos (t x : ℝ /- [definition] -/) :
    0 < extendedHermiteKernel 1 t x t x := by
  rw [extendedHermiteKernel_one]
  simp only [lt_self_iff_false, ↓reduceIte, sub_zero]
  exact mul_pos (hermiteFunction_zero_pos x) (hermiteFunction_zero_pos x)

/-- All-binder nondegenerate example: N=1, strictly ordered distinct times,
positive physical Mehler propagator, and positive equal-time occupied mode. -/
theorem extendedHermite_joint_probe :
    ∃ (N : ℕ) (t r x y a : ℝ),
      0 < N ∧ t < r ∧ t ≠ r ∧ x ≠ y ∧ a ≠ 0 ∧
      0 < mehlerKernel (t-r) x y ∧
      0 < extendedHermiteKernel N t x t x ∧
      extendedHermiteKernel N (t+a) x (r+a) y = extendedHermiteKernel N t x r y ∧
      extendedHermiteKernel N t x t y = hermiteKernel N x y := by
  refine ⟨1, 0, 1, 0, 1, 1, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact mehlerKernel_pos (0-1) 0 1 (by norm_num)
  · exact extendedHermiteKernel_one_diagonal_pos 0 0
  · exact extendedHermiteKernel_translation 1 0 1 1 0 1
  · exact extendedHermiteKernel_diagonal 1 0 0 1

/-- A literal two-time correlation determinant of the physical N=1 kernel.
This is not an assertion identifying a Fredholm gap determinant with a probability. -/
lemma scalar_two_time_determinant (t r x y : ℝ /- [definition] -/)
    (htr : t < r /- [standing] -/) :
    Matrix.det ![![extendedHermiteKernel 1 t x t x, extendedHermiteKernel 1 t x r y],
      ![extendedHermiteKernel 1 r y t x, extendedHermiteKernel 1 r y r y]] =
      hermiteFunction 0 x * hermiteFunction 0 y * mehlerKernel (t-r) x y := by
  change Matrix.det (Matrix.of ![![extendedHermiteKernel 1 t x t x, extendedHermiteKernel 1 t x r y],
    ![extendedHermiteKernel 1 r y t x, extendedHermiteKernel 1 r y r y]]) = _
  rw [Matrix.det_fin_two]
  simp [extendedHermiteKernel_one,
    lt_self_iff_false, htr, not_lt_of_ge htr.le, ↓reduceIte, sub_zero]
  ring

/-- Nonvacuous strict positivity of the N=1 physical two-time correlation determinant. -/
lemma scalar_two_time_determinant_pos (t r x y : ℝ /- [definition] -/)
    (htr : t < r /- [standing] -/) :
    0 < Matrix.det ![![extendedHermiteKernel 1 t x t x, extendedHermiteKernel 1 t x r y],
      ![extendedHermiteKernel 1 r y t x, extendedHermiteKernel 1 r y r y]] := by
  rw [scalar_two_time_determinant t r x y htr]
  exact mul_pos (mul_pos (hermiteFunction_zero_pos x) (hermiteFunction_zero_pos y))
    (mehlerKernel_pos (t-r) x y (sub_neg.mpr htr))

/-- All-binder example for the physical two-time correlation identity and its strict sign. -/
theorem scalar_two_time_joint_probe :
    ∃ (t r x y : ℝ), t < r ∧ t ≠ r ∧ x ≠ y ∧
      0 < Matrix.det ![![extendedHermiteKernel 1 t x t x, extendedHermiteKernel 1 t x r y],
        ![extendedHermiteKernel 1 r y t x, extendedHermiteKernel 1 r y r y]] ∧
      Matrix.det ![![extendedHermiteKernel 1 t x t x, extendedHermiteKernel 1 t x r y],
        ![extendedHermiteKernel 1 r y t x, extendedHermiteKernel 1 r y r y]] =
        hermiteFunction 0 x * hermiteFunction 0 y * mehlerKernel (t-r) x y := by
  refine ⟨0, 1, 0, 1, by norm_num, by norm_num, by norm_num, ?_, ?_⟩
  · exact scalar_two_time_determinant_pos 0 1 0 1 (by norm_num)
  · exact scalar_two_time_determinant 0 1 0 1 (by norm_num)

end RMTFoundations.TracyWidom.GUEExtendedHermite

#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.occupiedKernel
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.mehlerKernel
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.extendedHermiteKernel
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.occupiedKernel_diagonal
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.extendedHermiteKernel_diagonal
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.occupiedKernel_translation
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.extendedHermiteKernel_translation
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.extendedHermiteKernel_later
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.extendedHermiteKernel_earlier
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.occupiedKernel_zero
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.extendedHermiteKernel_zero
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.occupiedKernel_one
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.extendedHermiteKernel_one
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.occupiedKernel_spatial_symmetry
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.mehlerKernel_spatial_symmetry
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.mehlerKernel_pos
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.extendedHermiteKernel_spatial_symmetry
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.hermiteFunction_zero_pos
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.extendedHermiteKernel_one_diagonal_pos
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.extendedHermite_joint_probe
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.scalar_two_time_determinant
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.scalar_two_time_determinant_pos
#print axioms RMTFoundations.TracyWidom.GUEExtendedHermite.scalar_two_time_joint_probe
