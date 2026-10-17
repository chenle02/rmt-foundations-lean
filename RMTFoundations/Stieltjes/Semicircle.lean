import RMTFoundations.Stieltjes.HalfPlane
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The semicircle law as an explicit measure

## What is proved here

* `semicircleDensity x = (2 * π)⁻¹ * √(4 - x ^ 2)`, continuous and nonnegative
  everywhere (it vanishes off `[-2, 2]` because `Real.sqrt` of a negative number
  is `0`, but we still cut the measure down to `[-2, 2]` explicitly).
* `semicircle`, the measure `(volume.restrict (Icc (-2) 2)).withDensity …`.
* `integral_sqrt_four_sub_sq`: `∫ x in (-2)..2, √(4 - x ^ 2) = 2 * π`, by the
  substitution `x = 2 u` from mathlib's `integral_sqrt_one_sub_sq`.
* `semicircle_univ` and the `IsProbabilityMeasure` instance: **total mass 1.**
* `semicircle_compl_Icc`: the measure is carried by `[-2, 2]`.
* `im_stieltjes_semicircle_pos` and `norm_stieltjes_semicircle_le`: the general
  half-plane estimates specialised to this measure.

## What is NOT proved here

* **The value of the Stieltjes transform of the semicircle law is not
  computed.**  In particular the quadratic identity
  `m ^ 2 + z * m + 1 = 0` is *not* established for `stieltjes semicircle`.
  What is available is the algebraic statement in
  `RMTFoundations.Stieltjes.SelfConsistent`
  (`semicircle_quadratic_of_selfConsistent`), which derives the quadratic from
  the fixed-point equation for any function satisfying it; joining the two
  requires evaluating `∫ (x - z)⁻¹ dμ_sc`, a contour-integral computation not
  attempted anywhere in this package.
* No moment computation (the Catalan numbers do not appear), no statement that
  `μ.support = Icc (-2) 2` (only that the complement is null), and no
  free-probability characterisation.
-/

namespace RMTFoundations.Stieltjes

open MeasureTheory

/-- The semicircle density `(2π)⁻¹ √(4 - x²)`.  Outside `[-2, 2]` this is `0`
by the `Real.sqrt` junk-value convention, but the measure below is cut down to
`[-2, 2]` explicitly anyway. -/
noncomputable def semicircleDensity (x : ℝ /- [definition] -/ ) : ℝ :=
  (2 * Real.pi)⁻¹ * Real.sqrt (4 - x ^ 2)

theorem two_pi_pos : (0 : ℝ) < 2 * Real.pi := by
  have := Real.pi_pos
  linarith

theorem continuous_semicircleDensity : Continuous semicircleDensity :=
  continuous_const.mul
    (Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2)))

theorem semicircleDensity_nonneg (x : ℝ /- [definition] -/ ) : 0 ≤ semicircleDensity x :=
  mul_nonneg (le_of_lt (inv_pos.mpr two_pi_pos)) (Real.sqrt_nonneg _)

/-- `∫_{-2}^{2} √(4 - x²) dx = 2π`, by rescaling mathlib's
`integral_sqrt_one_sub_sq`. -/
theorem integral_sqrt_four_sub_sq :
    ∫ x in (-2 : ℝ)..2, Real.sqrt (4 - x ^ 2) = 2 * Real.pi := by
  have hsub : ∀ x : ℝ,
      Real.sqrt (4 - x ^ 2) = 2 * Real.sqrt (1 - (x / 2) ^ 2) := by
    intro x
    have h : (4 : ℝ) - x ^ 2 = 4 * (1 - (x / 2) ^ 2) := by ring
    rw [h, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  calc ∫ x in (-2 : ℝ)..2, Real.sqrt (4 - x ^ 2)
      = ∫ x in (-2 : ℝ)..2, 2 * Real.sqrt (1 - (x / 2) ^ 2) :=
        intervalIntegral.integral_congr fun x _ => hsub x
    _ = 2 * ∫ x in (-2 : ℝ)..2, Real.sqrt (1 - (x / 2) ^ 2) :=
        intervalIntegral.integral_const_mul 2 _
    _ = 2 * ((2 : ℝ) • ∫ x in (-1 : ℝ)..(1 : ℝ), Real.sqrt (1 - x ^ 2)) := by
        rw [intervalIntegral.integral_comp_div
          (fun u : ℝ => Real.sqrt (1 - u ^ 2)) two_ne_zero]
        norm_num
    _ = 2 * Real.pi := by
        rw [integral_sqrt_one_sub_sq, smul_eq_mul]
        ring

/-- The semicircle law on `[-2, 2]`. -/
noncomputable def semicircle : Measure ℝ :=
  (volume.restrict (Set.Icc (-2 : ℝ) 2)).withDensity
    fun x => ENNReal.ofReal (semicircleDensity x)

theorem integrableOn_semicircleDensity :
    IntegrableOn semicircleDensity (Set.Icc (-2 : ℝ) 2) volume :=
  continuous_semicircleDensity.integrableOn_Icc

theorem integral_semicircleDensity :
    ∫ x in Set.Icc (-2 : ℝ) 2, semicircleDensity x = 1 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]
  show ∫ x in (-2 : ℝ)..2, (2 * Real.pi)⁻¹ * Real.sqrt (4 - x ^ 2) = 1
  rw [intervalIntegral.integral_const_mul, integral_sqrt_four_sub_sq,
    inv_mul_cancel₀ two_pi_pos.ne']

/-- **The semicircle law is a probability measure.** -/
theorem semicircle_univ : semicircle Set.univ = 1 := by
  rw [semicircle, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal integrableOn_semicircleDensity
      (Filter.Eventually.of_forall semicircleDensity_nonneg),
    integral_semicircleDensity, ENNReal.ofReal_one]

instance : IsProbabilityMeasure semicircle := ⟨semicircle_univ⟩

/-- The semicircle law is carried by `[-2, 2]`. -/
theorem semicircle_compl_Icc : semicircle (Set.Icc (-2 : ℝ) 2)ᶜ = 0 := by
  rw [semicircle, withDensity_apply _ measurableSet_Icc.compl,
    Measure.restrict_restrict measurableSet_Icc.compl, Set.compl_inter_self,
    Measure.restrict_empty, lintegral_zero_measure]

/-! ### The general half-plane estimates, specialised -/

theorem im_stieltjes_semicircle_pos {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) :
    0 < (stieltjes semicircle z).im :=
  im_stieltjes_pos semicircle (IsProbabilityMeasure.ne_zero semicircle) hz

theorem norm_stieltjes_semicircle_le {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) :
    ‖stieltjes semicircle z‖ ≤ 1 / z.im := by
  have h := norm_stieltjes_le semicircle hz
  rwa [probReal_univ] at h

end RMTFoundations.Stieltjes

#print axioms RMTFoundations.Stieltjes.semicircleDensity
#print axioms RMTFoundations.Stieltjes.two_pi_pos
#print axioms RMTFoundations.Stieltjes.continuous_semicircleDensity
#print axioms RMTFoundations.Stieltjes.semicircleDensity_nonneg
#print axioms RMTFoundations.Stieltjes.integral_sqrt_four_sub_sq
#print axioms RMTFoundations.Stieltjes.semicircle
#print axioms RMTFoundations.Stieltjes.integrableOn_semicircleDensity
#print axioms RMTFoundations.Stieltjes.integral_semicircleDensity
#print axioms RMTFoundations.Stieltjes.semicircle_univ
#print axioms RMTFoundations.Stieltjes.semicircle_compl_Icc
#print axioms RMTFoundations.Stieltjes.im_stieltjes_semicircle_pos
#print axioms RMTFoundations.Stieltjes.norm_stieltjes_semicircle_le
