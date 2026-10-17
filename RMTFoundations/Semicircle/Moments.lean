import RMTFoundations.Stieltjes.Semicircle
import RMTFoundations.Concentration.SemicircleMoments

/-

# Joining the semicircle measure to the semicircle moments

The measure and its moments are related by integration against the density.

* `RMTFoundations.Stieltjes.Semicircle` builds the semicircle *measure*
  `semicircle = (volume.restrict (Icc (-2) 2)).withDensity (ENNReal.ofReal ∘ semicircleDensity)`
  and proves it is a probability measure carried by `[-2, 2]`.
* `RMTFoundations.Concentration.SemicircleMoments` computes the *moments* as
  bare interval integrals `semicircleMoment m = (2 π)⁻¹ ∫ x in (-2)..2, x ^ m √(4 - x ^ 2)`,
  and identifies them with the Catalan numbers.

## What is proved here

* `integral_semicircle_eq_setIntegral` and `integral_semicircle_eq_intervalIntegral`
  — the change of measure, valid for any Banach-space-valued integrand:
  `∫ x, g x ∂semicircle = ∫ x in (-2)..2, semicircleDensity x • g x`.
  This is the whole content; everything below is a specialisation.
* `integral_pow_semicircle` — **the join**:
  `∫ x, x ^ m ∂semicircle = semicircleMoment m` for every `m`.
* `integral_pow_two_mul_semicircle` — `∫ x, x ^ (2 k) ∂semicircle = catalan k`.
* `integral_pow_odd_semicircle` — `∫ x, x ^ (2 m + 1) ∂semicircle = 0`.
* `integral_id_semicircle` — mean zero, `∫ x, x ∂semicircle = 0`.
* `integral_sq_semicircle` — unit second moment, `∫ x, x ^ 2 ∂semicircle = 1`.
  Since the mean vanishes this is the variance, and it is `catalan 1 = 1`.
* `integrable_semicircle_of_continuous`, `integrable_pow_semicircle` — the
  integrability side conditions, as named reusable lemmas.
* `stieltjes_semicircle_eq_intervalIntegral` — the Stieltjes transform of the
  measure rewritten as an elementary interval integral of the density against
  the kernel `(x - z)⁻¹`.

## What is NOT proved here
-/

namespace RMTFoundations.Semicircle

open MeasureTheory

open RMTFoundations.Stieltjes (semicircle semicircleDensity semicircleDensity_nonneg
  continuous_semicircleDensity)

variable {E : Type* /- [definition] -/ } [NormedAddCommGroup E /- [definition] -/ ] [NormedSpace ℝ E /- [definition] -/ ]

/-! ### The density as an `ℝ≥0∞`-valued weight -/

/-- The `ℝ≥0∞`-valued density used by `withDensity` is measurable. -/
theorem measurable_ofReal_semicircleDensity :
    Measurable fun x : ℝ => ENNReal.ofReal (semicircleDensity x) :=
  continuous_semicircleDensity.measurable.ennreal_ofReal

/-- The `ℝ≥0∞`-valued density is everywhere finite, so `withDensity` may be
undone without an almost-everywhere caveat. -/
theorem ofReal_semicircleDensity_ne_top (x : ℝ /- [definition] -/ ) :
    ENNReal.ofReal (semicircleDensity x) ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem ofReal_semicircleDensity_lt_top (x : ℝ /- [definition] -/ ) :
    ENNReal.ofReal (semicircleDensity x) < ⊤ :=
  ENNReal.ofReal_lt_top

/-- Undoing `ENNReal.ofReal`: the density is nonnegative, so no information is
lost in `withDensity`. -/
theorem toReal_ofReal_semicircleDensity (x : ℝ /- [definition] -/ ) :
    (ENNReal.ofReal (semicircleDensity x)).toReal = semicircleDensity x :=
  ENNReal.toReal_ofReal (semicircleDensity_nonneg x)

/-! ### The change of measure -/

/-- Integration against the semicircle measure is integration of
`semicircleDensity • g` over `[-2, 2]` for Lebesgue measure. -/
theorem integral_semicircle_eq_setIntegral (g : ℝ → E /- [definition] -/ ) :
    ∫ x, g x ∂semicircle = ∫ x in Set.Icc (-2 : ℝ) 2, semicircleDensity x • g x := by
  rw [RMTFoundations.Stieltjes.semicircle,
    integral_withDensity_eq_integral_toReal_smul measurable_ofReal_semicircleDensity
      (Filter.Eventually.of_forall ofReal_semicircleDensity_lt_top) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (ENNReal.ofReal (semicircleDensity x)).toReal • g x = semicircleDensity x • g x
  rw [toReal_ofReal_semicircleDensity]

/-- The same, as an interval integral: this is the bridge between the
measure-theoretic and the elementary calculus formulations. -/
theorem integral_semicircle_eq_intervalIntegral (g : ℝ → E /- [definition] -/ ) :
    ∫ x, g x ∂semicircle = ∫ x in (-2 : ℝ)..2, semicircleDensity x • g x := by
  rw [integral_semicircle_eq_setIntegral, MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)]

/-! ### Integrability side conditions -/

/-- Every continuous function is `semicircle`-integrable: the measure is
compactly supported with a bounded density. -/
theorem integrable_semicircle_of_continuous {g : ℝ → E /- [definition] -/ } (hg : Continuous g /- [standing] -/ ) :
    Integrable g semicircle := by
  rw [RMTFoundations.Stieltjes.semicircle,
    integrable_withDensity_iff_integrable_smul' measurable_ofReal_semicircleDensity
      (Filter.Eventually.of_forall ofReal_semicircleDensity_lt_top)]
  have hcont : IntegrableOn (fun x : ℝ => semicircleDensity x • g x)
      (Set.Icc (-2 : ℝ) 2) volume :=
    (continuous_semicircleDensity.smul hg).integrableOn_Icc
  refine hcont.congr (Filter.Eventually.of_forall fun x => ?_)
  show semicircleDensity x • g x = (ENNReal.ofReal (semicircleDensity x)).toReal • g x
  rw [toReal_ofReal_semicircleDensity]

/-- The monomials are `semicircle`-integrable, so every moment below is the
integral of an integrable function rather than a junk value. -/
theorem integrable_pow_semicircle (m : ℕ /- [definition] -/ ) :
    Integrable (fun x : ℝ => x ^ m) semicircle :=
  integrable_semicircle_of_continuous (continuous_pow m)

/-- The identity is `semicircle`-integrable. -/
theorem integrable_id_semicircle : Integrable (fun x : ℝ => x) semicircle :=
  integrable_semicircle_of_continuous continuous_id

/-- The Stieltjes kernel is `semicircle`-integrable for `z` off the real axis;
this is the finite-measure statement specialised. -/
theorem integrable_stieltjesKernel_semicircle {z : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ ) :
    Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) semicircle :=
  RMTFoundations.Stieltjes.integrable_stieltjesKernel semicircle hz



/-- The moments of the semicircle measure agree with the explicitly computed semicircle moments. -/
theorem integral_pow_semicircle (m : ℕ /- [definition] -/ ) :
    ∫ x, x ^ m ∂semicircle = Concentration.semicircleMoment m := by
  rw [integral_semicircle_eq_intervalIntegral]
  have hpt : ∀ x : ℝ, semicircleDensity x • x ^ m
      = (2 * Real.pi)⁻¹ * (x ^ m * Real.sqrt (4 - x ^ 2)) := by
    intro x
    rw [smul_eq_mul, RMTFoundations.Stieltjes.semicircleDensity]
    ring
  rw [intervalIntegral.integral_congr (fun x _ => hpt x),
    intervalIntegral.integral_const_mul, Concentration.semicircleMoment, one_div]

/-- **The even moments of the semicircle measure are the Catalan numbers.** -/
theorem integral_pow_two_mul_semicircle (k : ℕ /- [definition] -/ ) :
    ∫ x, x ^ (2 * k) ∂semicircle = catalan k := by
  rw [integral_pow_semicircle, Concentration.semicircleMoment_two_mul]

/-- **The odd moments of the semicircle measure vanish.** -/
theorem integral_pow_odd_semicircle (m : ℕ /- [definition] -/ ) :
    ∫ x, x ^ (2 * m + 1) ∂semicircle = 0 := by
  rw [integral_pow_semicircle, Concentration.semicircleMoment_odd]

/-- **Mean zero.** -/
theorem integral_id_semicircle : ∫ x, x ∂semicircle = 0 := by
  have h := integral_pow_odd_semicircle 0
  rw [Nat.mul_zero, Nat.zero_add] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x : ℝ => (pow_one x).symm)

/-- **Unit second moment**, hence (with `integral_id_semicircle`) unit variance:
`catalan 1 = 1`. -/
theorem integral_sq_semicircle : ∫ x, x ^ 2 ∂semicircle = 1 := by
  have h := integral_pow_two_mul_semicircle 1
  rw [Nat.mul_one, catalan_one, Nat.cast_one] at h
  exact h

/-- The fourth moment is `catalan 2 = 2`. -/
theorem integral_pow_four_semicircle : ∫ x, x ^ 4 ∂semicircle = 2 := by
  have h := integral_pow_two_mul_semicircle 2
  rw [show 2 * 2 = 4 from rfl, catalan_two] at h
  rw [h]
  norm_num

/-! ### The Stieltjes transform, moved onto `[-2, 2]`

This is a change of variables only.  The transform is still not evaluated. -/

/-- The Stieltjes transform of the semicircle measure as an interval integral
against the explicit density.  No closed form is claimed. -/
theorem stieltjes_semicircle_eq_intervalIntegral (z : ℂ /- [definition] -/ ) :
    RMTFoundations.Stieltjes.stieltjes semicircle z
      = ∫ x in (-2 : ℝ)..2, (semicircleDensity x : ℂ) * ((x : ℂ) - z)⁻¹ := by
  rw [RMTFoundations.Stieltjes.stieltjes_apply,
    integral_semicircle_eq_intervalIntegral (fun x : ℝ => ((x : ℂ) - z)⁻¹)]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [Complex.real_smul]

end RMTFoundations.Semicircle

#print axioms RMTFoundations.Semicircle.measurable_ofReal_semicircleDensity
#print axioms RMTFoundations.Semicircle.ofReal_semicircleDensity_ne_top
#print axioms RMTFoundations.Semicircle.ofReal_semicircleDensity_lt_top
#print axioms RMTFoundations.Semicircle.toReal_ofReal_semicircleDensity
#print axioms RMTFoundations.Semicircle.integral_semicircle_eq_setIntegral
#print axioms RMTFoundations.Semicircle.integral_semicircle_eq_intervalIntegral
#print axioms RMTFoundations.Semicircle.integrable_semicircle_of_continuous
#print axioms RMTFoundations.Semicircle.integrable_pow_semicircle
#print axioms RMTFoundations.Semicircle.integrable_id_semicircle
#print axioms RMTFoundations.Semicircle.integrable_stieltjesKernel_semicircle
#print axioms RMTFoundations.Semicircle.integral_pow_semicircle
#print axioms RMTFoundations.Semicircle.integral_pow_two_mul_semicircle
#print axioms RMTFoundations.Semicircle.integral_pow_odd_semicircle
#print axioms RMTFoundations.Semicircle.integral_id_semicircle
#print axioms RMTFoundations.Semicircle.integral_sq_semicircle
#print axioms RMTFoundations.Semicircle.integral_pow_four_semicircle
#print axioms RMTFoundations.Semicircle.stieltjes_semicircle_eq_intervalIntegral
