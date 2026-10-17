import Mathlib.Analysis.Complex.Basic

/-!
Scalar Stieltjes self-consistency and semicircle identities.
-/

namespace RMTFoundations.Stieltjes

/-! ### Fixed-point form versus quadratic form -/

/-- If `z ≠ 0`, a solution of the fixed-point equation really does invert
`-z + a * m`; in particular `-z + a * m ≠ 0`. -/
theorem selfConsistent_mul_eq_one {a z m : ℂ /- [definition] -/ } (hz : z ≠ 0 /- [standing] -/ )
    (h : m = (-z + a * m)⁻¹ /- [standing] -/ ) : m * (-z + a * m) = 1 := by
  rcases eq_or_ne (-z + a * m) 0 with hw | hw
  · exfalso
    rw [hw, inv_zero] at h
    rw [h, mul_zero, add_zero, neg_eq_zero] at hw
    exact hz hw
  · nth_rewrite 1 [h]
    exact inv_mul_cancel₀ hw

/-- The fixed-point equation implies the quadratic. -/
theorem quadratic_of_selfConsistent {a z m : ℂ /- [definition] -/ } (hz : z ≠ 0 /- [standing] -/ )
    (h : m = (-z + a * m)⁻¹ /- [standing] -/ ) : a * m ^ 2 - z * m - 1 = 0 := by
  have h' := selfConsistent_mul_eq_one hz h
  linear_combination h'

/-- The quadratic implies the fixed-point equation.  No hypothesis on `z` is
needed in this direction. -/
theorem selfConsistent_of_quadratic {a z m : ℂ /- [definition] -/ }
    (h : a * m ^ 2 - z * m - 1 = 0 /- [standing] -/ ) : m = (-z + a * m)⁻¹ := by
  have hw : -z + a * m ≠ 0 := by
    intro hw
    apply (one_ne_zero : (1 : ℂ) ≠ 0)
    linear_combination -h + m * hw
  have hm : m * (-z + a * m) = 1 := by linear_combination h
  calc m = m * ((-z + a * m) * (-z + a * m)⁻¹) := by rw [mul_inv_cancel₀ hw, mul_one]
    _ = m * (-z + a * m) * (-z + a * m)⁻¹ := by rw [mul_assoc]
    _ = (-z + a * m)⁻¹ := by rw [hm, one_mul]

/-! ### The semicircle specialisation `a = -1` -/

/-- The quadratic identity `m ^ 2 + z * m + 1 = 0` for any `m` solving the
semicircle fixed-point equation `m = (-z - m)⁻¹`. -/
theorem semicircle_quadratic_of_selfConsistent {z m : ℂ /- [definition] -/ } (hz : z ≠ 0 /- [standing] -/ )
    (h : m = (-z - m)⁻¹ /- [standing] -/ ) : m ^ 2 + z * m + 1 = 0 := by
  have e : -z + (-1 : ℂ) * m = -z - m := by ring
  have h' : m = (-z + (-1 : ℂ) * m)⁻¹ := by rw [e]; exact h
  have := quadratic_of_selfConsistent (a := (-1 : ℂ)) hz h'
  linear_combination -this

/-- Conversely, the semicircle quadratic forces the fixed-point equation. -/
theorem selfConsistent_of_semicircle_quadratic {z m : ℂ /- [definition] -/ }
    (h : m ^ 2 + z * m + 1 = 0 /- [standing] -/ ) : m = (-z - m)⁻¹ := by
  have h' : (-1 : ℂ) * m ^ 2 - z * m - 1 = 0 := by linear_combination -h
  have h'' := selfConsistent_of_quadratic h'
  have e : -z - m = -z + (-1 : ℂ) * m := by ring
  rw [e]
  exact h''

/-! ### Uniqueness -/

/-- Exact dichotomy for two solutions of the quadratic. -/
theorem eq_or_sum_eq_of_quadratic {a z m₁ m₂ : ℂ /- [definition] -/ }
    (h₁ : a * m₁ ^ 2 - z * m₁ - 1 = 0 /- [standing] -/ ) (h₂ : a * m₂ ^ 2 - z * m₂ - 1 = 0 /- [standing] -/ ) :
    m₁ = m₂ ∨ a * (m₁ + m₂) = z := by
  have key : (m₁ - m₂) * (a * (m₁ + m₂) - z) = 0 := by linear_combination h₁ - h₂
  rcases mul_eq_zero.mp key with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-- Uniqueness of a solution with positive imaginary part, for real negative
`a` and `z` in the open upper half-plane.  The negativity of `a` is essential:
see the module docstring for the counterexample at `a = 1`. -/
theorem eq_of_quadratic_of_im_pos {a : ℝ /- [definition] -/ } (ha : a < 0 /- [standing] -/ ) {z m₁ m₂ : ℂ /- [definition] -/ }
    (hz : 0 < z.im /- [standing] -/ ) (hm₁ : 0 < m₁.im /- [standing] -/ ) (hm₂ : 0 < m₂.im /- [standing] -/ )
    (h₁ : (a : ℂ) * m₁ ^ 2 - z * m₁ - 1 = 0 /- [standing] -/ )
    (h₂ : (a : ℂ) * m₂ ^ 2 - z * m₂ - 1 = 0 /- [standing] -/ ) : m₁ = m₂ := by
  rcases eq_or_sum_eq_of_quadratic h₁ h₂ with h | h
  · exact h
  · exfalso
    have him : a * (m₁ + m₂).im = z.im := by
      rw [← Complex.im_ofReal_mul, h]
    rw [Complex.add_im] at him
    nlinarith

/-- Uniqueness for the fixed-point form, for real negative `a`. -/
theorem eq_of_selfConsistent_of_im_pos {a : ℝ /- [definition] -/ } (ha : a < 0 /- [standing] -/ ) {z m₁ m₂ : ℂ /- [definition] -/ }
    (hz : 0 < z.im /- [standing] -/ ) (hm₁ : 0 < m₁.im /- [standing] -/ ) (hm₂ : 0 < m₂.im /- [standing] -/ )
    (h₁ : m₁ = (-z + (a : ℂ) * m₁)⁻¹ /- [standing] -/ ) (h₂ : m₂ = (-z + (a : ℂ) * m₂)⁻¹ /- [standing] -/ ) :
    m₁ = m₂ := by
  have hzne : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hz
    exact lt_irrefl 0 hz
  exact eq_of_quadratic_of_im_pos ha hz hm₁ hm₂
    (quadratic_of_selfConsistent hzne h₁) (quadratic_of_selfConsistent hzne h₂)

/-- Uniqueness for the semicircle quadratic `m ^ 2 + z * m + 1 = 0` in the open
upper half-plane. -/
theorem eq_of_semicircle_quadratic_of_im_pos {z m₁ m₂ : ℂ /- [definition] -/ } (hz : 0 < z.im /- [standing] -/ )
    (hm₁ : 0 < m₁.im /- [standing] -/ ) (hm₂ : 0 < m₂.im /- [standing] -/ )
    (h₁ : m₁ ^ 2 + z * m₁ + 1 = 0 /- [standing] -/ ) (h₂ : m₂ ^ 2 + z * m₂ + 1 = 0 /- [standing] -/ ) : m₁ = m₂ := by
  have hc : ((-1 : ℝ) : ℂ) = -1 := by rw [Complex.ofReal_neg, Complex.ofReal_one]
  refine eq_of_quadratic_of_im_pos (a := (-1 : ℝ)) (by norm_num) hz hm₁ hm₂ ?_ ?_
  · rw [hc]; linear_combination -h₁
  · rw [hc]; linear_combination -h₂

/-! ### Stability -/

/-- **The stability identity.**  Let `uᵢ` invert `-z + a * mᵢ` and let
`rᵢ = mᵢ - uᵢ` be the residual by which `mᵢ` fails to solve the self-consistent
equation.  Then `(m₁ - m₂) * (1 + a * u₁ * u₂) = r₁ - r₂` exactly.  Nothing is
assumed small; this is an algebraic identity, and it is the source of every
quantitative bound below. -/
theorem sub_mul_one_add_mul_eq_sub {a z m₁ m₂ u₁ u₂ r₁ r₂ : ℂ /- [definition] -/ }
    (hu₁ : u₁ * (-z + a * m₁) = 1 /- [standing] -/ ) (hu₂ : u₂ * (-z + a * m₂) = 1 /- [standing] -/ )
    (hm₁ : m₁ = u₁ + r₁ /- [standing] -/ ) (hm₂ : m₂ = u₂ + r₂ /- [standing] -/ ) :
    (m₁ - m₂) * (1 + a * u₁ * u₂) = r₁ - r₂ := by
  have key : u₁ - u₂ = a * u₁ * u₂ * (m₂ - m₁) := by
    linear_combination u₂ * hu₁ - u₁ * hu₂
  linear_combination key + hm₁ - hm₂

/-- Uniqueness of exact solutions, directly from the stability identity: two
solutions coincide unless the stability factor `1 + a * m₁ * m₂` vanishes. -/
theorem eq_of_selfConsistent_of_one_add_ne_zero {a z m₁ m₂ : ℂ /- [definition] -/ } (hz : z ≠ 0 /- [standing] -/ )
    (h₁ : m₁ = (-z + a * m₁)⁻¹ /- [standing] -/ ) (h₂ : m₂ = (-z + a * m₂)⁻¹ /- [standing] -/ )
    (hstab : 1 + a * m₁ * m₂ ≠ 0 /- [standing] -/ ) : m₁ = m₂ := by
  have e₁ : m₁ * (-z + a * m₁) = 1 := selfConsistent_mul_eq_one hz h₁
  have e₂ : m₂ * (-z + a * m₂) = 1 := selfConsistent_mul_eq_one hz h₂
  have key := sub_mul_one_add_mul_eq_sub (u₁ := m₁) (u₂ := m₂) (r₁ := 0) (r₂ := 0)
    e₁ e₂ (by ring) (by ring)
  rw [sub_zero] at key
  have := mul_eq_zero.mp key
  rcases this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hstab

/-- **Quantitative stability.**  If the stability factor is bounded below in
modulus by `κ > 0`, two approximate solutions with residuals `r₁`, `r₂` differ
by at most `(‖r₁‖ + ‖r₂‖) / κ`. -/
theorem norm_sub_le_of_stability_const {a z m₁ m₂ u₁ u₂ r₁ r₂ : ℂ /- [definition] -/ } {κ : ℝ /- [definition] -/ }
    (hu₁ : u₁ * (-z + a * m₁) = 1 /- [standing] -/ ) (hu₂ : u₂ * (-z + a * m₂) = 1 /- [standing] -/ )
    (hm₁ : m₁ = u₁ + r₁ /- [standing] -/ ) (hm₂ : m₂ = u₂ + r₂ /- [standing] -/ )
    (hκ : 0 < κ /- [standing] -/ ) (hlb : κ ≤ ‖1 + a * u₁ * u₂‖ /- [standing] -/ ) :
    ‖m₁ - m₂‖ ≤ (‖r₁‖ + ‖r₂‖) / κ := by
  have key := sub_mul_one_add_mul_eq_sub hu₁ hu₂ hm₁ hm₂
  have hnorm : ‖m₁ - m₂‖ * ‖1 + a * u₁ * u₂‖ = ‖r₁ - r₂‖ := by
    rw [← norm_mul, key]
  have hr : ‖r₁ - r₂‖ ≤ ‖r₁‖ + ‖r₂‖ := norm_sub_le _ _
  have hmul : ‖m₁ - m₂‖ * κ ≤ ‖r₁‖ + ‖r₂‖ := by
    calc ‖m₁ - m₂‖ * κ ≤ ‖m₁ - m₂‖ * ‖1 + a * u₁ * u₂‖ := by
          exact mul_le_mul_of_nonneg_left hlb (norm_nonneg _)
      _ = ‖r₁ - r₂‖ := hnorm
      _ ≤ ‖r₁‖ + ‖r₂‖ := hr
  exact (le_div_iff₀ hκ).mpr hmul

/-- A lower bound on the stability factor in the contractive regime. -/
theorem le_norm_one_add_mul {a u₁ u₂ : ℂ /- [definition] -/ } :
    1 - ‖a‖ * (‖u₁‖ * ‖u₂‖) ≤ ‖1 + a * u₁ * u₂‖ := by
  have h1 : ‖(1 : ℂ)‖ ≤ ‖1 + a * u₁ * u₂‖ + ‖a * u₁ * u₂‖ := by
    have : ‖(1 : ℂ)‖ = ‖(1 + a * u₁ * u₂) - a * u₁ * u₂‖ := by
      rw [add_sub_cancel_right]
    rw [this]
    exact norm_sub_le _ _
  rw [norm_one] at h1
  have h2 : ‖a * u₁ * u₂‖ = ‖a‖ * (‖u₁‖ * ‖u₂‖) := by
    rw [norm_mul, norm_mul, mul_assoc]
  rw [h2] at h1
  linarith

/-- **Stability in the contractive regime.**  When `‖a‖ * ‖u₁‖ * ‖u₂‖ < 1` the
stability constant is explicit and no auxiliary hypothesis is needed. -/
theorem norm_sub_le_of_contractive {a z m₁ m₂ u₁ u₂ r₁ r₂ : ℂ /- [definition] -/ }
    (hu₁ : u₁ * (-z + a * m₁) = 1 /- [standing] -/ ) (hu₂ : u₂ * (-z + a * m₂) = 1 /- [standing] -/ )
    (hm₁ : m₁ = u₁ + r₁ /- [standing] -/ ) (hm₂ : m₂ = u₂ + r₂ /- [standing] -/ )
    (hc : ‖a‖ * (‖u₁‖ * ‖u₂‖) < 1 /- [standing] -/ ) :
    ‖m₁ - m₂‖ ≤ (‖r₁‖ + ‖r₂‖) / (1 - ‖a‖ * (‖u₁‖ * ‖u₂‖)) :=
  norm_sub_le_of_stability_const hu₁ hu₂ hm₁ hm₂ (by linarith) le_norm_one_add_mul

/-! ### A concrete regime: real `a ≤ 0`, `z` and `m` in the upper half-plane

The estimates above take the stability constant as a hypothesis.  In the regime
that matters for a Stieltjes transform — `a` real and nonpositive, `z` strictly
in the upper half-plane, `m` in the closed upper half-plane — the constant can
be made explicit, because `-z + a * m` then has imaginary part at most `-z.im`.
This gives a stability estimate whose only hypothesis is `|a| < (z.im) ^ 2`,
a genuinely checkable condition, though one that fails near the spectral edge.
-/

/-- For real `a ≤ 0` and `0 ≤ m.im`, the imaginary part of `-z + a * m` is at
most `-z.im`. -/
theorem im_selfConsistentFactor_le {a : ℝ /- [definition] -/ } (ha : a ≤ 0 /- [standing] -/ ) {z m : ℂ /- [definition] -/ } (hm : 0 ≤ m.im /- [standing] -/ ) :
    (-z + (a : ℂ) * m).im ≤ -z.im := by
  rw [Complex.add_im, Complex.neg_im, Complex.im_ofReal_mul]
  have h : (0 : ℝ) ≤ -a * m.im := mul_nonneg (neg_nonneg.mpr ha) hm
  rw [neg_mul] at h
  linarith

/-- Consequently `-z + a * m` has modulus at least `z.im`. -/
theorem im_le_norm_selfConsistentFactor {a : ℝ /- [definition] -/ } (ha : a ≤ 0 /- [standing] -/ ) {z m : ℂ /- [definition] -/ }
    (hz : 0 < z.im /- [standing] -/ ) (hm : 0 ≤ m.im /- [standing] -/ ) : z.im ≤ ‖-z + (a : ℂ) * m‖ := by
  have h := Complex.abs_im_le_norm (-z + (a : ℂ) * m)
  have h2 := im_selfConsistentFactor_le ha (z := z) (m := m) hm
  have h3 : z.im ≤ |(-z + (a : ℂ) * m).im| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  linarith

/-- In particular the factor never vanishes, so the map is well defined. -/
theorem selfConsistentFactor_ne_zero {a : ℝ /- [definition] -/ } (ha : a ≤ 0 /- [standing] -/ ) {z m : ℂ /- [definition] -/ }
    (hz : 0 < z.im /- [standing] -/ ) (hm : 0 ≤ m.im /- [standing] -/ ) : -z + (a : ℂ) * m ≠ 0 := by
  intro h
  have hb := im_le_norm_selfConsistentFactor ha hz hm
  rw [h, norm_zero] at hb
  linarith

/-- The value of the map is bounded by `(z.im)⁻¹`, matching the general bound
`norm_stieltjes_le` for Stieltjes transforms of probability measures. -/
theorem norm_inv_selfConsistentFactor_le {a : ℝ /- [definition] -/ } (ha : a ≤ 0 /- [standing] -/ ) {z m : ℂ /- [definition] -/ }
    (hz : 0 < z.im /- [standing] -/ ) (hm : 0 ≤ m.im /- [standing] -/ ) : ‖(-z + (a : ℂ) * m)⁻¹‖ ≤ (z.im)⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ hz (im_le_norm_selfConsistentFactor ha hz hm)

/-- **Stability with an explicit constant.**  For real `a ≤ 0`, `z` in the open
upper half-plane, approximate solutions `m₁`, `m₂` in the closed upper
half-plane and `|a| < (z.im) ^ 2`, the two are close in terms of their
residuals alone. -/
theorem norm_sub_le_of_im_nonneg {a : ℝ /- [definition] -/ } (ha : a ≤ 0 /- [standing] -/ ) {z m₁ m₂ r₁ r₂ : ℂ /- [definition] -/ }
    (hz : 0 < z.im /- [standing] -/ ) (hm₁ : 0 ≤ m₁.im /- [standing] -/ ) (hm₂ : 0 ≤ m₂.im /- [standing] -/ )
    (e₁ : m₁ = (-z + (a : ℂ) * m₁)⁻¹ + r₁ /- [definition] -/ )
    (e₂ : m₂ = (-z + (a : ℂ) * m₂)⁻¹ + r₂ /- [definition] -/ )
    (hsmall : |a| < z.im ^ 2 /- [standing] -/ ) :
    ‖m₁ - m₂‖ ≤ (‖r₁‖ + ‖r₂‖) / (1 - |a| / z.im ^ 2) := by
  have hw₁ : -z + (a : ℂ) * m₁ ≠ 0 := selfConsistentFactor_ne_zero ha hz hm₁
  have hw₂ : -z + (a : ℂ) * m₂ ≠ 0 := selfConsistentFactor_ne_zero ha hz hm₂
  have hb₁ : ‖(-z + (a : ℂ) * m₁)⁻¹‖ ≤ (z.im)⁻¹ :=
    norm_inv_selfConsistentFactor_le ha hz hm₁
  have hb₂ : ‖(-z + (a : ℂ) * m₂)⁻¹‖ ≤ (z.im)⁻¹ :=
    norm_inv_selfConsistentFactor_le ha hz hm₂
  set u₁ : ℂ := (-z + (a : ℂ) * m₁)⁻¹ with hu₁def
  set u₂ : ℂ := (-z + (a : ℂ) * m₂)⁻¹ with hu₂def
  have hu₁ : u₁ * (-z + (a : ℂ) * m₁) = 1 := inv_mul_cancel₀ hw₁
  have hu₂ : u₂ * (-z + (a : ℂ) * m₂) = 1 := inv_mul_cancel₀ hw₂
  have hzi : (0 : ℝ) < (z.im)⁻¹ := inv_pos.mpr hz
  have hna : ‖((a : ℝ) : ℂ)‖ = |a| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hprod : ‖u₁‖ * ‖u₂‖ ≤ (z.im)⁻¹ * (z.im)⁻¹ :=
    mul_le_mul hb₁ hb₂ (norm_nonneg _) (le_of_lt hzi)
  have hbound : ‖((a : ℝ) : ℂ)‖ * (‖u₁‖ * ‖u₂‖) ≤ |a| / z.im ^ 2 := by
    rw [hna]
    calc |a| * (‖u₁‖ * ‖u₂‖) ≤ |a| * ((z.im)⁻¹ * (z.im)⁻¹) :=
          mul_le_mul_of_nonneg_left hprod (abs_nonneg a)
      _ = |a| / z.im ^ 2 := by rw [div_eq_mul_inv, ← inv_pow, pow_two]
  have hκ : 0 < 1 - |a| / z.im ^ 2 := by
    have hz2 : (0 : ℝ) < z.im ^ 2 := pow_pos hz 2
    rw [sub_pos, div_lt_one hz2]
    exact hsmall
  refine norm_sub_le_of_stability_const hu₁ hu₂ e₁ e₂ hκ ?_
  have hlb := le_norm_one_add_mul (a := ((a : ℝ) : ℂ)) (u₁ := u₁) (u₂ := u₂)
  linarith

end RMTFoundations.Stieltjes

#print axioms RMTFoundations.Stieltjes.selfConsistent_mul_eq_one
#print axioms RMTFoundations.Stieltjes.quadratic_of_selfConsistent
#print axioms RMTFoundations.Stieltjes.selfConsistent_of_quadratic
#print axioms RMTFoundations.Stieltjes.semicircle_quadratic_of_selfConsistent
#print axioms RMTFoundations.Stieltjes.selfConsistent_of_semicircle_quadratic
#print axioms RMTFoundations.Stieltjes.eq_or_sum_eq_of_quadratic
#print axioms RMTFoundations.Stieltjes.eq_of_quadratic_of_im_pos
#print axioms RMTFoundations.Stieltjes.eq_of_selfConsistent_of_im_pos
#print axioms RMTFoundations.Stieltjes.eq_of_semicircle_quadratic_of_im_pos
#print axioms RMTFoundations.Stieltjes.sub_mul_one_add_mul_eq_sub
#print axioms RMTFoundations.Stieltjes.eq_of_selfConsistent_of_one_add_ne_zero
#print axioms RMTFoundations.Stieltjes.norm_sub_le_of_stability_const
#print axioms RMTFoundations.Stieltjes.le_norm_one_add_mul
#print axioms RMTFoundations.Stieltjes.norm_sub_le_of_contractive
#print axioms RMTFoundations.Stieltjes.im_selfConsistentFactor_le
#print axioms RMTFoundations.Stieltjes.im_le_norm_selfConsistentFactor
#print axioms RMTFoundations.Stieltjes.selfConsistentFactor_ne_zero
#print axioms RMTFoundations.Stieltjes.norm_inv_selfConsistentFactor_le
#print axioms RMTFoundations.Stieltjes.norm_sub_le_of_im_nonneg
