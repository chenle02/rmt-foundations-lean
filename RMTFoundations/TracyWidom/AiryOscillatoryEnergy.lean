import Mathlib

set_option autoImplicit false
namespace RMTFoundations.TracyWidom.AiryOscillatoryEnergy

noncomputable def energy (f df : ℝ → ℝ /- [definition] -/)
    (r : ℝ /- [definition] -/) : ℝ :=
  (r + 5 / (16 * r ^ 5)) * f (-(r ^ 2)) ^ 2 +
    (df (-(r ^ 2)) - f (-(r ^ 2)) / (4 * r ^ 2)) ^ 2 / r

/-- A modified Liouville energy decreases; this is an exact identity, not an asymptotic. -/
theorem hasDerivAt_energy (f df : ℝ → ℝ /- [definition] -/)
    (hf : ∀ x, HasDerivAt f (df x) x /- [standing] -/)
    (hdf : ∀ x, HasDerivAt df (x * f x) x /- [standing] -/)
    (r : ℝ /- [definition] -/)
    (hr : 0 < r /- [standing] -/) :
    HasDerivAt (energy f df) (-(15 / (8 * r ^ 6)) * f (-(r ^ 2)) ^ 2) r := by
  have hx := ((hasDerivAt_id r).pow 2).neg
  have hF := (hf (-(r ^ 2))).comp r hx
  have hG := (hdf (-(r ^ 2))).comp r hx
  have hden := ((hasDerivAt_id r).pow 5).const_mul 16
  have hc := (hasDerivAt_id r).add
    ((hasDerivAt_const r (5 : ℝ)).div hden (by dsimp; positivity))
  have hden2 := ((hasDerivAt_id r).pow 2).const_mul 4
  have hterm := hG.sub (hF.div hden2 (by dsimp; positivity))
  have h := (hc.mul (hF.pow 2)).add ((hterm.pow 2).div (hasDerivAt_id r) hr.ne')
  convert h using 1
  all_goals try rfl
  all_goals dsimp [energy]
  all_goals field_simp [hr.ne']
  all_goals ring


/-- The energy controls the function before any monotonicity argument. -/
theorem amplitude_sq_le_energy (f df : ℝ → ℝ /- [definition] -/)
    (r : ℝ /- [definition] -/) (hr : 0 < r /- [standing] -/) :
    r * f (-(r ^ 2)) ^ 2 ≤ energy f df r := by
  unfold energy
  have h1 : 0 ≤ 5 / (16 * r ^ 5) := by positivity
  have h2 : 0 ≤ (df (-(r ^ 2)) - f (-(r ^ 2)) / (4 * r ^ 2)) ^ 2 / r := by positivity
  nlinarith [sq_nonneg (f (-(r ^ 2)))]


/-- Every Airy solution has a nonincreasing modified energy on the positive scale. -/
theorem energy_antitoneOn (f df : ℝ → ℝ /- [definition] -/)
    (hf : ∀ x, HasDerivAt f (df x) x /- [standing] -/)
    (hdf : ∀ x, HasDerivAt df (x * f x) x /- [standing] -/) :
    AntitoneOn (energy f df) (Set.Ioi 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro r hr
    exact (hasDerivAt_energy f df hf hdf r hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioi] at hr
    exact (hasDerivAt_energy f df hf hdf r hr).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ioi] at hr
    rw [(hasDerivAt_energy f df hf hdf r hr).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)

/-- Uniform oscillatory-side amplitude control on the square-root scale. -/
theorem amplitude_bound (f df : ℝ → ℝ /- [definition] -/)
    (hf : ∀ x, HasDerivAt f (df x) x /- [standing] -/)
    (hdf : ∀ x, HasDerivAt df (x * f x) x /- [standing] -/)
    (r : ℝ /- [definition] -/)
    (hr : 1 ≤ r /- [standing] -/) :
    |f (-(r ^ 2))| ≤ Real.sqrt (energy f df 1) / Real.sqrt r := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hb := (amplitude_sq_le_energy f df r hr0).trans
    (energy_antitoneOn f df hf hdf (by norm_num : (1 : ℝ) ∈ Set.Ioi 0) (by simpa only [Set.mem_Ioi] using hr0) hr)
  have he : 0 ≤ energy f df 1 :=
    (by positivity : 0 ≤ r * f (-(r ^ 2)) ^ 2).trans hb
  apply (le_div_iff₀ (Real.sqrt_pos.mpr hr0)).mpr
  have hsq : (|f (-(r ^ 2))| * Real.sqrt r) ^ 2 ≤ (Real.sqrt (energy f df 1)) ^ 2 := by
    rw [mul_pow, sq_abs, Real.sq_sqrt hr0.le, Real.sq_sqrt he]
    nlinarith
  exact (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp hsq

end RMTFoundations.TracyWidom.AiryOscillatoryEnergy

#print axioms RMTFoundations.TracyWidom.AiryOscillatoryEnergy.energy
#print axioms RMTFoundations.TracyWidom.AiryOscillatoryEnergy.hasDerivAt_energy
#print axioms RMTFoundations.TracyWidom.AiryOscillatoryEnergy.amplitude_sq_le_energy
#print axioms RMTFoundations.TracyWidom.AiryOscillatoryEnergy.energy_antitoneOn
#print axioms RMTFoundations.TracyWidom.AiryOscillatoryEnergy.amplitude_bound
