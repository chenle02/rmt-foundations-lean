import RMTFoundations.Stieltjes.Defs

/-!
# The Stieltjes transform on the real axis, off the support

## What is proved here

* `stieltjesReal`: the real-variable transform `t ↦ ∫ (x - t)⁻¹ dμ`.
* `stieltjes_ofReal`: `stieltjes μ (t : ℂ) = (stieltjesReal μ t : ℂ)` for every
  measure and every real `t`, with no hypotheses.  This is the precise sense in
  which the transform "is real on the real axis"; note that it holds even where
  the integral diverges, because both sides are then `0` by the junk-value
  convention for the Bochner integral.
* `integrable_realStieltjesKernel`: off the support of a finite measure the
  integrand is bounded, hence integrable.
* `inv_sub_le_inv_sub`: the pointwise inequality behind monotonicity.
* `stieltjesReal_monotone`: **`stieltjesReal μ` is monotone increasing on any
  closed interval disjoint from the support.**

A remark on the direction of the inequality: with the convention
`m z = ∫ (x - z)⁻¹ dμ` used throughout this package the real transform
*increases* on intervals off the support, because `∂/∂t (x - t)⁻¹ = (x - t)⁻²`
is positive.  It is the opposite convention `∫ (z - x)⁻¹ dμ` whose real
restriction decreases; `stieltjesReal_antitone_neg` records that reading.

## What is NOT proved here

* No strict monotonicity, and no statement that the transform is a bijection
  from a gap in the support onto an interval.  Strictness needs `μ ≠ 0` plus a
  strict-inequality version of `integral_mono_ae`, which is not done.
* No derivative formula on the real axis; in particular
  `(stieltjesReal μ)' = ∫ (x - t)⁻² dμ` is not proved here, although mathlib's
  `hasDerivAt_resolventTransform` gives the complex statement.
* No limits as `t` approaches the support, and no behaviour at `±∞`.
-/

namespace RMTFoundations.Stieltjes

open MeasureTheory

variable {μ : Measure ℝ /- [definition] -/ }

/-- The Stieltjes transform restricted to the real axis, as a real-valued
function. -/
noncomputable def stieltjesReal (μ : Measure ℝ /- [definition] -/ ) (t : ℝ /- [definition] -/ ) : ℝ :=
  ∫ x : ℝ, (x - t)⁻¹ ∂μ

theorem stieltjesReal_apply (μ : Measure ℝ /- [definition] -/ ) (t : ℝ /- [definition] -/ ) :
    stieltjesReal μ t = ∫ x : ℝ, (x - t)⁻¹ ∂μ := rfl

/-- The complex transform at a real point is the real transform. -/
theorem stieltjes_ofReal (μ : Measure ℝ /- [definition] -/ ) (t : ℝ /- [definition] -/ ) :
    stieltjes μ (t : ℂ) = (stieltjesReal μ t : ℂ) := by
  rw [stieltjes_apply, stieltjesReal_apply, ← integral_complex_ofReal]
  congr 1
  funext x
  rw [← Complex.ofReal_sub, ← Complex.ofReal_inv]

/-! ### Integrability off the support -/

/-- Off the support of a finite measure the real integrand is bounded, hence
integrable. -/
theorem integrable_realStieltjesKernel (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] {t : ℝ /- [definition] -/ }
    (ht : t ∉ μ.support /- [standing] -/ ) : Integrable (fun x : ℝ => (x - t)⁻¹) μ := by
  rw [Measure.mem_support_iff_forall] at ht
  push Not at ht
  obtain ⟨U, hU, hUle⟩ := ht
  have hUzero : μ U = 0 := nonpos_iff_eq_zero.mp hUle
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  have hball : μ (Metric.ball t ε) = 0 := measure_mono_null hsub hUzero
  refine ⟨(measurable_id.sub measurable_const).inv.aestronglyMeasurable, ?_⟩
  refine HasFiniteIntegral.of_bounded (C := ε⁻¹) ?_
  filter_upwards [compl_mem_ae_iff.mpr hball] with x hx
  have hdist : ε ≤ |x - t| := by
    have : ε ≤ dist x t := not_lt.mp (fun h => hx (Metric.mem_ball.mpr h))
    rwa [Real.dist_eq] at this
  rw [Real.norm_eq_abs, abs_inv]
  exact inv_anti₀ hε hdist

/-! ### Monotonicity -/

/-- The pointwise inequality: for `x` outside `[s, t]` the kernel increases in
the base point. -/
theorem inv_sub_le_inv_sub {s t x : ℝ /- [definition] -/ } (hst : s ≤ t /- [standing] -/ ) (hx : x ∉ Set.Icc s t /- [standing] -/ ) :
    (x - s)⁻¹ ≤ (x - t)⁻¹ := by
  have hprod : 0 < (x - t) * (x - s) := by
    rcases lt_or_ge x s with h | h
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · have hxt : t < x := by
        by_contra hc
        exact hx ⟨h, not_lt.mp hc⟩
      exact mul_pos (by linarith) (by linarith)
  have hs : x - s ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact lt_irrefl 0 hprod
  have ht : x - t ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact lt_irrefl 0 hprod
  rw [← sub_nonneg, ← one_div, ← one_div, div_sub_div _ _ ht hs]
  refine div_nonneg ?_ hprod.le
  have : (1 : ℝ) * (x - s) - (x - t) * 1 = t - s := by ring
  rw [this]
  linarith

/-- **Monotonicity off the support.**  On a closed interval disjoint from the
support of a finite measure, `stieltjesReal μ` is increasing. -/
theorem stieltjesReal_monotone (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] {s t : ℝ /- [definition] -/ }
    (hst : s ≤ t /- [standing] -/ ) (hI : Set.Icc s t ⊆ (μ.support)ᶜ /- [standing] -/ ) :
    stieltjesReal μ s ≤ stieltjesReal μ t := by
  have hs : s ∉ μ.support := hI (Set.left_mem_Icc.mpr hst)
  have ht : t ∉ μ.support := hI (Set.right_mem_Icc.mpr hst)
  have hIcc : μ (Set.Icc s t) = 0 :=
    measure_mono_null hI Measure.measure_compl_support
  refine integral_mono_ae (integrable_realStieltjesKernel μ hs)
    (integrable_realStieltjesKernel μ ht) ?_
  filter_upwards [compl_mem_ae_iff.mpr hIcc] with x hx
  exact inv_sub_le_inv_sub hst hx

/-- The same statement in the opposite sign convention `z ↦ ∫ (z - x)⁻¹ dμ`,
where the real transform decreases. -/
theorem stieltjesReal_antitone_neg (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] {s t : ℝ /- [definition] -/ }
    (hst : s ≤ t /- [standing] -/ ) (hI : Set.Icc s t ⊆ (μ.support)ᶜ /- [standing] -/ ) :
    -stieltjesReal μ t ≤ -stieltjesReal μ s :=
  neg_le_neg (stieltjesReal_monotone μ hst hI)

end RMTFoundations.Stieltjes

#print axioms RMTFoundations.Stieltjes.stieltjesReal
#print axioms RMTFoundations.Stieltjes.stieltjesReal_apply
#print axioms RMTFoundations.Stieltjes.stieltjes_ofReal
#print axioms RMTFoundations.Stieltjes.integrable_realStieltjesKernel
#print axioms RMTFoundations.Stieltjes.inv_sub_le_inv_sub
#print axioms RMTFoundations.Stieltjes.stieltjesReal_monotone
#print axioms RMTFoundations.Stieltjes.stieltjesReal_antitone_neg
