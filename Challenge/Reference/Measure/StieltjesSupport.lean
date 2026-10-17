import Challenge.Reference.Measure.StieltjesInversion
import Mathlib
namespace RMTFoundations.StieltjesSupport
open MeasureTheory Filter Topology Set
open RMTFoundations.Stieltjes (stieltjes)
open RMTFoundations.StieltjesInversion (stieltjes_density)
/-- `iy · S_μ(iy) → -μ(ℝ)` as `y → ∞` (dominated convergence). -/
theorem tendsto_iy_stieltjes (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] :
    Tendsto (fun y : ℝ => ((y : ℂ) * Complex.I) * stieltjes μ ((y : ℂ) * Complex.I)) atTop
      (𝓝 (-(μ.real univ : ℂ))) := by
  have hrw : ∀ y : ℝ, ((y : ℂ) * Complex.I) * stieltjes μ ((y : ℂ) * Complex.I)
      = ∫ t, ((y : ℂ) * Complex.I) * ((t : ℂ) - (y : ℂ) * Complex.I)⁻¹ ∂μ := by
    intro y; rw [stieltjes, integral_const_mul]
  simp_rw [hrw]
  have hconst : (-(μ.real univ : ℂ)) = ∫ _t, (-1 : ℂ) ∂μ := by
    rw [integral_const, Complex.real_smul]; ring
  rw [hconst]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    refine Continuous.aestronglyMeasurable ?_
    refine continuous_const.mul ((Complex.continuous_ofReal.sub continuous_const).inv₀ ?_)
    intro t h0; have := congrArg Complex.im h0; simp at this; linarith
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    refine Eventually.of_forall fun t => ?_
    have hw : y ≤ ‖(t : ℂ) - (y : ℂ) * Complex.I‖ := by
      have := Complex.abs_im_le_norm ((t : ℂ) - (y : ℂ) * Complex.I)
      simp at this; rwa [abs_of_pos hy] at this
    rw [norm_mul, norm_inv, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hy]
    rw [mul_inv_le_iff₀ (lt_of_lt_of_le hy hw)]; linarith
  · refine Eventually.of_forall fun t => ?_
    have hkey : ∀ y : ℝ, 0 < y → ((y : ℂ) * Complex.I) * ((t : ℂ) - (y : ℂ) * Complex.I)⁻¹
        = ((t : ℂ) / ((y : ℂ) * Complex.I) - 1)⁻¹ := by
      intro y hy
      have hyI : (y : ℂ) * Complex.I ≠ 0 :=
        mul_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne') Complex.I_ne_zero
      rw [div_sub_one hyI, inv_div, div_eq_mul_inv]
    have h1 : Tendsto (fun y : ℝ => (t : ℂ) / ((y : ℂ) * Complex.I)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : (fun y : ℝ => ‖(t : ℂ) / ((y : ℂ) * Complex.I)‖) =ᶠ[atTop] fun y => |t| / y := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
        rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hy]
      exact Tendsto.congr' this.symm (tendsto_const_nhds.div_atTop tendsto_id)
    have h2 := (h1.sub tendsto_const_nhds).inv₀ (show (0 : ℂ) - 1 ≠ 0 by norm_num)
    rw [show ((0 : ℂ) - 1)⁻¹ = -1 by norm_num] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    exact (hkey y hy).symm

/-- A finite measure whose Stieltjes transform has `0 ≤ Im S(x + iη) ≤ C η` for all
`|x| ≥ R` has no mass outside `[-R, R]` (via `PathEdgeDensity.stieltjes_density`). -/
theorem support_of_im_small (μ : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure μ /- [standing] -/ ] (R C : ℝ /- [definition] -/ )
    (him : ∀ x η : ℝ, 0 < η → R ≤ |x| →
      0 ≤ (stieltjes μ ((x : ℂ) + (η : ℂ) * Complex.I)).im ∧
      (stieltjes μ ((x : ℂ) + (η : ℂ) * Complex.I)).im ≤ C * η /- [standing] -/ ) :
    μ (Icc (-R) R)ᶜ = 0 := by
  have hconv : ∀ x : ℝ, R < |x| → Tendsto (fun η : ℝ =>
      (stieltjes μ ((x : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] 0) (𝓝 (Real.pi * 0)) := by
    intro x hx
    rw [mul_zero]
    have hup : Tendsto (fun η : ℝ => C * η) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun η : ℝ => C * η) (𝓝 0) (𝓝 (C * 0)) :=
        (continuous_const.mul continuous_id).tendsto (0 : ℝ)
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη using (him x η hη hx.le).1
    · filter_upwards [self_mem_nhdsWithin] with η hη using (him x η hη hx.le).2
  have hbd : ∀ p q : ℝ, (∀ x ∈ Ioo p q, R < |x|) → ∀ a b, p < a → b < q →
      ∃ C', ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), ∀ x ∈ Icc a b,
        |(stieltjes μ ((x : ℂ) + (η : ℂ) * Complex.I)).im| ≤ C' := by
    intro p q hpq a b ha hb
    refine ⟨|C|, ?_⟩
    have hev : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), η < 1 := nhdsWithin_le_nhds (gt_mem_nhds one_pos)
    filter_upwards [hev, self_mem_nhdsWithin] with η h1 h0 x hx
    by_cases hab : a ≤ b
    · have hxR : R < |x| := hpq x ⟨by linarith [hx.1], by linarith [hx.2]⟩
      obtain ⟨hi0, hi1⟩ := him x η h0 hxR.le
      rw [abs_of_nonneg hi0]
      have : C * η ≤ |C| := by
        have h0' : (0 : ℝ) < η := h0
        calc C * η ≤ |C| * η := mul_le_mul_of_nonneg_right (le_abs_self C) h0'.le
          _ ≤ |C| * 1 := by gcongr
          _ = |C| := mul_one _
      linarith
    · exact absurd (hx.1.trans hx.2) hab
  have hzero : ∀ p q : ℝ, (∀ x ∈ Ioo p q, R < |x|) → ∀ a b, p < a → a < b → b < q →
      μ (Ioo a b) = 0 := by
    intro p q hpq a b ha hab hb
    have := stieltjes_density μ p q (fun _ => 0) (fun x hx => hconv x (hpq x hx))
      (hbd p q hpq) a b ha hab hb
    rw [intervalIntegral.integral_zero] at this
    exact (measureReal_eq_zero_iff (measure_ne_top μ _)).mp this
  have hright : μ (Ioi R) = 0 := by
    have hcov : Ioi R ⊆ ⋃ n : ℕ, Ioo (R + 1 / ((n : ℝ) + 2)) (R + n + 2) := by
      intro x hx
      have hx0 : 0 < x - R := sub_pos.mpr hx
      obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / (x - R)) (x - R))
      refine Set.mem_iUnion.mpr ⟨n, ?_, ?_⟩
      · have h1 : 1 / (x - R) < (n : ℝ) + 2 := by linarith [le_max_left (1 / (x - R)) (x - R)]
        have : 1 / ((n : ℝ) + 2) < x - R := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hx0] at h1
          linarith
        linarith
      · linarith [le_max_right (1 / (x - R)) (x - R)]
    refine measure_mono_null hcov (measure_iUnion_null fun n => ?_)
    have hn2 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hn3 : 1 / ((n : ℝ) + 2) < n + 2 := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    refine hzero R (R + n + 3) (fun x hx => ?_) _ _ (by linarith) (by linarith) (by linarith)
    have : 0 ≤ R ∨ R < 0 := le_or_gt 0 R
    rcases this with h | h
    · rw [abs_of_pos (by linarith [hx.1])]; exact hx.1
    · exact lt_of_lt_of_le (by linarith [hx.1] : R < x) (le_abs_self x)
  have hleft : μ (Iio (-R)) = 0 := by
    have hcov : Iio (-R) ⊆ ⋃ n : ℕ, Ioo (-R - n - 2) (-R - 1 / ((n : ℝ) + 2)) := by
      intro x hx
      have hx0 : 0 < -R - x := by simp at hx; linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / (-R - x)) (-R - x))
      refine Set.mem_iUnion.mpr ⟨n, ?_, ?_⟩
      · linarith [le_max_right (1 / (-R - x)) (-R - x)]
      · have h1 : 1 / (-R - x) < (n : ℝ) + 2 := by linarith [le_max_left (1 / (-R - x)) (-R - x)]
        have : 1 / ((n : ℝ) + 2) < -R - x := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hx0] at h1
          linarith
        linarith
    refine measure_mono_null hcov (measure_iUnion_null fun n => ?_)
    have hn2 : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hn3 : 1 / ((n : ℝ) + 2) < n + 2 := by
      rw [div_lt_iff₀ (by positivity)]; nlinarith
    refine hzero (-R - n - 3) (-R) (fun x hx => ?_) _ _ (by linarith) (by linarith) (by linarith)
    rcases le_or_gt 0 R with h | h
    · rw [abs_of_neg (by linarith [hx.2])]; linarith [hx.2]
    · exact lt_of_lt_of_le (by linarith [hx.2] : R < -x) (neg_le_abs x)
  have hc : (Icc (-R) R)ᶜ ⊆ Iio (-R) ∪ Ioi R := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact measure_mono_null hc (measure_union_null hleft hright)

end RMTFoundations.StieltjesSupport

#print axioms RMTFoundations.StieltjesSupport.tendsto_iy_stieltjes
#print axioms RMTFoundations.StieltjesSupport.support_of_im_small
