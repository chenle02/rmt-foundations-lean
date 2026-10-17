import Challenge.Reference.Stieltjes.Defs
import Mathlib

namespace RMTFoundations.StieltjesInversion

open MeasureTheory Filter Topology Set Real
open RMTFoundations.Stieltjes (stieltjes)

section Inversion

/- The Stieltjes transform `S_ν(z) = ∫ (t - z)⁻¹ dν(t)` (mathlib's
`resolventTransform` for `𝕜 = ℝ`, `A = ℂ`, written out). -/

/-- `Im (t - x - iη)⁻¹ = η/((t-x)² + η²)`, the Poisson kernel (times `π`). -/
theorem im_kernel (t x η : ℝ /- [definition] -/ ) :
    (((t : ℂ) - ((x : ℂ) + (η : ℂ) * Complex.I))⁻¹).im = η / ((t - x) ^ 2 + η ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, Complex.I_re, Complex.sub_re, Complex.add_re,
    Complex.mul_re]
  ring_nf

/-- `|(t - x - iη)⁻¹| ≤ η⁻¹`. -/
theorem norm_kernel_le (t x η : ℝ /- [definition] -/ ) (hη : 0 < η /- [standing] -/ ) :
    ‖((t : ℂ) - ((x : ℂ) + (η : ℂ) * Complex.I))⁻¹‖ ≤ η⁻¹ := by
  have hw : η ≤ ‖(t : ℂ) - ((x : ℂ) + (η : ℂ) * Complex.I)‖ := by
    have := Complex.abs_im_le_norm ((t : ℂ) - ((x : ℂ) + (η : ℂ) * Complex.I))
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re] at this
    simp at this
    rwa [abs_of_pos hη] at this
  rw [norm_inv]
  exact inv_anti₀ hη hw

/-- The kernel is continuous in `t` for `η > 0`. -/
theorem continuous_kernel (x η : ℝ /- [definition] -/ ) (hη : 0 < η /- [standing] -/ ) :
    Continuous fun t : ℝ => ((t : ℂ) - ((x : ℂ) + (η : ℂ) * Complex.I))⁻¹ := by
  refine (Complex.continuous_ofReal.sub continuous_const).inv₀ fun t h0 => ?_
  have := congrArg Complex.im h0
  simp at this
  linarith

/-- The kernel is `ν`-integrable for finite `ν`. -/
theorem integrable_kernel (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] (x η : ℝ /- [definition] -/ ) (hη : 0 < η /- [standing] -/ ) :
    Integrable (fun t : ℝ => ((t : ℂ) - ((x : ℂ) + (η : ℂ) * Complex.I))⁻¹) ν :=
  Integrable.of_bound (continuous_kernel x η hη).aestronglyMeasurable η⁻¹
    (Eventually.of_forall fun t => norm_kernel_le t x η hη)

/-- `Im S_ν(x + iη) = ∫ η/((t-x)² + η²) dν(t)`. -/
theorem stieltjes_im (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] (x η : ℝ /- [definition] -/ ) (hη : 0 < η /- [standing] -/ ) :
    (stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im = ∫ t, η / ((t - x) ^ 2 + η ^ 2) ∂ν := by
  have h := integral_im (integrable_kernel ν x η hη)
  simp only [RCLike.im_to_complex] at h
  rw [stieltjes, ← h]
  simp only [im_kernel]

/-- `d/dx arctan((x - t)/η) = η/((t-x)² + η²)`. -/
theorem hasDerivAt_arctan_shift (t η x : ℝ /- [definition] -/ ) (hη : 0 < η /- [standing] -/ ) :
    HasDerivAt (fun y => arctan ((y - t) / η)) (η / ((t - x) ^ 2 + η ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => (y - t) / η) (1 / η) x :=
    ((hasDerivAt_id x).sub_const t).div_const η
  have h2 := (hasDerivAt_arctan ((x - t) / η)).comp x h1
  refine h2.congr_deriv ?_
  field_simp
  ring

/-- The Poisson kernel is nonnegative. -/
theorem kernel_nonneg (t x η : ℝ /- [definition] -/ ) (hη : 0 < η /- [standing] -/ ) : 0 ≤ η / ((t - x) ^ 2 + η ^ 2) := by
  positivity

/-- The Poisson kernel is at most `η⁻¹`. -/
theorem kernel_le (t x η : ℝ /- [definition] -/ ) (hη : 0 < η /- [standing] -/ ) : η / ((t - x) ^ 2 + η ^ 2) ≤ η⁻¹ := by
  rw [div_le_iff₀ (by positivity)]
  have : η⁻¹ * η ^ 2 = η := by field_simp
  nlinarith [sq_nonneg (t - x), inv_pos.mpr hη]

/-- `∫_a^b η/((t-x)² + η²) dx = arctan((b-t)/η) - arctan((a-t)/η)`. -/
theorem interval_kernel (t η a b : ℝ /- [definition] -/ ) (hη : 0 < η /- [standing] -/ ) :
    ∫ x in a..b, η / ((t - x) ^ 2 + η ^ 2) = arctan ((b - t) / η) - arctan ((a - t) / η) := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_arctan_shift t η x hη) ?_
  refine (Continuous.intervalIntegrable ?_ a b)
  fun_prop (disch := intros; positivity)

/-- **Fubini step**: `∫_a^b Im S_ν(x + iη) dx = ∫ (arctan((b-t)/η) - arctan((a-t)/η)) dν(t)`. -/
theorem interval_im (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] (η a b : ℝ /- [definition] -/ ) (hη : 0 < η /- [standing] -/ ) :
    ∫ x in a..b, (stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im
      = ∫ t, (arctan ((b - t) / η) - arctan ((a - t) / η)) ∂ν := by
  simp_rw [stieltjes_im ν _ η hη]
  haveI : IsFiniteMeasure (volume.restrict (Set.uIoc a b)) :=
    isFiniteMeasure_restrict.2 (by rw [Set.uIoc]; exact measure_Ioc_lt_top.ne)
  rw [intervalIntegral_integral_swap]
  · simp_rw [interval_kernel _ η a b hη]
  · refine Integrable.of_bound ?_ η⁻¹ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [Function.uncurry_def]
      fun_prop (disch := intros; positivity)
    · simp only [Function.uncurry_def, Real.norm_eq_abs]
      rw [abs_of_nonneg (kernel_nonneg _ _ η hη)]
      exact kernel_le _ _ η hη

/-- `lim_{η↓0} arctan(c/η)`: `π/2`, `-π/2` or `0` by the sign of `c`. -/
noncomputable def arctanLim (c : ℝ /- [definition] -/ ) : ℝ :=
  if 0 < c then π / 2 else if c < 0 then -(π / 2) else 0

/-- `arctan(c/η) → arctanLim c` as `η ↓ 0`. -/
theorem tendsto_arctan_div (c : ℝ /- [definition] -/ ) :
    Tendsto (fun η : ℝ => arctan (c / η)) (𝓝[>] 0) (𝓝 (arctanLim c)) := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · have h1 : Tendsto (fun η : ℝ => (-c) * η⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop (by linarith)
    have h2 := (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
    have h3 := h2.neg
    rw [arctanLim, if_neg (not_lt.mpr hc.le), if_pos hc]
    refine h3.congr fun η => ?_
    simp only [Function.comp_apply, div_eq_mul_inv, neg_mul, arctan_neg, neg_neg]
  · subst hc
    rw [arctanLim, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
    simp
  · have h1 : Tendsto (fun η : ℝ => c * η⁻¹) (𝓝[>] 0) atTop :=
      tendsto_inv_nhdsGT_zero.const_mul_atTop hc
    have h2 := (tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
    rw [arctanLim, if_pos hc]
    refine h2.congr fun η => ?_
    simp only [Function.comp_apply, div_eq_mul_inv]

/-- The limit profile of the arctan kernel: `1` on `(a,b)`, `1/2` at the ends. -/
noncomputable def edgeProfile (a b t : ℝ /- [definition] -/ ) : ℝ :=
  (Ioo a b).indicator 1 t + (1 / 2) * ({a} : Set ℝ).indicator 1 t
    + (1 / 2) * ({b} : Set ℝ).indicator 1 t

/-- The arctan kernel tends to `π · edgeProfile a b`. -/
theorem kernel_limit (a b t : ℝ /- [definition] -/ ) (hab : a < b /- [standing] -/ ) :
    Tendsto (fun η : ℝ => arctan ((b - t) / η) - arctan ((a - t) / η)) (𝓝[>] 0)
      (𝓝 (π * edgeProfile a b t)) := by
  have h := (tendsto_arctan_div (b - t)).sub (tendsto_arctan_div (a - t))
  convert h using 2
  unfold edgeProfile arctanLim
  rcases lt_trichotomy t a with h1 | h1 | h1
  · have : t ∉ Ioo a b := fun h => by linarith [h.1]
    simp [Set.indicator, this, h1.ne, (h1.trans hab).ne, show 0 < b - t by linarith,
      show 0 < a - t by linarith]
  · subst h1
    simp [Set.indicator, hab.ne, show 0 < b - t by linarith]
    ring
  · rcases lt_trichotomy t b with h2 | h2 | h2
    · simp [Set.indicator, h1, h2, h1.ne', h2.ne, show 0 < b - t by linarith,
        show a - t < 0 by linarith, show ¬ 0 < a - t by linarith]
    · subst h2
      simp [Set.indicator, hab.ne', show a - t < 0 by linarith, show ¬ 0 < a - t by linarith]
      ring
    · have : t ∉ Ioo a b := fun h => by linarith [h.2]
      simp [Set.indicator, this, h1.ne', h2.ne', show b - t < 0 by linarith,
        show ¬ 0 < b - t by linarith, show a - t < 0 by linarith, show ¬ 0 < a - t by linarith]

/-- `|arctan u - arctan v| ≤ π` (domination). -/
theorem abs_arctan_sub_le (u v : ℝ /- [definition] -/ ) : |arctan u - arctan v| ≤ π := by
  have h1 := neg_pi_div_two_lt_arctan u
  have h2 := arctan_lt_pi_div_two u
  have h3 := neg_pi_div_two_lt_arctan v
  have h4 := arctan_lt_pi_div_two v
  rw [abs_le]; constructor <;> linarith

/-- `∫ π · edgeProfile dν = π(ν(a,b) + ν{a}/2 + ν{b}/2)`. -/
theorem integral_edgeProfile (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] (a b : ℝ /- [definition] -/ ) :
    ∫ t, π * edgeProfile a b t ∂ν
      = π * (ν.real (Ioo a b) + ν.real {a} / 2 + ν.real {b} / 2) := by
  have i1 : Integrable ((Ioo a b).indicator (1 : ℝ → ℝ)) ν :=
    (integrable_const (1 : ℝ)).indicator measurableSet_Ioo
  have i2 : Integrable (({a} : Set ℝ).indicator (1 : ℝ → ℝ)) ν :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_singleton a)
  have i3 : Integrable (({b} : Set ℝ).indicator (1 : ℝ → ℝ)) ν :=
    (integrable_const (1 : ℝ)).indicator (measurableSet_singleton b)
  have j2 : Integrable (fun t => (1 / 2 : ℝ) * ({a} : Set ℝ).indicator 1 t) ν :=
    i2.const_mul _
  have j3 : Integrable (fun t => (1 / 2 : ℝ) * ({b} : Set ℝ).indicator 1 t) ν :=
    i3.const_mul _
  have j1 : Integrable (fun t => (Ioo a b).indicator (1 : ℝ → ℝ) t) ν := i1
  have j12 : Integrable (fun t => (Ioo a b).indicator (1 : ℝ → ℝ) t
      + (1 / 2 : ℝ) * ({a} : Set ℝ).indicator 1 t) ν := j1.add j2
  unfold edgeProfile
  rw [integral_const_mul, integral_add j12 j3, integral_add j1 j2, integral_const_mul,
    integral_const_mul, integral_indicator_one measurableSet_Ioo,
    integral_indicator_one (measurableSet_singleton a),
    integral_indicator_one (measurableSet_singleton b)]
  ring

/-- **The arctan side of Stieltjes inversion**: as `η ↓ 0`,
`∫_a^b Im S_ν(x + iη) dx → π (ν(a,b) + ν{a}/2 + ν{b}/2)`. -/
theorem tendsto_interval_im (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] (a b : ℝ /- [definition] -/ ) (hab : a < b /- [standing] -/ ) :
    Tendsto (fun η : ℝ => ∫ x in a..b, (stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im)
      (𝓝[>] 0) (𝓝 (π * (ν.real (Ioo a b) + ν.real {a} / 2 + ν.real {b} / 2))) := by
  rw [← integral_edgeProfile]
  have hev : (fun η : ℝ => ∫ t, (arctan ((b - t) / η) - arctan ((a - t) / η)) ∂ν)
      =ᶠ[𝓝[>] 0] fun η => ∫ x in a..b, (stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact (interval_im ν η a b hη).symm
  refine Tendsto.congr' hev ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => π) ?_ ?_
    (integrable_const π) (Eventually.of_forall fun t => kernel_limit a b t hab)
  · filter_upwards [self_mem_nhdsWithin] with η hη
    refine Continuous.aestronglyMeasurable ?_
    have : (η : ℝ) ≠ 0 := ne_of_gt hη
    fun_prop
  · exact Eventually.of_forall fun η => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs]; exact abs_arctan_sub_le _ _

/-- `x ↦ S_ν(x + iη)` is continuous for `η > 0`. -/
theorem continuous_stieltjes_line (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] (η : ℝ /- [definition] -/ ) (hη : 0 < η /- [standing] -/ ) :
    Continuous fun x : ℝ => stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I) := by
  unfold stieltjes
  refine continuous_of_dominated (bound := fun _ => η⁻¹)
    (fun x => (continuous_kernel x η hη).aestronglyMeasurable)
    (fun x => Eventually.of_forall fun t => norm_kernel_le t x η hη) (integrable_const _)
    (Eventually.of_forall fun t => ?_)
  refine (continuous_const.sub (Complex.continuous_ofReal.add continuous_const)).inv₀ ?_
  intro x h0
  have := congrArg Complex.im h0
  simp at this
  linarith

/-- **Stieltjes inversion on an interval.** Let `ν` be a finite measure on `ℝ`
with Stieltjes transform `S_ν(z) = ∫ (t - z)⁻¹ dν(t)`, and `a < b`. If
`Im S_ν(x + iη) → π f(x)` as `η ↓ 0` for every `x ∈ (a, b]` and
`|Im S_ν(x + iη)|` is bounded for `x ∈ [a, b]` and small `η`, then
`ν(a,b) + ν{a}/2 + ν{b}/2 = ∫_a^b f`. -/
theorem stieltjes_inversion (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] (a b : ℝ /- [definition] -/ ) (hab : a < b /- [standing] -/ )
    (f : ℝ → ℝ /- [definition] -/ )
    (hconv : ∀ x ∈ Ioc a b, Tendsto (fun η : ℝ =>
      (stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] 0) (𝓝 (π * f x)) /- [standing] -/ )
    (C : ℝ /- [definition] -/ ) (hbd : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), ∀ x ∈ Icc a b,
      |(stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im| ≤ C /- [standing] -/ ) :
    ν.real (Ioo a b) + ν.real {a} / 2 + ν.real {b} / 2 = ∫ x in a..b, f x := by
  have T1 := tendsto_interval_im ν a b hab
  have T2 : Tendsto (fun η : ℝ => ∫ x in a..b, (stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im)
      (𝓝[>] 0) (𝓝 (∫ x in a..b, π * f x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [self_mem_nhdsWithin] with η hη
      exact (Complex.continuous_im.comp (continuous_stieltjes_line ν η hη)).aestronglyMeasurable
    · filter_upwards [hbd] with η hη
      refine Eventually.of_forall fun x hx => ?_
      rw [Real.norm_eq_abs]
      rw [Set.uIoc_of_le hab.le] at hx
      exact hη x ⟨hx.1.le, hx.2⟩
    · refine Eventually.of_forall fun x hx => ?_
      rw [Set.uIoc_of_le hab.le] at hx
      exact hconv x hx
  rw [intervalIntegral.integral_const_mul] at T2
  have := tendsto_nhds_unique T1 T2
  have hπ : π ≠ 0 := pi_ne_zero
  exact mul_left_cancel₀ hπ this

/-- The limit function inherits the bound: `|f| ≤ C/π`. -/
theorem abs_limit_le (ν : Measure ℝ /- [definition] -/ ) (x C : ℝ /- [definition] -/ ) (f : ℝ /- [definition] -/ )
    (hconv : Tendsto (fun η : ℝ => (stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] 0)
      (𝓝 (π * f)) /- [standing] -/ )
    (hbd : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), |(stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im| ≤ C /- [standing] -/ ) :
    |f| ≤ C / π := by
  have h := le_of_tendsto (continuous_abs.continuousAt.tendsto.comp hconv) hbd
  simp only [abs_mul, abs_of_pos pi_pos] at h
  rw [le_div_iff₀ pi_pos]; linarith

/-- **No atoms where the boundary values converge boundedly.** -/
theorem atom_zero (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] (x₀ h₀ C : ℝ /- [definition] -/ ) (hh₀ : 0 < h₀ /- [standing] -/ )
    (f : ℝ → ℝ /- [definition] -/ )
    (hconv : ∀ x ∈ Icc (x₀ - h₀) (x₀ + h₀), Tendsto (fun η : ℝ =>
      (stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] 0) (𝓝 (π * f x)) /- [standing] -/ )
    (hbd : ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), ∀ x ∈ Icc (x₀ - h₀) (x₀ + h₀),
      |(stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im| ≤ C /- [standing] -/ ) :
    ν.real {x₀} = 0 := by
  have hf : ∀ x ∈ Icc (x₀ - h₀) (x₀ + h₀), |f x| ≤ C / π := fun x hx =>
    abs_limit_le ν x C (f x) (hconv x hx) (hbd.mono fun η h => h x hx)
  have hC : 0 ≤ C / π := (abs_nonneg _).trans (hf x₀ ⟨by linarith, by linarith⟩)
  have key : ∀ h, 0 < h → h ≤ h₀ → ν.real {x₀} ≤ 2 * h * (C / π) := by
    intro h hh hhh
    have hsub : Icc (x₀ - h) (x₀ + h) ⊆ Icc (x₀ - h₀) (x₀ + h₀) :=
      Icc_subset_Icc (by linarith) (by linarith)
    have hinv := stieltjes_inversion ν (x₀ - h) (x₀ + h) (by linarith) f
      (fun x hx => hconv x (hsub (Ioc_subset_Icc_self hx))) C
      (hbd.mono fun η hη x hx => hη x (hsub hx))
    have hint : ∫ x in (x₀ - h)..(x₀ + h), f x ≤ 2 * h * (C / π) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x₀ - h) (b := x₀ + h)
        (C := C / π) (f := f) (fun x hx => by
          rw [Real.norm_eq_abs]
          rw [Set.uIoc_of_le (by linarith)] at hx
          exact hf x (hsub (Ioc_subset_Icc_self hx)))
      rw [Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < x₀ + h - (x₀ - h))] at this
      have e : x₀ + h - (x₀ - h) = 2 * h := by ring
      rw [e] at this
      linarith [le_abs_self (∫ x in (x₀ - h)..(x₀ + h), f x)]
    have h1 : ν.real {x₀} ≤ ν.real (Ioo (x₀ - h) (x₀ + h)) :=
      measureReal_mono (by
        intro y hy; rw [Set.mem_singleton_iff] at hy; subst hy
        exact ⟨by linarith, by linarith⟩)
    have h2 := measureReal_nonneg (μ := ν) (s := {x₀ - h})
    have h3 := measureReal_nonneg (μ := ν) (s := {x₀ + h})
    linarith
  by_contra hne
  have hpos : 0 < ν.real {x₀} := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
  set δ := ν.real {x₀}
  set h := min h₀ (δ / (4 * (C / π + 1))) with hh
  have hhpos : 0 < h := lt_min hh₀ (by positivity)
  have hk := key h hhpos (min_le_left _ _)
  have hh2 : h ≤ δ / (4 * (C / π + 1)) := min_le_right _ _
  have : 2 * h * (C / π) < δ := by
    rw [le_div_iff₀ (by positivity)] at hh2
    nlinarith
  linarith

/-- **Density on an open interval.** If on `(p, q)` the boundary values converge,
boundedly on compact subintervals, to `π f`, then `ν(a,b) = ∫_a^b f` for all
`p < a < b < q`: `ν` restricted to `(p, q)` has density `f`. -/
theorem stieltjes_density (ν : Measure ℝ /- [definition] -/ ) [IsFiniteMeasure ν /- [standing] -/ ] (p q : ℝ /- [definition] -/ ) (f : ℝ → ℝ /- [definition] -/ )
    (hconv : ∀ x ∈ Ioo p q, Tendsto (fun η : ℝ =>
      (stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im) (𝓝[>] 0) (𝓝 (π * f x)) /- [standing] -/ )
    (hbd : ∀ a b, p < a → b < q → ∃ C, ∀ᶠ η : ℝ in 𝓝[>] (0 : ℝ), ∀ x ∈ Icc a b,
      |(stieltjes ν ((x : ℂ) + (η : ℂ) * Complex.I)).im| ≤ C /- [standing] -/ )
    (a b : ℝ /- [definition] -/ ) (hpa : p < a /- [standing] -/ ) (hab : a < b /- [standing] -/ ) (hbq : b < q /- [standing] -/ ) :
    ν.real (Ioo a b) = ∫ x in a..b, f x := by
  have hatom : ∀ x₀ ∈ Ioo p q, ν.real {x₀} = 0 := by
    intro x₀ hx
    set h₀ := min (x₀ - p) (q - x₀) / 2 with hh
    have hh0 : 0 < h₀ := by have := hx.1; have := hx.2; positivity
    have hh1 : h₀ < x₀ - p := by
      have := min_le_left (x₀ - p) (q - x₀); have := hx.1; linarith
    have hh2 : h₀ < q - x₀ := by
      have := min_le_right (x₀ - p) (q - x₀); have := hx.2; linarith
    obtain ⟨C, hC⟩ := hbd (x₀ - h₀) (x₀ + h₀) (by linarith) (by linarith)
    exact atom_zero ν x₀ h₀ C hh0 f
      (fun x hx' => hconv x ⟨by linarith [hx'.1], by linarith [hx'.2]⟩) hC
  obtain ⟨C, hC⟩ := hbd a b hpa hbq
  have := stieltjes_inversion ν a b hab f
    (fun x hx => hconv x ⟨by linarith [hx.1], by linarith [hx.2]⟩) C hC
  rw [hatom a ⟨hpa, by linarith⟩, hatom b ⟨by linarith, hbq⟩] at this
  linarith

end Inversion
end RMTFoundations.StieltjesInversion

#print axioms RMTFoundations.StieltjesInversion.im_kernel
#print axioms RMTFoundations.StieltjesInversion.norm_kernel_le
#print axioms RMTFoundations.StieltjesInversion.continuous_kernel
#print axioms RMTFoundations.StieltjesInversion.integrable_kernel
#print axioms RMTFoundations.StieltjesInversion.stieltjes_im
#print axioms RMTFoundations.StieltjesInversion.hasDerivAt_arctan_shift
#print axioms RMTFoundations.StieltjesInversion.kernel_nonneg
#print axioms RMTFoundations.StieltjesInversion.kernel_le
#print axioms RMTFoundations.StieltjesInversion.interval_kernel
#print axioms RMTFoundations.StieltjesInversion.interval_im
#print axioms RMTFoundations.StieltjesInversion.arctanLim
#print axioms RMTFoundations.StieltjesInversion.tendsto_arctan_div
#print axioms RMTFoundations.StieltjesInversion.edgeProfile
#print axioms RMTFoundations.StieltjesInversion.kernel_limit
#print axioms RMTFoundations.StieltjesInversion.abs_arctan_sub_le
#print axioms RMTFoundations.StieltjesInversion.integral_edgeProfile
#print axioms RMTFoundations.StieltjesInversion.tendsto_interval_im
#print axioms RMTFoundations.StieltjesInversion.continuous_stieltjes_line
#print axioms RMTFoundations.StieltjesInversion.stieltjes_inversion
#print axioms RMTFoundations.StieltjesInversion.abs_limit_le
#print axioms RMTFoundations.StieltjesInversion.atom_zero
#print axioms RMTFoundations.StieltjesInversion.stieltjes_density
