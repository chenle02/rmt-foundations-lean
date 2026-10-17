import Mathlib
import Challenge.Reference.Airy.Core
namespace RMTFoundations.Airy
open MeasureTheory Set Filter Complex
open scoped ENNReal InnerProductSpace InnerProduct Topology ContDiff SchwartzMap TemperedDistribution
/- Airy inversion with positive damping and no normalization premise. -/
theorem airyAiReal_globally_bounded :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |airyAiReal x| ≤ C := by
  obtain ⟨Cneg, hneg⟩ := airyAiReal_abs_le_nonpos
  obtain ⟨Cpos, hpos, hb⟩ := airyAiReal_abs_le_exp'
  refine ⟨max Cneg Cpos, hpos.trans_le (le_max_right _ _), ?_⟩
  intro x
  by_cases hx : x ≤ 0
  · exact (hneg x hx).trans (le_max_left _ _)
  · have he : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    exact (hb x).trans ((mul_le_of_le_one_right hpos.le he).trans (le_max_right _ _))
noncomputable def airyAiComplexReal (x : ℝ /- [definition] -/) : ℂ := (airyAiReal x : ℂ)
theorem airyAiComplexReal_memLp_top : MemLp airyAiComplexReal ⊤ (volume : Measure ℝ) := by
  obtain ⟨C, _, hC⟩ := airyAiReal_globally_bounded
  exact memLp_top_of_bound
    (Complex.continuous_ofReal.comp continuous_airyAiReal).aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun x => by simpa [airyAiComplexReal] using hC x))
noncomputable def airyAiTempered : TemperedDistribution ℝ ℂ :=
  MeasureTheory.Lp.toTemperedDistribution
    (airyAiComplexReal_memLp_top.toLp airyAiComplexReal)
theorem airyAiTempered_apply (φ : SchwartzMap ℝ ℂ /- [definition] -/) :
    airyAiTempered φ = ∫ x : ℝ, φ x * (airyAiReal x : ℂ) := by
  rw [airyAiTempered, MeasureTheory.Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [airyAiComplexReal_memLp_top.coeFn_toLp] with x hx
  rw [hx]
  rfl

theorem airyAiReal_deriv_polynomial_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ,
      |deriv airyAiReal x| ≤ C * (1 + |x|^2) := by
  obtain ⟨M, hM, hbound⟩ := airyAiReal_globally_bounded
  refine ⟨|deriv airyAiReal 0| + M, by positivity, ?_⟩
  intro x
  have hODE : ∀ t : ℝ, HasDerivAt (deriv airyAiReal) (t * airyAiReal t) t := by
    intro t
    simpa only [← (hasDerivAt_deriv_airyAiReal t).deriv, deriv_deriv_airyAiReal] using
      hasDerivAt_deriv_airyAiReal t
  have hFTC : (∫ t in 0..x, t * airyAiReal t) = deriv airyAiReal x - deriv airyAiReal 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hODE t)
      ((continuous_id.mul continuous_airyAiReal).intervalIntegrable 0 x)
  have hb : ∀ t ∈ Set.uIoc 0 x, ‖t * airyAiReal t‖ ≤ M * |x| := by
    intro t ht
    have ht' : |t| ≤ |x| := by
      by_cases hx : 0 ≤ x
      · rw [Set.uIoc_of_le hx] at ht
        rw [abs_of_nonneg ht.1.le, abs_of_nonneg hx]
        exact ht.2
      · have hx' : x ≤ 0 := le_of_not_ge hx
        rw [Set.uIoc_of_ge hx'] at ht
        rw [abs_of_nonpos ht.2, abs_of_nonpos hx']
        linarith [ht.1]
    rw [Real.norm_eq_abs, abs_mul]
    calc |t| * |airyAiReal t| ≤ |x| * M :=
        mul_le_mul ht' (hbound t) (abs_nonneg _) (abs_nonneg _)
      _ = M * |x| := mul_comm _ _
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [hFTC, Real.norm_eq_abs, sub_zero] at hnorm
  have htri : |deriv airyAiReal x| ≤
      |deriv airyAiReal x - deriv airyAiReal 0| + |deriv airyAiReal 0| := by
    simpa using abs_add_le (deriv airyAiReal x - deriv airyAiReal 0) (deriv airyAiReal 0)
  nlinarith [abs_nonneg (deriv airyAiReal 0), sq_nonneg |x|]
/-- All pairings needed for weak integration by parts are actual integrable functions. -/
theorem schwartz_mul_polynomial_bound_integrable
    (φ : SchwartzMap ℝ ℂ /- [definition] -/) (f : ℝ → ℂ /- [definition] -/)
    (hf : Continuous f /- [standing] -/) (C : ℝ /- [definition] -/)
    (hC : ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|^2) /- [standing] -/ ) :
    Integrable (fun x : ℝ => φ x * f x) := by
  have hi : Integrable (fun x : ℝ => C * (‖φ x‖ + ‖x‖^2 * ‖φ x‖)) :=
    (φ.integrable.norm.add (φ.integrable_pow_mul volume 2)).const_mul C
  apply hi.mono (φ.continuous.mul hf).aestronglyMeasurable
  filter_upwards [] with x
  calc ‖φ x * f x‖ = ‖φ x‖ * ‖f x‖ := norm_mul _ _
    _ ≤ ‖φ x‖ * (C * (1 + |x|^2)) :=
      mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
    _ = C * (‖φ x‖ + ‖x‖^2 * ‖φ x‖) := by rw [Real.norm_eq_abs]; ring
    _ ≤ ‖C * (‖φ x‖ + ‖x‖^2 * ‖φ x‖)‖ := le_abs_self _
theorem airyAi_schwartz_integrable (φ : SchwartzMap ℝ ℂ /- [definition] -/) :
    Integrable (fun x : ℝ => φ x * (airyAiReal x : ℂ)) := by
  obtain ⟨C, hC, hb⟩ := airyAiReal_globally_bounded
  apply schwartz_mul_polynomial_bound_integrable φ _
    (Complex.continuous_ofReal.comp continuous_airyAiReal) C
  intro x
  simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs]
  exact (hb x).trans (show C ≤ C * (1 + |x|^2) by
    nlinarith [mul_nonneg hC.le (sq_nonneg |x|)])
theorem airyAi_deriv_schwartz_integrable (φ : SchwartzMap ℝ ℂ /- [definition] -/) :
    Integrable (fun x : ℝ => φ x * ((deriv airyAiReal x : ℝ) : ℂ)) := by
  obtain ⟨C, _, hb⟩ := airyAiReal_deriv_polynomial_bound
  exact schwartz_mul_polynomial_bound_integrable φ _
    (Complex.continuous_ofReal.comp continuous_deriv_airyAiReal) C
    (fun x => by simpa using hb x)
theorem airyAi_coordinate_schwartz_integrable (φ : SchwartzMap ℝ ℂ /- [definition] -/) :
    Integrable (fun x : ℝ => φ x * (x * airyAiReal x : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := airyAiReal_globally_bounded
  apply schwartz_mul_polynomial_bound_integrable φ _
    (Complex.continuous_ofReal.comp (continuous_id.mul continuous_airyAiReal)) C
  intro x
  simp only [Function.comp_apply, Pi.mul_apply, id_eq, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  calc |x| * |airyAiReal x| ≤ |x| * C :=
      mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)
    _ ≤ C * (1 + |x|^2) := by nlinarith [sq_nonneg (|x| - 1)]
theorem airyAi_schwartz_weak_ode (φ : SchwartzMap ℝ ℂ /- [definition] -/) :
    (∫ x : ℝ, deriv (deriv φ) x * (airyAiReal x : ℂ)) =
      ∫ x : ℝ, φ x * (x * airyAiReal x : ℝ) := by
  let φ' := SchwartzMap.derivCLM ℂ ℂ φ
  have h1 : (∫ x : ℝ, deriv (deriv φ) x * (airyAiReal x : ℂ)) =
      -(∫ x : ℝ, deriv φ x * ((deriv airyAiReal x : ℝ) : ℂ)) := by
    have h := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := fun x : ℝ => (airyAiReal x : ℂ)) (v := (φ' : ℝ → ℂ))
      (fun x _ => (hasDerivAt_airyAiReal' x).ofReal_comp)
      (fun x _ => φ'.hasDerivAt x)
      ((airyAi_schwartz_integrable (SchwartzMap.derivCLM ℂ ℂ φ')).congr
        (by filter_upwards [] with x; simp [φ', SchwartzMap.derivCLM_apply, mul_comm]))
      ((airyAi_deriv_schwartz_integrable φ').congr
        (by filter_upwards [] with x; simp [φ', SchwartzMap.derivCLM_apply, mul_comm]))
      ((airyAi_schwartz_integrable φ').congr (by filter_upwards [] with x; simp [mul_comm]))
    have hd : (φ' : ℝ → ℂ) = deriv φ := funext (fun x => SchwartzMap.derivCLM_apply ℂ φ x)
    rw [hd] at h
    simpa [mul_comm] using h
  have h2 : (∫ x : ℝ, deriv φ x * ((deriv airyAiReal x : ℝ) : ℂ)) =
      -(∫ x : ℝ, φ x * (x * airyAiReal x : ℝ)) := by
    have h := integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := fun x : ℝ => ((deriv airyAiReal x : ℝ) : ℂ)) (v := (φ : ℝ → ℂ))
      (fun x _ => ((by
        simpa only [← (hasDerivAt_deriv_airyAiReal x).deriv, deriv_deriv_airyAiReal] using
          hasDerivAt_deriv_airyAiReal x : HasDerivAt (deriv airyAiReal) (x * airyAiReal x) x).ofReal_comp))
      (fun x _ => φ.hasDerivAt x)
      ((airyAi_deriv_schwartz_integrable (SchwartzMap.derivCLM ℂ ℂ φ)).congr
        (by filter_upwards [] with x; simp [SchwartzMap.derivCLM_apply, mul_comm]))
      ((airyAi_coordinate_schwartz_integrable φ).congr (by filter_upwards [] with x; simp [mul_comm]))
      ((airyAi_deriv_schwartz_integrable φ).congr (by filter_upwards [] with x; simp [mul_comm]))
    simpa [mul_comm] using h
  rw [h1, h2, neg_neg]

open FourierTransform LineDeriv
open scoped SchwartzMap TemperedDistribution
noncomputable def coordinateMultiplier : 𝓢'(ℝ, ℂ) →L[ℂ] 𝓢'(ℝ, ℂ) :=
  TemperedDistribution.smulLeftCLM ℂ (fun x : ℝ => (x : ℂ))
theorem coordinateMultiplier_fourier_deriv (T : 𝓢'(ℝ, ℂ) /- [definition] -/ ) :
    𝓕 (∂_{(1 : ℝ)} T) = (2 * Real.pi * Complex.I) • coordinateMultiplier (𝓕 T) := by
  simpa [coordinateMultiplier, real_inner_comm, RCLike.inner_apply] using
    TemperedDistribution.fourier_lineDerivOp_eq T (1 : ℝ)
theorem coordinateMultiplier_fourier (T : 𝓢'(ℝ, ℂ) /- [definition] -/ ) :
    ∂_{(1 : ℝ)} (𝓕 T) = -(2 * Real.pi * Complex.I) • 𝓕 (coordinateMultiplier T) := by
  ext φ
  simpa [coordinateMultiplier, real_inner_comm, RCLike.inner_apply, smul_apply, neg_mul] using
    congrArg (fun S : 𝓢'(ℝ, ℂ) => S φ)
      (TemperedDistribution.lineDerivOp_fourier_eq T (1 : ℝ))
/-- The exact pinned 2π convention; no pointwise Fourier integrability is assumed. -/
theorem airy_tempered_fourier_ode (T : 𝓢'(ℝ, ℂ) /- [definition] -/ )
    (hODE : ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} T) = coordinateMultiplier T /- [standing] -/) :
    ∂_{(1 : ℝ)} (𝓕 T) = ((2 * Real.pi : ℂ)^3 * Complex.I) •
      coordinateMultiplier (coordinateMultiplier (𝓕 T)) := by
  rw [coordinateMultiplier_fourier, ← hODE, coordinateMultiplier_fourier_deriv,
    coordinateMultiplier_fourier_deriv, map_smul, smul_smul, smul_smul]
  congr 1
  calc -(2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I) * (2 * Real.pi * Complex.I)
      = -((2 * Real.pi : ℂ)^3 * (Complex.I^2 * Complex.I)) := by ring
    _ = _ := by rw [Complex.I_sq]; ring

noncomputable def fourierAiryPhase (x : ℝ /- [definition] -/) : ℂ :=
  Complex.exp (Complex.I * (2 * Real.pi * (x : ℂ))^3 / 3)
theorem fourierAiryPhase_hasDerivAt (x : ℝ /- [definition] -/) :
    HasDerivAt fourierAiryPhase
      (((2 * Real.pi : ℂ)^3 * Complex.I * (x : ℂ)^2) * fourierAiryPhase x) x := by
  have h := (((((hasDerivAt_id x).ofReal_comp).const_mul (2 * Real.pi : ℂ)).pow 3).const_mul Complex.I).div_const 3
  convert! h.cexp using 1 <;> simp only [fourierAiryPhase, id_eq, Pi.pow_apply, Nat.cast_ofNat, Complex.ofReal_one]
  ring
/-- Uniqueness after regularity: this lemma does not assert distributional regularity. -/
theorem classical_fourier_ode_solution (f : ℝ → ℂ /- [definition] -/)
    (hf : ∀ x : ℝ, HasDerivAt f (((2 * Real.pi : ℂ)^3 * Complex.I * (x : ℂ)^2) * f x) x
      /- [standing] -/) (x : ℝ /- [definition] -/) :
    f x = f 0 * fourierAiryPhase x := by
  let g : ℝ → ℂ := fun t => f t / fourierAiryPhase t
  have hg : ∀ t, HasDerivAt g 0 t := by
    intro t
    have h := (hf t).div (fourierAiryPhase_hasDerivAt t) (Complex.exp_ne_zero _)
    convert! h using 1 <;> ring
  have hc : g x = g 0 := is_const_of_deriv_eq_zero
    (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) x 0
  dsimp [g] at hc
  simp [fourierAiryPhase] at hc
  exact (div_eq_iff (Complex.exp_ne_zero _)).mp hc
theorem fourierAiryPhase_norm (x : ℝ /- [definition] -/) : ‖fourierAiryPhase x‖ = 1 := by
  have he : Complex.I * (2 * Real.pi * (x : ℂ))^3 / 3 =
      Complex.I * (((2 * Real.pi * x)^3 / 3 : ℝ) : ℂ) := by push_cast; ring
  change ‖Complex.exp (Complex.I * (2 * Real.pi * (x : ℂ))^3 / 3)‖ = 1
  rw [he, mul_comm Complex.I]
  exact Complex.norm_exp_ofReal_mul_I _
theorem polynomial_real_eval_hasTemperateGrowth (P : Polynomial ℂ /- [definition] -/) :
    (fun x : ℝ => P.eval (x : ℂ)).HasTemperateGrowth := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add, Pi.add_apply] using! hp.add hq
  | monomial n a =>
    simpa only [Polynomial.eval_monomial, Pi.mul_apply, Pi.pow_apply] using!
      (Function.HasTemperateGrowth.const a).mul (Function.Complex.hasTemperateGrowth_ofReal.pow n)
noncomputable def fourierAiryPhaseDerivativePolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | n+1 => (fourierAiryPhaseDerivativePolynomial n).derivative +
      fourierAiryPhaseDerivativePolynomial n *
        (Polynomial.C ((2 * Real.pi : ℂ)^3 * Complex.I) * Polynomial.X^2)
theorem fourierAiryPhase_iteratedDeriv (n : ℕ /- [definition] -/)
    (x : ℝ /- [definition] -/) :
    iteratedDeriv n fourierAiryPhase x =
      (fourierAiryPhaseDerivativePolynomial n).eval (x : ℂ) * fourierAiryPhase x := by
  induction n generalizing x with
  | zero => simp [fourierAiryPhaseDerivativePolynomial]
  | succ n ih =>
    have he : iteratedDeriv n fourierAiryPhase = fun t : ℝ =>
        (fourierAiryPhaseDerivativePolynomial n).eval (t : ℂ) * fourierAiryPhase t :=
      funext ih
    rw [iteratedDeriv_succ, he]
    have h := (((fourierAiryPhaseDerivativePolynomial n).hasDerivAt (x : ℂ)).comp_ofReal).fun_mul
      (fourierAiryPhase_hasDerivAt x)
    rw [h.deriv]
    simp only [fourierAiryPhaseDerivativePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    ring
theorem fourierAiryPhase_hasTemperateGrowth : fourierAiryPhase.HasTemperateGrowth := by
  refine ⟨?_, ?_⟩
  · have hcast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
    unfold fourierAiryPhase
    fun_prop
  · intro n
    obtain ⟨k, C, hb⟩ := (polynomial_real_eval_hasTemperateGrowth
      (fourierAiryPhaseDerivativePolynomial n)).2 0
    refine ⟨k, C, ?_⟩
    intro x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, fourierAiryPhase_iteratedDeriv,
      norm_mul, fourierAiryPhase_norm, mul_one]
    simpa only [norm_iteratedFDeriv_zero] using hb x
noncomputable def inverseFourierAiryPhase (x : ℝ /- [definition] -/) : ℂ := fourierAiryPhase (-x)
theorem inverseFourierAiryPhase_hasTemperateGrowth : inverseFourierAiryPhase.HasTemperateGrowth :=
  fourierAiryPhase_hasTemperateGrowth.comp Function.HasTemperateGrowth.id.neg
theorem inverseFourierAiryPhase_hasDerivAt (x : ℝ /- [definition] -/) :
    HasDerivAt inverseFourierAiryPhase
      (-((2 * Real.pi : ℂ)^3 * Complex.I * (x : ℂ)^2) * inverseFourierAiryPhase x) x := by
  convert! (fourierAiryPhase_hasDerivAt (-x)).scomp x (hasDerivAt_neg' (x := x)) using 1 <;>
    simp [Complex.ofReal_neg, neg_sq, inverseFourierAiryPhase, Complex.real_smul] <;> ring
theorem fourierAiryPhase_mul_inverse (x : ℝ /- [definition] -/) :
    fourierAiryPhase x * inverseFourierAiryPhase x = 1 := by
  simp only [inverseFourierAiryPhase, fourierAiryPhase]
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 1
  congr 1
  push_cast
  ring

noncomputable def schwartzCumulative (φ : 𝓢(ℝ, ℂ) /- [definition] -/ )
    (x : ℝ /- [definition] -/) : ℂ := ∫ t in Set.Iic x, φ t
theorem schwartzCumulative_eq_interval (φ : 𝓢(ℝ, ℂ) /- [definition] -/ )
    (x : ℝ /- [definition] -/) :
    schwartzCumulative φ x = schwartzCumulative φ 0 + ∫ t in 0..x, φ t := by
  have h := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := x) (μ := volume)
    φ.integrable.integrableOn φ.integrable.integrableOn
  dsimp [schwartzCumulative]
  linear_combination h
theorem schwartzCumulative_hasDerivAt (φ : 𝓢(ℝ, ℂ) /- [definition] -/ )
    (x : ℝ /- [definition] -/) : HasDerivAt (schwartzCumulative φ) (φ x) x := by
  have h := (intervalIntegral.integral_hasDerivAt_right
    (φ.continuous.intervalIntegrable 0 x)
    φ.continuous.stronglyMeasurable.stronglyMeasurableAtFilter φ.continuous.continuousAt).const_add
    (schwartzCumulative φ 0)
  rw [show schwartzCumulative φ = (fun t => schwartzCumulative φ 0 + ∫ u in 0..t, φ u) from
    funext (schwartzCumulative_eq_interval φ)]
  exact h
theorem schwartzCumulative_deriv (φ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    deriv (schwartzCumulative φ) = φ := funext (fun x => (schwartzCumulative_hasDerivAt φ x).deriv)
theorem schwartzCumulative_smooth (φ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    ContDiff ℝ ∞ (schwartzCumulative φ) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun x => (schwartzCumulative_hasDerivAt φ x).differentiableAt,
    by rw [schwartzCumulative_deriv]; exact φ.smooth ⊤⟩
theorem schwartz_tail_moment_bound (φ : 𝓢(ℝ, ℂ) /- [definition] -/ )
    (x : ℝ /- [definition] -/) (k : ℕ /- [definition] -/)
    (S : Set ℝ /- [definition] -/)
    (hmS : MeasurableSet S /- [standing] -/)
    (hS : ∀ t ∈ S, |x| ≤ |t| /- [standing] -/) :
    |x|^k * ‖∫ t in S, φ t‖ ≤ ∫ t : ℝ, ‖t‖^k * ‖φ t‖ := by
  have him := φ.integrable_pow_mul volume k
  calc |x|^k * ‖∫ t in S, φ t‖ ≤ |x|^k * ∫ t in S, ‖φ t‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ t in S, |x|^k * ‖φ t‖ := (integral_const_mul _ _).symm
    _ ≤ ∫ t in S, ‖t‖^k * ‖φ t‖ := by
      apply integral_mono_ae (φ.integrable.norm.const_mul _).integrableOn him.integrableOn
      filter_upwards [ae_restrict_mem hmS] with t ht
      rw [Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hS t ht) k)
        (norm_nonneg _)
    _ ≤ ∫ t : ℝ, ‖t‖^k * ‖φ t‖ :=
      setIntegral_le_integral him (Filter.Eventually.of_forall (fun t => by positivity))
theorem schwartzCumulative_decay (φ : 𝓢(ℝ, ℂ) /- [definition] -/ )
    (hφ : ∫ x : ℝ, φ x = 0 /- [standing] -/)
    (k : ℕ /- [definition] -/) (x : ℝ /- [definition] -/) :
    ‖x‖^k * ‖schwartzCumulative φ x‖ ≤ ∫ t : ℝ, ‖t‖^k * ‖φ t‖ := by
  rw [Real.norm_eq_abs]
  by_cases hx : x ≤ 0
  · exact schwartz_tail_moment_bound φ x k (Set.Iic x) measurableSet_Iic (fun t ht => by
      rw [abs_of_nonpos hx, abs_of_nonpos (ht.trans hx)]; exact neg_le_neg ht)
  · have hx' : 0 ≤ x := le_of_not_ge hx
    have he : schwartzCumulative φ x = -(∫ t in Set.Ioi x, φ t) := by
      have h := intervalIntegral.integral_Iic_add_Ioi (b := x) (μ := volume)
        φ.integrable.integrableOn φ.integrable.integrableOn
      rw [hφ] at h
      dsimp [schwartzCumulative]
      exact eq_neg_of_add_eq_zero_left h
    rw [he, norm_neg]
    exact schwartz_tail_moment_bound φ x k (Set.Ioi x) measurableSet_Ioi (fun t ht => by
      rw [abs_of_nonneg hx', abs_of_nonneg (hx'.trans ht.le)]; exact ht.le)
noncomputable def schwartzZeroIntegralPrimitive (φ : 𝓢(ℝ, ℂ) /- [definition] -/ )
    (hφ : ∫ x : ℝ, φ x = 0 /- [standing] -/) : 𝓢(ℝ, ℂ) where
  toFun := schwartzCumulative φ
  smooth' := schwartzCumulative_smooth φ
  decay' := by
    intro k n
    cases n with
    | zero =>
      refine ⟨∫ t : ℝ, ‖t‖^k * ‖φ t‖, ?_⟩
      intro x
      simpa using schwartzCumulative_decay φ hφ k x
    | succ n =>
      obtain ⟨C, _, hC⟩ := φ.decay k n
      refine ⟨C, ?_⟩
      intro x
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ',
        schwartzCumulative_deriv, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hC x
theorem schwartzZeroIntegralPrimitive_deriv (φ : 𝓢(ℝ, ℂ) /- [definition] -/ )
    (hφ : ∫ x : ℝ, φ x = 0 /- [standing] -/) :
    SchwartzMap.derivCLM ℂ ℂ (schwartzZeroIntegralPrimitive φ hφ) = φ := by
  ext x
  rw [SchwartzMap.derivCLM_apply]
  exact (schwartzCumulative_hasDerivAt φ x).deriv
/-- No assumption of a regular-function representative for the distribution. -/
theorem tempered_deriv_zero_eq_constant_on_tests
    (T : 𝓢'(ℝ, ℂ) /- [definition] -/ )
    (hT : TemperedDistribution.derivCLM ℂ T = 0 /- [standing] -/)
    (ψ : 𝓢(ℝ, ℂ) /- [definition] -/ )
    (hψ : ∫ x : ℝ, ψ x = 1 /- [standing] -/)
    (φ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    T φ = (∫ x : ℝ, φ x) * T ψ := by
  let η := φ - (∫ x : ℝ, φ x) • ψ
  have hη : ∫ x : ℝ, η x = 0 := by
    simp only [η, SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul]
    rw [integral_sub φ.integrable (ψ.integrable.const_mul _), integral_const_mul, hψ]
    ring
  have hh := DFunLike.congr_fun hT (schwartzZeroIntegralPrimitive η hη)
  rw [TemperedDistribution.derivCLM_apply_apply,
    schwartzZeroIntegralPrimitive_deriv] at hh
  have hz : T η = 0 := by simpa using hh
  simpa only [η, map_sub, map_smul, smul_eq_mul, sub_eq_zero] using hz

noncomputable def normalizedSchwartzTest : 𝓢(ℝ, ℂ) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  exact (b.hasCompactSupport_normed (μ := volume)).comp_left (g := Complex.ofReal)
    (by simp) |>.toSchwartzMap (by exact Complex.ofRealCLM.contDiff.comp b.contDiff_normed)
theorem normalizedSchwartzTest_integral : ∫ x : ℝ, normalizedSchwartzTest x = 1 := by
  change (∫ x : ℝ, ((ContDiffBump.normed
    (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)) volume x : ℝ) : ℂ)) = 1
  rw [integral_complex_ofReal, ContDiffBump.integral_normed]
  norm_num
theorem tempered_deriv_zero_eq_constant (T : 𝓢'(ℝ, ℂ) /- [definition] -/ )
    (hT : TemperedDistribution.derivCLM ℂ T = 0 /- [standing] -/) :
    T = (T normalizedSchwartzTest) • (volume : Measure ℝ).toTemperedDistribution := by
  ext φ
  rw [tempered_deriv_zero_eq_constant_on_tests T hT normalizedSchwartzTest
    normalizedSchwartzTest_integral φ]
  simp only [smul_apply, smul_eq_mul,
    MeasureTheory.Measure.toTemperedDistribution_apply]
  ring
theorem schwartz_deriv_integral_zero (φ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    ∫ x : ℝ, (SchwartzMap.derivCLM ℂ ℂ φ) x = 0 := by
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun _ : ℝ => (1 : ℂ)) (u' := fun _ => (0 : ℂ)) (v := φ)
    (v' := SchwartzMap.derivCLM ℂ ℂ φ)
    (fun x _ => hasDerivAt_const x 1) (fun x _ => φ.hasDerivAt x)
    (by
      change Integrable (fun x : ℝ => (1 : ℂ) * (SchwartzMap.derivCLM ℂ ℂ φ) x)
      simp only [one_mul]
      exact (SchwartzMap.derivCLM ℂ ℂ φ).integrable (μ := volume))
    (by
      change Integrable (fun x : ℝ => (0 : ℂ) * φ x)
      simp only [zero_mul]
      exact integrable_zero ℝ ℂ volume)
    (by
      change Integrable (fun x : ℝ => (1 : ℂ) * φ x)
      simp only [one_mul]
      exact φ.integrable (μ := volume))
  simpa using h
/-- The primitive bundle is inhabited on a nonzero, zero-integral test. -/
theorem schwartzPrimitive_nonzero_probe :
    ∃ φ : 𝓢(ℝ, ℂ), φ ≠ 0 ∧ ∃ hφ : (∫ x : ℝ, φ x) = 0,
      schwartzZeroIntegralPrimitive φ hφ ≠ 0 ∧
      SchwartzMap.derivCLM ℂ ℂ (schwartzZeroIntegralPrimitive φ hφ) = φ := by
  let φ := SchwartzMap.derivCLM ℂ ℂ normalizedSchwartzTest
  have hφ : ∫ x : ℝ, φ x = 0 := schwartz_deriv_integral_zero normalizedSchwartzTest
  have hn : φ ≠ 0 := by
    intro hz
    have hd : ∀ x, deriv normalizedSchwartzTest x = 0 := by
      intro x
      have hh := congrArg (fun f : 𝓢(ℝ, ℂ) => f x) hz
      simpa [φ, SchwartzMap.derivCLM_apply] using hh
    have he : (normalizedSchwartzTest : ℝ → ℂ) = fun _ => normalizedSchwartzTest 0 :=
      funext (fun x => is_const_of_deriv_eq_zero
        (fun t => (normalizedSchwartzTest.hasDerivAt t).differentiableAt) hd x 0)
    have hi := normalizedSchwartzTest_integral
    rw [he] at hi
    simpa [MeasureTheory.Measure.real, Real.volume_univ] using hi
  refine ⟨φ, hn, hφ, ?_, schwartzZeroIntegralPrimitive_deriv φ hφ⟩
  intro hz
  have h := schwartzZeroIntegralPrimitive_deriv φ hφ
  rw [hz, map_zero] at h
  exact hn h.symm


theorem schwartz_deriv_smulLeft (g g' : ℝ → ℂ /- [definition] -/)
    (hg : g.HasTemperateGrowth /- [standing] -/)
    (hg' : g'.HasTemperateGrowth /- [standing] -/)
    (hder : ∀ x : ℝ, HasDerivAt g (g' x) x /- [standing] -/)
    (φ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    SchwartzMap.derivCLM ℂ ℂ (SchwartzMap.smulLeftCLM ℂ g φ) =
      SchwartzMap.smulLeftCLM ℂ g' φ +
        SchwartzMap.smulLeftCLM ℂ g (SchwartzMap.derivCLM ℂ ℂ φ) := by
  ext x
  have he : (SchwartzMap.smulLeftCLM ℂ g φ : ℝ → ℂ) = fun t => g t * φ t :=
    funext (fun t => by simp [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul])
  simp only [SchwartzMap.derivCLM_apply, he, add_apply,
    SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.smulLeftCLM_apply_apply hg',
    smul_eq_mul]
  exact ((hder x).fun_mul (φ.hasDerivAt x)).deriv
theorem tempered_deriv_smulLeft (g g' : ℝ → ℂ /- [definition] -/)
    (hg : g.HasTemperateGrowth /- [standing] -/)
    (hg' : g'.HasTemperateGrowth /- [standing] -/)
    (hder : ∀ x : ℝ, HasDerivAt g (g' x) x /- [standing] -/)
    (T : 𝓢'(ℝ, ℂ) /- [definition] -/ ) :
    TemperedDistribution.derivCLM ℂ (TemperedDistribution.smulLeftCLM ℂ g T) =
      TemperedDistribution.smulLeftCLM ℂ g' T +
        TemperedDistribution.smulLeftCLM ℂ g (TemperedDistribution.derivCLM ℂ T) := by
  ext φ
  simp only [TemperedDistribution.derivCLM_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, map_neg,
    schwartz_deriv_smulLeft g g' hg hg' hder, add_apply, map_add]
  abel


theorem schwartz_lineDeriv_one (φ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    ∂_{(1 : ℝ)} φ = SchwartzMap.derivCLM ℂ ℂ φ := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.derivCLM_apply,
    fderiv_apply_one_eq_deriv]
theorem tempered_lineDeriv_one (T : 𝓢'(ℝ, ℂ) /- [definition] -/ ) :
    ∂_{(1 : ℝ)} T = TemperedDistribution.derivCLM ℂ T := by
  ext φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply, schwartz_lineDeriv_one,
    TemperedDistribution.derivCLM_apply_apply]
noncomputable def fourierAiryPhaseTempered : 𝓢'(ℝ, ℂ) :=
  fourierAiryPhase_hasTemperateGrowth.toTemperedDistribution volume
/-- A distributional first-order ODE; all regularity comes from Schwartz test functions. -/
theorem tempered_cubic_ode_integrating_factor (U : 𝓢'(ℝ, ℂ) /- [definition] -/ )
    (hU : ∂_{(1 : ℝ)} U = ((2 * Real.pi : ℂ)^3 * Complex.I) •
      coordinateMultiplier (coordinateMultiplier U) /- [standing] -/ ) :
    TemperedDistribution.derivCLM ℂ
      (TemperedDistribution.smulLeftCLM ℂ inverseFourierAiryPhase U) = 0 := by
  let α : ℂ := (2 * Real.pi : ℂ)^3 * Complex.I
  let g' : ℝ → ℂ := fun x => -α * (x : ℂ)^2 * inverseFourierAiryPhase x
  have hg' : g'.HasTemperateGrowth := by
    exact ((Function.HasTemperateGrowth.const (-α)).mul
      (Function.Complex.hasTemperateGrowth_ofReal.pow 2)).mul
      inverseFourierAiryPhase_hasTemperateGrowth
  have hder : ∀ x : ℝ, HasDerivAt inverseFourierAiryPhase (g' x) x := by
    intro x
    simpa [g', α, neg_mul] using inverseFourierAiryPhase_hasDerivAt x
  rw [tempered_deriv_smulLeft inverseFourierAiryPhase g'
    inverseFourierAiryPhase_hasTemperateGrowth hg' hder]
  rw [← tempered_lineDeriv_one, hU, map_smul]
  have hc : TemperedDistribution.smulLeftCLM ℂ g' U =
      (-α) • TemperedDistribution.smulLeftCLM ℂ inverseFourierAiryPhase
        (coordinateMultiplier (coordinateMultiplier U)) := by
    ext φ
    simp only [coordinateMultiplier, TemperedDistribution.smulLeftCLM_apply_apply,
      smul_apply]
    rw [← map_smul]
    congr 1
    ext x
    simp only [SchwartzMap.smulLeftCLM_apply_apply hg',
      SchwartzMap.smulLeftCLM_apply_apply Function.Complex.hasTemperateGrowth_ofReal,
      SchwartzMap.smulLeftCLM_apply_apply inverseFourierAiryPhase_hasTemperateGrowth,
      smul_apply, smul_eq_mul, g']
    ring
  rw [hc]
  ext φ
  simp [α, smul_apply]
theorem phase_multiplier_inverse (U : 𝓢'(ℝ, ℂ) /- [definition] -/ ) :
    TemperedDistribution.smulLeftCLM ℂ fourierAiryPhase
      (TemperedDistribution.smulLeftCLM ℂ inverseFourierAiryPhase U) = U := by
  ext φ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply]
  congr 1
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply inverseFourierAiryPhase_hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply fourierAiryPhase_hasTemperateGrowth, smul_eq_mul]
  calc inverseFourierAiryPhase x * (fourierAiryPhase x * φ x) =
      (fourierAiryPhase x * inverseFourierAiryPhase x) * φ x := by ring
    _ = φ x := by rw [fourierAiryPhase_mul_inverse, one_mul]
theorem phase_multiplier_volume :
    TemperedDistribution.smulLeftCLM ℂ fourierAiryPhase
      (volume : Measure ℝ).toTemperedDistribution = fourierAiryPhaseTempered := by
  ext φ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply,
    MeasureTheory.Measure.toTemperedDistribution_apply,
    SchwartzMap.smulLeftCLM_apply_apply fourierAiryPhase_hasTemperateGrowth,
    fourierAiryPhaseTempered, Function.HasTemperateGrowth.toTemperedDistribution_apply,
    smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  exact mul_comm _ _
theorem tempered_cubic_ode_solution (U : 𝓢'(ℝ, ℂ) /- [definition] -/ )
    (hU : ∂_{(1 : ℝ)} U = ((2 * Real.pi : ℂ)^3 * Complex.I) •
      coordinateMultiplier (coordinateMultiplier U) /- [standing] -/ ) :
    ∃ c : ℂ, U = c • fourierAiryPhaseTempered := by
  let V := TemperedDistribution.smulLeftCLM ℂ inverseFourierAiryPhase U
  have hv : TemperedDistribution.derivCLM ℂ V = 0 :=
    tempered_cubic_ode_integrating_factor U hU
  refine ⟨V normalizedSchwartzTest, ?_⟩
  calc U = TemperedDistribution.smulLeftCLM ℂ fourierAiryPhase V :=
      (phase_multiplier_inverse U).symm
    _ = _ := by
      have hh := congrArg (TemperedDistribution.smulLeftCLM ℂ fourierAiryPhase)
        (tempered_deriv_zero_eq_constant V hv)
      simpa only [map_smul, phase_multiplier_volume] using hh
theorem tempered_airy_fourier_proportional (T : 𝓢'(ℝ, ℂ) /- [definition] -/ )
    (hODE : ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} T) = coordinateMultiplier T /- [standing] -/) :
    ∃ c : ℂ, 𝓕 T = c • fourierAiryPhaseTempered :=
  tempered_cubic_ode_solution (𝓕 T) (airy_tempered_fourier_ode T hODE)
theorem airyAiTempered_ode :
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} airyAiTempered) = coordinateMultiplier airyAiTempered := by
  ext φ
  rw [tempered_lineDeriv_one, tempered_lineDeriv_one]
  simp only [TemperedDistribution.derivCLM_apply_apply, map_neg, neg_neg,
    coordinateMultiplier, TemperedDistribution.smulLeftCLM_apply_apply]
  rw [airyAiTempered_apply, airyAiTempered_apply]
  have hd : (SchwartzMap.derivCLM ℂ ℂ φ : ℝ → ℂ) = deriv φ :=
    funext (fun x => SchwartzMap.derivCLM_apply ℂ φ x)
  simp only [SchwartzMap.derivCLM_apply]
  rw [hd]
  simpa only [SchwartzMap.derivCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply Function.Complex.hasTemperateGrowth_ofReal,
    smul_eq_mul, Complex.ofReal_mul, mul_assoc, mul_left_comm] using
      airyAi_schwartz_weak_ode φ
theorem airyAiTempered_ne_zero : airyAiTempered ≠ 0 := by
  intro hz
  let f : Lp ℂ ⊤ (volume : Measure ℝ) := airyAiComplexReal_memLp_top.toLp airyAiComplexReal
  have hf : f = 0 := by
    have hk : f ∈ (Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) ⊤).ker := by
      change airyAiTempered = 0
      exact hz
    rw [Lp.ker_toTemperedDistributionCLM_eq_bot] at hk
    simpa using hk
  have hae : airyAiComplexReal =ᵐ[volume] 0 :=
    (airyAiComplexReal_memLp_top.coeFn_toLp).symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp hf)
  have he := (Continuous.ae_eq_iff_eq (volume : Measure ℝ)
    (Complex.continuous_ofReal.comp continuous_airyAiReal) continuous_zero).mp hae
  have h0 := congr_fun he 0
  have hz' : airyAiReal 0 = 0 := by simpa [airyAiComplexReal] using h0
  exact airyAiReal_zero_pos.ne' hz'
noncomputable def airyFourierNormalizationTest : 𝓢(ℝ, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ inverseFourierAiryPhase normalizedSchwartzTest
theorem fourierAiryPhaseTempered_normalization_test :
    fourierAiryPhaseTempered airyFourierNormalizationTest = 1 := by
  change (∫ x : ℝ, airyFourierNormalizationTest x • fourierAiryPhase x) = 1
  calc (∫ x : ℝ, airyFourierNormalizationTest x • fourierAiryPhase x) =
      ∫ x : ℝ, normalizedSchwartzTest x := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [airyFourierNormalizationTest,
          SchwartzMap.smulLeftCLM_apply_apply inverseFourierAiryPhase_hasTemperateGrowth,
          smul_eq_mul]
        calc (inverseFourierAiryPhase x * normalizedSchwartzTest x) * fourierAiryPhase x =
            (fourierAiryPhase x * inverseFourierAiryPhase x) * normalizedSchwartzTest x := by ring
          _ = normalizedSchwartzTest x := by rw [fourierAiryPhase_mul_inverse, one_mul]
    _ = 1 := normalizedSchwartzTest_integral
noncomputable def airyFourierCoefficient : ℂ :=
  (𝓕 airyAiTempered) airyFourierNormalizationTest
/-- Genuine power-series Ai. The remaining unit normalization is not assumed here. -/
theorem airyAi_fourier_eq_coefficient_phase :
    𝓕 airyAiTempered = airyFourierCoefficient • fourierAiryPhaseTempered := by
  obtain ⟨c, hc⟩ := tempered_airy_fourier_proportional airyAiTempered airyAiTempered_ode
  have he : airyFourierCoefficient = c := by
    rw [airyFourierCoefficient, hc, smul_apply, fourierAiryPhaseTempered_normalization_test,
      smul_eq_mul, mul_one]
  rw [he]
  exact hc
theorem airyFourierCoefficient_integral :
    airyFourierCoefficient = ∫ x : ℝ,
      (𝓕 airyFourierNormalizationTest) x * (airyAiReal x : ℂ) := by
  rw [airyFourierCoefficient, TemperedDistribution.fourier_apply, airyAiTempered_apply]
theorem airyFourierCoefficient_ne_zero : airyFourierCoefficient ≠ 0 := by
  intro hz
  have hh : 𝓕 airyAiTempered = 0 := by
    rw [airyAi_fourier_eq_coefficient_phase, hz]
    ext φ
    simp [smul_apply, smul_eq_mul]
  have hi := congrArg (fun T : 𝓢'(ℝ, ℂ) => 𝓕⁻ T) hh
  simp only [fourierInv_fourier_eq, fourierInv_zero] at hi
  exact airyAiTempered_ne_zero hi
theorem airyAi_fourier_joint_probe :
    airyAiTempered ≠ 0 ∧
    ∂_{(1 : ℝ)} (∂_{(1 : ℝ)} airyAiTempered) = coordinateMultiplier airyAiTempered ∧
    ∂_{(1 : ℝ)} (𝓕 airyAiTempered) = ((2 * Real.pi : ℂ)^3 * Complex.I) •
      coordinateMultiplier (coordinateMultiplier (𝓕 airyAiTempered)) ∧
    airyFourierCoefficient ≠ 0 ∧
    (∫ x : ℝ, normalizedSchwartzTest x) = 1 :=
  ⟨airyAiTempered_ne_zero, airyAiTempered_ode,
    airy_tempered_fourier_ode airyAiTempered airyAiTempered_ode,
    airyFourierCoefficient_ne_zero, normalizedSchwartzTest_integral⟩
theorem fourierAiryPhaseTempered_ne_zero : fourierAiryPhaseTempered ≠ 0 := by
  intro hz
  have h := fourierAiryPhaseTempered_normalization_test
  rw [hz] at h
  simpa using h
theorem airyAi_fourier_eq_phase_iff_coefficient_one :
    𝓕 airyAiTempered = fourierAiryPhaseTempered ↔ airyFourierCoefficient = 1 := by
  constructor
  · intro h
    rw [airyFourierCoefficient, h, fourierAiryPhaseTempered_normalization_test]
  · intro h
    rw [airyAi_fourier_eq_coefficient_phase, h]
    ext φ
    simp [smul_apply, smul_eq_mul]
/-- An explicit scalar goal for the unfinished unit normalization. -/
theorem airyAi_fourier_eq_phase_iff_scalar_integral_one :
    𝓕 airyAiTempered = fourierAiryPhaseTempered ↔
      (∫ x : ℝ, (𝓕 airyFourierNormalizationTest) x * (airyAiReal x : ℂ)) = 1 := by
  rw [airyAi_fourier_eq_phase_iff_coefficient_one, airyFourierCoefficient_integral]


open Asymptotics
open scoped Asymptotics
noncomputable def airyLeadF (z u : ℝ /- [definition] -/) : ℝ :=
  Real.exp (-z * (Real.cosh (u / Real.sqrt z) - 1)) * Real.cosh (u / Real.sqrt z / 3)

/-- `airyLeadF z` is continuous in `u` for every `z`. -/
theorem continuous_airyLeadF (z : ℝ /- [definition] -/) : Continuous fun u => airyLeadF z u := by
  unfold airyLeadF
  fun_prop

/-- **The quadratic-gap bound for `cosh`**: `cosh s - 1 - s²/2 ≤ (s²/2)(cosh s - 1)`.
Termwise comparison of the power series: for `n ≥ 2`,
`s^{2n}/(2n)! ≤ (s²/2) · s^{2n-2}/(2n-2)!` since `(2n)! = (2n)(2n-1)·(2n-2)! ≥ 2·(2n-2)!`. -/
theorem cosh_sub_one_sub_half_sq_le (s : ℝ /- [definition] -/) :
    Real.cosh s - 1 - s ^ 2 / 2 ≤ (s ^ 2 / 2) * (Real.cosh s - 1) := by
  have hs : Summable (fun n : ℕ => s ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) :=
    (Real.hasSum_cosh s).summable
  have hs1 : Summable (fun i : ℕ => s ^ (2 * (i + 1)) / (Nat.factorial (2 * (i + 1)) : ℝ)) :=
    (summable_nat_add_iff 1).2 hs
  have hs2 : Summable (fun i : ℕ => s ^ (2 * (i + 2)) / (Nat.factorial (2 * (i + 2)) : ℝ)) :=
    (summable_nat_add_iff 2).2 hs
  have hpt : ∀ i : ℕ, s ^ (2 * (i + 2)) / (Nat.factorial (2 * (i + 2)) : ℝ)
      ≤ (s ^ 2 / 2) * (s ^ (2 * (i + 1)) / (Nat.factorial (2 * (i + 1)) : ℝ)) := by
    intro i
    have hfact : (Nat.factorial (2 * (i + 2)) : ℝ)
        = ((2 * i + 4) * (2 * i + 3) : ℝ) * (Nat.factorial (2 * (i + 1)) : ℝ) := by
      rw [show 2 * (i + 2) = (2 * i + 3) + 1 from by ring, Nat.factorial_succ,
        show 2 * i + 3 = (2 * i + 2) + 1 from by ring, Nat.factorial_succ,
        show 2 * i + 2 = 2 * (i + 1) from by ring]
      push_cast
      ring
    have hpow : s ^ (2 * (i + 2)) = s ^ 2 * s ^ (2 * (i + 1)) := by
      rw [show 2 * (i + 2) = 2 + 2 * (i + 1) from by ring, pow_add]
    have hC : (2:ℝ) ≤ ((2 * i + 4) * (2 * i + 3) : ℝ) := by
      have h1 : (4:ℕ) ≤ 2 * i + 4 := by omega
      have h2 : (3:ℕ) ≤ 2 * i + 3 := by omega
      have h3 := Nat.mul_le_mul h1 h2
      calc (2:ℝ) ≤ (12:ℕ) := by norm_num
        _ ≤ (2 * i + 4) * (2 * i + 3) := by exact_mod_cast h3
    have hC0 : (0:ℝ) < ((2 * i + 4) * (2 * i + 3) : ℝ) := by linarith [hC]
    have hB : (0:ℝ) < (Nat.factorial (2 * (i + 1)) : ℝ) := by positivity
    rw [hpow, hfact,
      show (s ^ 2 / 2) * (s ^ (2 * (i + 1)) / (Nat.factorial (2 * (i + 1)) : ℝ))
        = (s ^ 2 / 2 * s ^ (2 * (i + 1))) / (Nat.factorial (2 * (i + 1)) : ℝ) from
        (mul_div_assoc _ _ _).symm,
      div_le_div_iff₀ (mul_pos hC0 hB) hB]
    calc s ^ 2 * s ^ (2 * (i + 1)) * (Nat.factorial (2 * (i + 1)) : ℝ)
        = (s ^ 2 / 2 * s ^ (2 * (i + 1))) * (2 * (Nat.factorial (2 * (i + 1)) : ℝ)) := by ring
      _ ≤ (s ^ 2 / 2 * s ^ (2 * (i + 1)))
          * (((2 * i + 4) * (2 * i + 3) : ℝ) * (Nat.factorial (2 * (i + 1)) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _
            (mul_nonneg (by positivity : (0:ℝ) ≤ s ^ 2 / 2)
              (by rw [pow_mul]; positivity : (0:ℝ) ≤ s ^ (2 * (i + 1))))
          exact mul_le_mul_of_nonneg_right hC hB.le
  have h01 : (s ^ (2 * 0) / (Nat.factorial (2 * 0) : ℝ)
      + s ^ (2 * 1) / (Nat.factorial (2 * 1) : ℝ)) = 1 + s ^ 2 / 2 := by
    norm_num
  have h0 : (s ^ (2 * 0) / (Nat.factorial (2 * 0) : ℝ)) = 1 := by
    norm_num
  calc Real.cosh s - 1 - s ^ 2 / 2
      = ∑' i : ℕ, s ^ (2 * (i + 2)) / (Nat.factorial (2 * (i + 2)) : ℝ) := by
        rw [Real.cosh_eq_tsum, ← hs.sum_add_tsum_nat_add 2,
          show Finset.range 2 = {0, 1} from by decide,
          Finset.sum_insert (by norm_num), Finset.sum_singleton, h01]
        ring
    _ ≤ ∑' i : ℕ, (s ^ 2 / 2) * (s ^ (2 * (i + 1)) / (Nat.factorial (2 * (i + 1)) : ℝ)) :=
        hs2.tsum_le_tsum hpt (hs1.mul_left _)
    _ = (s ^ 2 / 2) * ∑' i : ℕ, s ^ (2 * (i + 1)) / (Nat.factorial (2 * (i + 1)) : ℝ) :=
        tsum_mul_left
    _ = (s ^ 2 / 2) * (Real.cosh s - 1) := by
        rw [Real.cosh_eq_tsum, ← hs.sum_add_tsum_nat_add 1,
          show Finset.range 1 = {0} from by decide, Finset.sum_singleton, h0]
        ring

/-- `u / √z → 0` as `z → ∞`. -/
theorem tendsto_div_sqrt_atTop (u : ℝ /- [definition] -/) :
    Tendsto (fun z : ℝ => u / Real.sqrt z) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop).const_mul u
  rw [mul_zero] at h
  refine h.congr' (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, div_eq_mul_inv]

/-- For `0 < z` and `0 ≤ u`: `z * (cosh (u/√z) - 1) ≥ u²/2` (from `cosh s ≥ 1 + s²/2`). -/
theorem mul_cosh_div_sqrt_sub_one_ge {z u : ℝ /- [definition] -/} (hz : 0 < z /- [standing] -/) (_hu : 0 ≤ u /- [standing] -/) :
    u ^ 2 / 2 ≤ z * (Real.cosh (u / Real.sqrt z) - 1) := by
  have h := one_add_sq_div_two_le_cosh (u / Real.sqrt z)
  have h2 : z * ((u / Real.sqrt z) ^ 2 / 2) = u ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt hz.le]
    field_simp [hz.ne']
  calc u ^ 2 / 2 = z * ((u / Real.sqrt z) ^ 2 / 2) := h2.symm
    _ ≤ z * (Real.cosh (u / Real.sqrt z) - 1) :=
        mul_le_mul_of_nonneg_left (by linarith [h]) hz.le

/-- `z * (cosh (u/√z) - 1) → u²/2` as `z → ∞` (squeeze between `u²/2` and
`u²/2 + (u²/2)(cosh (u/√z) - 1)` via `cosh_sub_one_sub_half_sq_le`). -/
theorem tendsto_mul_cosh_div_sqrt_sub_one {u : ℝ /- [definition] -/} (hu : 0 < u /- [standing] -/) :
    Tendsto (fun z : ℝ => z * (Real.cosh (u / Real.sqrt z) - 1)) atTop (𝓝 (u ^ 2 / 2)) := by
  have h0 := tendsto_div_sqrt_atTop u
  have hcosh : Tendsto (fun z : ℝ => Real.cosh (u / Real.sqrt z)) atTop (𝓝 1) := by
    have h := (Real.continuous_cosh.tendsto 0).comp h0
    rwa [Real.cosh_zero] at h
  have hup : Tendsto (fun z : ℝ => u ^ 2 / 2 + (u ^ 2 / 2) * (Real.cosh (u / Real.sqrt z) - 1))
      atTop (𝓝 (u ^ 2 / 2)) := by
    have h : Tendsto (fun z : ℝ => u ^ 2 / 2 + (u ^ 2 / 2) * (Real.cosh (u / Real.sqrt z) - 1))
        atTop (𝓝 (u ^ 2 / 2 + (u ^ 2 / 2) * (1 - 1))) :=
      (tendsto_const_nhds (x := u ^ 2 / 2)).add
        ((tendsto_const_nhds (x := u ^ 2 / 2)).mul (hcosh.sub_const 1))
    rwa [sub_self, mul_zero, add_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with z hz
    exact mul_cosh_div_sqrt_sub_one_ge hz hu.le
  · filter_upwards [eventually_gt_atTop 0] with z hz
    have h := cosh_sub_one_sub_half_sq_le (u / Real.sqrt z)
    have h2 : z * ((u / Real.sqrt z) ^ 2 / 2) = u ^ 2 / 2 := by
      rw [div_pow, Real.sq_sqrt hz.le]
      field_simp [hz.ne']
    have h3 := mul_le_mul_of_nonneg_left h hz.le
    rw [mul_sub, h2] at h3
    have h4 : z * ((u / Real.sqrt z) ^ 2 / 2 * (Real.cosh (u / Real.sqrt z) - 1))
        = (u ^ 2 / 2) * (Real.cosh (u / Real.sqrt z) - 1) := by
      rw [← mul_assoc, h2]
    rw [h4] at h3
    linarith [h3]

/-- **Dominated convergence for the rescaled Schläfli family**: if `W z u` is continuous
in `u`, nonnegative on `[0, ∞)`, bounded by `e^{C u}` for `z ≥ 1`, and converges pointwise
to `1` as `z → ∞`, then `∫₀^∞ W z · airyLeadF z → ∫₀^∞ e^{-u²/2} du`. -/
theorem tendsto_integral_airyLeadF_mul (W : ℝ → ℝ → ℝ /- [definition] -/) {C : ℝ /- [definition] -/} (_hC : 0 ≤ C /- [standing] -/)
    (hW_cont : ∀ z, Continuous fun u => W z u /- [standing] -/)
    (hW_nn : ∀ z u, 0 ≤ u → 0 ≤ W z u /- [standing] -/)
    (hW_bound : ∀ z, 1 ≤ z → ∀ u, 0 ≤ u → W z u ≤ Real.exp (C * u) /- [standing] -/ )
    (hW_lim : ∀ u, 0 < u → Tendsto (fun z => W z u) atTop (𝓝 1) /- [standing] -/ ) :
    Tendsto (fun z => ∫ u in Set.Ioi 0, W z u * airyLeadF z u) atTop
      (𝓝 (∫ u in Set.Ioi 0, Real.exp (-(1/2) * u ^ 2))) := by
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun u => Real.exp ((C + 1/3) ^ 2) * Real.exp (-(1/4) * u ^ 2)) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun z =>
      ((hW_cont z).mul (continuous_airyLeadF z)).aestronglyMeasurable
  · filter_upwards [eventually_ge_atTop 1] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0:ℝ) ≤ u := hu.le
    have hz0 : (0:ℝ) < z := by linarith
    have h1 : Real.exp (-z * (Real.cosh (u / Real.sqrt z) - 1)) ≤ Real.exp (-(u ^ 2 / 2)) := by
      apply Real.exp_le_exp.2
      rw [neg_mul]
      exact neg_le_neg (mul_cosh_div_sqrt_sub_one_ge hz0 hu0)
    have hdiv : u / Real.sqrt z ≤ u := by
      calc u / Real.sqrt z ≤ u / 1 :=
            div_le_div_of_nonneg_left hu0 zero_lt_one (Real.one_le_sqrt.2 hz)
        _ = u := div_one u
    have h2 : Real.cosh (u / Real.sqrt z / 3) ≤ Real.exp (u / 3) := by
      calc Real.cosh (u / Real.sqrt z / 3)
          ≤ Real.exp |u / Real.sqrt z / 3| := cosh_le_exp_abs _
        _ = Real.exp (u / Real.sqrt z / 3) := by
            congr 1
            exact abs_of_nonneg (by positivity)
        _ ≤ Real.exp (u / 3) :=
            Real.exp_le_exp.2 ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 3)).2 hdiv)
    have hnn : 0 ≤ W z u * airyLeadF z u :=
      mul_nonneg (hW_nn z u hu0) (mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le)
    rw [Real.norm_of_nonneg hnn]
    calc W z u * airyLeadF z u
        ≤ Real.exp (C * u) * (Real.exp (-(u ^ 2 / 2)) * Real.exp (u / 3)) := by
          apply mul_le_mul (hW_bound z hz u hu0) _ _
            (Real.exp_pos _).le
          · exact mul_le_mul h1 h2 (Real.cosh_pos _).le (Real.exp_pos _).le
          · exact mul_nonneg (Real.exp_pos _).le (Real.cosh_pos _).le
      _ = Real.exp (C * u + (-(u ^ 2 / 2) + u / 3)) := by
          rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp ((C + 1/3) ^ 2) * Real.exp (-(1/4) * u ^ 2) := by
          rw [← Real.exp_add]
          apply Real.exp_le_exp.2
          have h4 : (C + 1/3) * u ≤ u ^ 2 / 4 + (C + 1/3) ^ 2 := by
            have h5 := sq_nonneg (u / 2 - (C + 1/3))
            nlinarith
          nlinarith
  · exact ((integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/4)).const_mul _).integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0:ℝ) < u := hu
    have h1 := tendsto_mul_cosh_div_sqrt_sub_one hu0
    have h2 : Tendsto (fun z : ℝ => Real.exp (-(z * (Real.cosh (u / Real.sqrt z) - 1))))
        atTop (𝓝 (Real.exp (-(1/2) * u ^ 2))) := by
      have h := (Real.continuous_exp.tendsto _).comp h1.neg
      rwa [show -(u ^ 2 / 2) = -(1/2) * u ^ 2 from by ring] at h
    have h3 : Tendsto (fun z : ℝ => Real.cosh (u / Real.sqrt z / 3)) atTop (𝓝 1) := by
      have h0 := (tendsto_div_sqrt_atTop u).div_const 3
      rw [zero_div] at h0
      have h := (Real.continuous_cosh.tendsto 0).comp h0
      rwa [Real.cosh_zero] at h
    have h4 := (hW_lim u hu0).mul (h2.mul h3)
    rw [one_mul, mul_one] at h4
    refine h4.congr' (Eventually.of_forall fun z => ?_)
    show W z u * (Real.exp (-(z * (Real.cosh (u / Real.sqrt z) - 1))) * Real.cosh (u / Real.sqrt z / 3))
      = W z u * airyLeadF z u
    unfold airyLeadF
    rw [neg_mul]

/-- The normalized half-line Gaussian integral: `√(2/π) ∫₀^∞ e^{-u²/2} du = 1`. -/
theorem sqrt_two_div_pi_mul_integral_exp_neg_half_sq :
    Real.sqrt (2 / Real.pi) * ∫ u in Set.Ioi 0, Real.exp (-(1/2) * u ^ 2) = 1 := by
  rw [integral_gaussian_Ioi, show Real.pi / (1/2 : ℝ) = 2 * Real.pi from by field_simp,
    ← mul_div_assoc, ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 / Real.pi),
    show (2 / Real.pi) * (2 * Real.pi) = (2:ℝ) ^ 2 from by field_simp [Real.pi_ne_zero],
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- **Master Laplace lemma**: for a weight `w z t` that is continuous in `t`, nonnegative
on `[0, ∞)`, bounded by `e^{C t}` for `z ≥ 1`, and satisfies `w z (t/√z) → 1` as `z → ∞`,
the weighted Schläfli integral has the exact leading asymptotics
`∫₀^∞ w(z,t) e^{-z cosh t} cosh(t/3) dt ~ √(π/(2z)) e^{-z}`. -/
theorem schlaefli_master_isEquivalent (w : ℝ → ℝ → ℝ /- [definition] -/) {C : ℝ /- [definition] -/} (hC : 0 ≤ C /- [standing] -/)
    (hw_cont : ∀ z, Continuous fun t => w z t /- [standing] -/)
    (hw_nn : ∀ z t, 0 ≤ t → 0 ≤ w z t /- [standing] -/)
    (hw_bound : ∀ z, 1 ≤ z → ∀ t, 0 ≤ t → w z t ≤ Real.exp (C * t) /- [standing] -/ )
    (hw_lim : ∀ t, 0 < t → Tendsto (fun z => w z (t / Real.sqrt z)) atTop (𝓝 1) /- [standing] -/ ) :
    (fun z => ∫ t in Set.Ioi 0, w z t * (Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)))
      ~[atTop] fun z => Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z) := by
  have hDCT := tendsto_integral_airyLeadF_mul (fun z u => w z (u / Real.sqrt z)) hC
    (fun z => (hw_cont z).comp (continuous_id.div_const _))
    (fun z u hu => hw_nn z _ (div_nonneg hu (Real.sqrt_nonneg _)))
    (fun z hz u hu => (hw_bound z hz _ (div_nonneg hu (Real.sqrt_nonneg _))).trans
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left
        (by
          calc u / Real.sqrt z ≤ u / 1 :=
                div_le_div_of_nonneg_left hu zero_lt_one (Real.one_le_sqrt.2 hz)
            _ = u := div_one u)
        hC)))
    hw_lim
  have hne : ∀ᶠ z in atTop, (fun z => Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z)) z ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with z hz
    positivity
  rw [isEquivalent_iff_tendsto_one hne]
  have hlim : Tendsto (fun z => Real.sqrt (2 / Real.pi) *
      ∫ u in Set.Ioi 0, w z (u / Real.sqrt z) * airyLeadF z u) atTop (𝓝 1) := by
    have h := hDCT.const_mul (Real.sqrt (2 / Real.pi))
    rwa [sqrt_two_div_pi_mul_integral_exp_neg_half_sq] at h
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with z hz
  have hzsq : (0:ℝ) < Real.sqrt z := Real.sqrt_pos.2 hz
  have hE : ∀ t : ℝ, Real.exp (-z * Real.cosh t)
      = Real.exp (-z) * Real.exp (-z * (Real.cosh t - 1)) := by
    intro t
    rw [← Real.exp_add]
    congr 1
    ring
  have hI1 : (∫ t in Set.Ioi 0, w z t * (Real.exp (-z * Real.cosh t) * Real.cosh (t / 3)))
      = Real.exp (-z) * ∫ t in Set.Ioi 0, w z t *
        (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    show w z t * (Real.exp (-z * Real.cosh t) * Real.cosh (t / 3))
      = Real.exp (-z) * (w z t * (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)))
    rw [hE t]
    ring
  have hconv : (∫ u in Set.Ioi 0, w z (u / Real.sqrt z) * airyLeadF z u)
      = (∫ u in Set.Ioi 0, w z ((Real.sqrt z)⁻¹ * u) *
        (Real.exp (-z * (Real.cosh ((Real.sqrt z)⁻¹ * u) - 1)) *
          Real.cosh ((Real.sqrt z)⁻¹ * u / 3))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u _
    show w z (u / Real.sqrt z) * (Real.exp (-z * (Real.cosh (u / Real.sqrt z) - 1)) *
        Real.cosh (u / Real.sqrt z / 3))
      = w z ((Real.sqrt z)⁻¹ * u) * (Real.exp (-z * (Real.cosh ((Real.sqrt z)⁻¹ * u) - 1)) *
        Real.cosh ((Real.sqrt z)⁻¹ * u / 3))
    rw [show u / Real.sqrt z = (Real.sqrt z)⁻¹ * u from by rw [div_eq_mul_inv, mul_comm]]
  have hsub : (∫ u in Set.Ioi 0, w z ((Real.sqrt z)⁻¹ * u) *
        (Real.exp (-z * (Real.cosh ((Real.sqrt z)⁻¹ * u) - 1)) *
          Real.cosh ((Real.sqrt z)⁻¹ * u / 3)))
      = Real.sqrt z * ∫ t in Set.Ioi 0, w z t *
        (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)) := by
    have h := integral_comp_mul_left_Ioi
      (fun t => w z t * (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3)))
      (0 : ℝ) (b := (Real.sqrt z)⁻¹) (inv_pos.2 hzsq)
    simpa only [inv_inv, mul_zero, smul_eq_mul] using h
  show Real.sqrt (2 / Real.pi) * ∫ u in Set.Ioi 0, w z (u / Real.sqrt z) * airyLeadF z u
    = (∫ t in Set.Ioi 0, w z t * (Real.exp (-z * Real.cosh t) * Real.cosh (t / 3))) /
      (Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z))
  rw [hconv, hsub, hI1]
  set I := ∫ t in Set.Ioi 0, w z t * (Real.exp (-z * (Real.cosh t - 1)) * Real.cosh (t / 3))
    with hI
  have hsp : (0:ℝ) < Real.sqrt (Real.pi / (2 * z)) := Real.sqrt_pos.2 (by positivity)
  have hee : Real.exp (-z) ≠ 0 := (Real.exp_pos _).ne'
  rw [show Real.sqrt (2 / Real.pi) * (Real.sqrt z * I)
      = I * (Real.sqrt (2 / Real.pi) * Real.sqrt z) from by ring,
    mul_comm (Real.sqrt (Real.pi / (2 * z))) (Real.exp (-z)), mul_div_mul_left _ _ hee]
  rw [← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 / Real.pi)]
  rw [show (2 / Real.pi) * z = 2 * z / Real.pi from by ring]
  rw [eq_div_iff hsp.ne', mul_assoc,
    ← Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * z / Real.pi),
    show (2 * z / Real.pi) * (Real.pi / (2 * z)) = 1 from by
      field_simp [Real.pi_ne_zero, hz.ne'],
    Real.sqrt_one, mul_one]

/-- **D1: the exact leading asymptotics of the Schläfli `K_{1/3}` integral**:
`schlaefliK13 z ~ √(π/(2z)) e^{-z}` as `z → ∞` (Laplace's method). -/
theorem schlaefliK13_isEquivalent :
    schlaefliK13 ~[atTop] fun z => Real.sqrt (Real.pi / (2 * z)) * Real.exp (-z) := by
  have h := schlaefli_master_isEquivalent (fun _ _ => 1) zero_le_one
    (fun _ => continuous_const) (fun _ _ _ => zero_le_one)
    (fun z hz t ht => by
      rw [one_mul]
      exact Real.one_le_exp_iff.2 ht)
    (fun t _ => tendsto_const_nhds)
  refine h.congr_left (Eventually.of_forall fun z => ?_)
  unfold schlaefliK13
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  simp only [one_mul]

theorem sqrt_pi_div_two_mul_g {x : ℝ /- [definition] -/} (hx : 0 < x /- [standing] -/) :
    Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ))))
      = ((3:ℝ) ^ (1/2 : ℝ) * Real.sqrt Real.pi / 2) * x ^ (-3/4 : ℝ) := by
  have hxp : (0:ℝ) ≤ x := hx.le
  have h2 : Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ))) = (3 * Real.pi / 4) * x ^ (-3/2 : ℝ) := by
    have hy : (0:ℝ) < x ^ (3/2 : ℝ) := Real.rpow_pos_of_pos hx _
    rw [show (-3/2 : ℝ) = -(3/2 : ℝ) from by norm_num, Real.rpow_neg hxp]
    field_simp [hy.ne', Real.pi_ne_zero]
    ring
  have h3 : Real.sqrt ((3 * Real.pi / 4) * x ^ (-3/2 : ℝ))
      = Real.sqrt (3 * Real.pi / 4) * Real.sqrt (x ^ (-3/2 : ℝ)) :=
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 3 * Real.pi / 4) _
  have h4 : Real.sqrt (x ^ (-3/2 : ℝ)) = x ^ (-3/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hxp]
    norm_num
  have h5 : Real.sqrt (3 * Real.pi / 4) = (3:ℝ) ^ (1/2 : ℝ) * Real.sqrt Real.pi / 2 := by
    rw [show (3 * Real.pi / 4 : ℝ) = (3 * Real.pi) / 2 ^ 2 from by ring,
      Real.sqrt_div (by positivity : (0:ℝ) ≤ 3 * Real.pi), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2),
      Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_eq_rpow]
  rw [h2, h3, h4, h5]

/-- The constant identity `√π / (2π) = 1 / (2√π)`. -/
theorem sqrt_pi_div_two_mul_pi : Real.sqrt Real.pi / (2 * Real.pi)
    = 1 / (2 * Real.sqrt Real.pi) := by
  have hsp : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  rw [eq_div_iff (by positivity : (0:ℝ) < 2 * Real.sqrt Real.pi).ne']
  rw [show Real.sqrt Real.pi / (2 * Real.pi) * (2 * Real.sqrt Real.pi)
      = (Real.sqrt Real.pi * Real.sqrt Real.pi) / Real.pi from by
    field_simp [hsp.ne', Real.pi_ne_zero]]
  rw [Real.mul_self_sqrt Real.pi_pos.le, div_self Real.pi_ne_zero]

/-- The D3 prefactor identity: for `0 < x`,
`(1/π) √(x/3) √(π/(2 ((2/3) x^{3/2}))) = (1/(2√π)) x^{-1/4}`. -/
theorem airyAiReal_prefactor {x : ℝ /- [definition] -/} (hx : 0 < x /- [standing] -/) :
    (1 / Real.pi) * Real.sqrt (x / 3) * Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ))))
      = (1 / (2 * Real.sqrt Real.pi)) * x ^ (-1/4 : ℝ) := by
  have hxp : (0:ℝ) ≤ x := hx.le
  rw [sqrt_pi_div_two_mul_g hx]
  have h1 : Real.sqrt (x / 3) = x ^ (1/2 : ℝ) / (3:ℝ) ^ (1/2 : ℝ) := by
    rw [Real.sqrt_div hxp, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [h1]
  have h2 : (1 / Real.pi) * (x ^ (1/2 : ℝ) / (3:ℝ) ^ (1/2 : ℝ)) *
      (((3:ℝ) ^ (1/2 : ℝ) * Real.sqrt Real.pi / 2) * x ^ (-3/4 : ℝ))
      = ((3:ℝ) ^ (1/2 : ℝ) * Real.sqrt Real.pi / (2 * Real.pi * (3:ℝ) ^ (1/2 : ℝ))) *
        (x ^ (1/2 : ℝ) * x ^ (-3/4 : ℝ)) := by ring
  rw [h2]
  have h3 : x ^ (1/2 : ℝ) * x ^ (-3/4 : ℝ) = x ^ (-1/4 : ℝ) := by
    rw [← Real.rpow_add hx]
    norm_num
  rw [h3]
  have hs3 : (0:ℝ) < (3:ℝ) ^ (1/2 : ℝ) := by positivity
  rw [show 2 * Real.pi * (3:ℝ) ^ (1/2 : ℝ) = (3:ℝ) ^ (1/2 : ℝ) * (2 * Real.pi) from by ring,
    mul_div_mul_left _ _ hs3.ne', sqrt_pi_div_two_mul_pi]

/-- **D3: the exact leading asymptotics of the Airy function** (DLMF 9.7.5):
`Ai(x) ~ (1/(2√π)) x^{-1/4} e^{-(2/3) x^{3/2}}` as `x → ∞`, via the Airy–Bessel
identity and Laplace asymptotics of the Schläfli integral at `z = (2/3) x^{3/2}`. -/
theorem airyAiReal_isEquivalent :
    airyAiReal ~[atTop] fun x => (1 / (2 * Real.sqrt Real.pi)) * x ^ (-1/4 : ℝ) *
      Real.exp (-(2/3) * x ^ (3/2 : ℝ)) := by
  have hg : Tendsto (fun x : ℝ => (2/3) * x ^ (3/2 : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0:ℝ) < 2/3)).2
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3/2))
  have hAi : airyAiReal =ᶠ[atTop] fun x => (1 / Real.pi) * Real.sqrt (x / 3) *
      schlaefliK13 ((2/3) * x ^ (3/2 : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with x hx
    rw [airyAiReal_eq_airyBesselY_div_pi hx]
    unfold airyBesselY
    rw [div_eq_mul_inv, one_div]
    ring
  have hK : (fun x => schlaefliK13 ((2/3) * x ^ (3/2 : ℝ))) ~[atTop]
      fun x => Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
        Real.exp (-((2/3) * x ^ (3/2 : ℝ))) :=
    schlaefliK13_isEquivalent.comp_tendsto hg
  have hmul : (fun x => (1 / Real.pi) * Real.sqrt (x / 3) *
      schlaefliK13 ((2/3) * x ^ (3/2 : ℝ))) ~[atTop]
      fun x => (1 / Real.pi) * Real.sqrt (x / 3) *
        (Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
          Real.exp (-((2/3) * x ^ (3/2 : ℝ)))) :=
    IsEquivalent.refl.mul hK
  refine hAi.isEquivalent.trans (hmul.trans_eventuallyEq ?_)
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [show (1 / Real.pi) * Real.sqrt (x / 3) *
      (Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ)))) *
        Real.exp (-((2/3) * x ^ (3/2 : ℝ))))
    = ((1 / Real.pi) * Real.sqrt (x / 3) * Real.sqrt (Real.pi / (2 * ((2/3) * x ^ (3/2 : ℝ))))) *
      Real.exp (-((2/3) * x ^ (3/2 : ℝ))) from by ring, airyAiReal_prefactor hx, neg_mul]


noncomputable def airyLaplaceProfile (r : ℝ /- [definition] -/) : ℝ :=
  Real.sqrt r * airyAiReal (r^2) * Real.exp ((2/3) * r^3)
theorem airyLaplaceProfile_continuous : Continuous airyLaplaceProfile := by
  unfold airyLaplaceProfile
  exact (Real.continuous_sqrt.mul (continuous_airyAiReal.comp (continuous_id.pow 2))).mul
    (by fun_prop)
theorem airyLaplaceProfile_tendsto :
    Tendsto airyLaplaceProfile atTop (𝓝 (1 / (2 * Real.sqrt Real.pi))) := by
  have hr : Tendsto (fun r : ℝ => r^2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have he := airyAiReal_isEquivalent.comp_tendsto hr
  have hm := ((IsEquivalent.refl (u := fun r : ℝ => Real.sqrt r)).mul he).mul
    (IsEquivalent.refl (u := fun r : ℝ => Real.exp ((2/3) * r^3)))
  have heq : (fun r : ℝ => Real.sqrt r *
      ((1 / (2 * Real.sqrt Real.pi)) * (r^2)^(-1/4 : ℝ) *
        Real.exp (-(2/3) * (r^2)^(3/2 : ℝ))) * Real.exp ((2/3)*r^3)) =ᶠ[atTop]
      (fun _ => 1 / (2 * Real.sqrt Real.pi)) := by
    filter_upwards [eventually_gt_atTop 0] with r hr
    have hpow : (r^2)^(-1/4 : ℝ) = r^(-1/2 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      norm_num
    have hcube : (r^2)^(3/2 : ℝ) = r^3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le]
      norm_num
    have hroot : Real.sqrt r * r^(-1/2 : ℝ) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hr]
      norm_num
    rw [hpow, hcube]
    calc _ = (1 / (2 * Real.sqrt Real.pi)) * (Real.sqrt r * r^(-1/2 : ℝ)) *
        (Real.exp (-((2/3)*r^3)) * Real.exp ((2/3)*r^3)) := by ring
      _ = _ := by rw [hroot, ← Real.exp_add]; simp
  apply (hm.trans_eventuallyEq heq).tendsto_const
/-- Genuine non-event readiness for the future Laplace saddle calculation. -/
theorem airyLaplaceProfile_bounded :
    ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 ≤ r → |airyLaplaceProfile r| ≤ M := by
  let G : ℝ := 1 / (2 * Real.sqrt Real.pi)
  have he : ∀ᶠ r : ℝ in atTop, |airyLaplaceProfile r| < |G| + 1 :=
    (airyLaplaceProfile_tendsto.abs).eventually (eventually_lt_nhds (by dsimp [G]; linarith))
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp he
  let A := max R 0
  obtain ⟨r₀, hr₀, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (by exact ⟨0, by simp [A]⟩ : (Set.Icc (0 : ℝ) A).Nonempty)
    airyLaplaceProfile_continuous.abs.continuousOn
  refine ⟨max |airyLaplaceProfile r₀| (|G| + 1),
    (by positivity : 0 < |G| + 1).trans_le (le_max_right _ _), ?_⟩
  intro r hr
  by_cases h : r ≤ A
  · exact (hmax ⟨hr, h⟩).trans (le_max_left _ _)
  · exact (hR r ((le_max_left R 0).trans (le_of_not_ge h))).le.trans (le_max_right _ _)
noncomputable def laplaceSaddleDensity (g : ℝ → ℝ /- [definition] -/)
    (β u : ℝ /- [definition] -/) : ℝ :=
  if -(β * Real.sqrt β) ≤ u then
    2 * Real.sqrt (1 + u / (β * Real.sqrt β)) * g (β + u / Real.sqrt β) *
      Real.exp (-u^2 - (2/3) * u^3 / (β * Real.sqrt β))
  else 0
theorem laplaceSaddle_exponent_le (β u : ℝ /- [definition] -/)
    (hβ : 1 ≤ β /- [standing] -/) (hu : -(β * Real.sqrt β) ≤ u /- [standing] -/) :
    -u^2 - (2/3) * u^3 / (β * Real.sqrt β) ≤ -(1/3) * u^2 := by
  have hA : 0 < β * Real.sqrt β := mul_pos (by linarith) (Real.sqrt_pos.mpr (by linarith))
  have hmul : 0 ≤ u^2 * (u + β * Real.sqrt β) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  apply (mul_le_mul_iff_of_pos_right hA).mp
  calc (-u^2 - (2/3) * u^3 / (β * Real.sqrt β)) * (β * Real.sqrt β) =
      -(u^2 * (β * Real.sqrt β)) - (2/3) * u^3 := by field_simp <;> ring
    _ ≤ -(1/3) * u^2 * (β * Real.sqrt β) := by nlinarith [hmul]
theorem laplaceSaddle_factor_le (β u : ℝ /- [definition] -/)
    (hβ : 1 ≤ β /- [standing] -/) :
    Real.sqrt (1 + u / (β * Real.sqrt β)) ≤ 1 + |u| := by
  have hs : 1 ≤ Real.sqrt β := Real.one_le_sqrt.mpr hβ
  have hA : 1 ≤ β * Real.sqrt β := by nlinarith
  have hAp : 0 < β * Real.sqrt β := by linarith
  have hu : u / (β * Real.sqrt β) ≤ |u| := by
    calc u / (β * Real.sqrt β) ≤ |u| / (β * Real.sqrt β) :=
        div_le_div_of_nonneg_right (le_abs_self _) hAp.le
      _ ≤ |u| / 1 := div_le_div_of_nonneg_left (abs_nonneg _) zero_lt_one hA
      _ = |u| := div_one _
  apply (Real.sqrt_le_left (by positivity : 0 ≤ 1 + |u|)).mpr
  nlinarith [sq_nonneg |u|, abs_nonneg u]
theorem laplaceSaddle_density_bound (g : ℝ → ℝ /- [definition] -/)
    (M β u : ℝ /- [definition] -/) (hM : 0 ≤ M /- [standing] -/)
    (hg : ∀ r : ℝ, 0 ≤ r → |g r| ≤ M /- [standing] -/)
    (hβ : 1 ≤ β /- [standing] -/) :
    ‖laplaceSaddleDensity g β u‖ ≤ 2 * M * (1 + |u|) * Real.exp (-(1/3) * u^2) := by
  unfold laplaceSaddleDensity
  split_ifs with hu
  · have hs : 0 < Real.sqrt β := Real.sqrt_pos.mpr (by linarith)
    have hr : 0 ≤ β + u / Real.sqrt β := by
      apply (mul_le_mul_iff_of_pos_right hs).mp
      calc (0 : ℝ) * Real.sqrt β ≤ β * Real.sqrt β + u := by linarith
        _ = (β + u / Real.sqrt β) * Real.sqrt β := by field_simp <;> ring
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul
      (mul_le_mul_of_nonneg_left (hg _ hr) (by positivity : 0 ≤ 2 * Real.sqrt (1 + u / (β * Real.sqrt β))))
      (Real.exp_le_exp.mpr (laplaceSaddle_exponent_le β u hβ hu))
      (Real.exp_pos _).le (by positivity : 0 ≤ 2 * Real.sqrt (1 + u / (β * Real.sqrt β)) * M)
    calc _ ≤ (2 * Real.sqrt (1 + u / (β * Real.sqrt β)) * M) *
          Real.exp (-(1/3) * u^2) := h
      _ ≤ (2 * (1 + |u|) * M) * Real.exp (-(1/3) * u^2) := by
        gcongr
        exact laplaceSaddle_factor_le β u hβ
      _ = _ := by ring
  · simp only [norm_zero]
    positivity
theorem laplaceSaddle_envelope_integrable (M : ℝ /- [definition] -/) :
    Integrable (fun u : ℝ => 2 * M * (1 + |u|) * Real.exp (-(1/3) * u^2)) := by
  have h0 := integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/3)
  have h1 := (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/3)).norm
  have h1' : Integrable (fun u : ℝ => |u| * Real.exp (-(1/3) * u^2)) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using h1
  convert (h0.add h1').const_mul (2 * M) using 1
  funext u
  simp only [Pi.add_apply]
  ring
theorem laplaceSaddle_pointwise_tendsto (g : ℝ → ℝ /- [definition] -/)
    (G : ℝ /- [definition] -/) (hg : Tendsto g atTop (𝓝 G) /- [standing] -/ )
    (u : ℝ /- [definition] -/) :
    Tendsto (fun β => laplaceSaddleDensity g β u) atTop (𝓝 (2 * G * Real.exp (-u^2))) := by
  have hA : Tendsto (fun β : ℝ => β * Real.sqrt β) atTop atTop :=
    tendsto_id.atTop_mul_atTop₀ Real.tendsto_sqrt_atTop
  have hi := tendsto_inv_atTop_zero.comp hA
  have hfrac : Tendsto (fun β : ℝ => u / (β * Real.sqrt β)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hi)
  have hr0 : Tendsto (fun β : ℝ => u / Real.sqrt β) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop))
  have hr : Tendsto (fun β : ℝ => β + u / Real.sqrt β) atTop atTop :=
    tendsto_id.atTop_add hr0
  have hs : Tendsto (fun β : ℝ => Real.sqrt (1 + u / (β * Real.sqrt β))) atTop (𝓝 1) := by
    simpa only [Function.comp_apply, add_zero, Real.sqrt_one] using!
      Real.continuous_sqrt.continuousAt.tendsto.comp ((tendsto_const_nhds (x := (1 : ℝ))).add hfrac)
  have hsmall : Tendsto (fun β : ℝ => (2/3) * u^3 / (β * Real.sqrt β)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hi)
  have he : Tendsto (fun β : ℝ => Real.exp (-u^2 - (2/3) * u^3 / (β * Real.sqrt β)))
      atTop (𝓝 (Real.exp (-u^2))) := by
    simpa only [Function.comp_apply, sub_zero] using!
      Real.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := -u^2)).sub hsmall)
  have hh := (((tendsto_const_nhds (x := (2 : ℝ))).mul hs).mul (hg.comp hr)).mul he
  simp only [mul_one] at hh
  apply hh.congr'
  filter_upwards [hA.eventually (eventually_ge_atTop (-u))] with β hβ
  simp only [Function.comp_apply, laplaceSaddleDensity, if_pos (by linarith : -(β * Real.sqrt β) ≤ u)]
theorem laplaceSaddle_integral_tendsto (g : ℝ → ℝ /- [definition] -/)
    (M G : ℝ /- [definition] -/) (hM : 0 ≤ M /- [standing] -/)
    (hc : Continuous g /- [standing] -/)
    (hb : ∀ r : ℝ, 0 ≤ r → |g r| ≤ M /- [standing] -/)
    (hg : Tendsto g atTop (𝓝 G) /- [standing] -/ ) :
    Tendsto (fun β => ∫ u : ℝ, laplaceSaddleDensity g β u)
      atTop (𝓝 (2 * G * Real.sqrt Real.pi)) := by
  have hh := tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => 2 * M * (1 + |u|) * Real.exp (-(1/3) * u^2))
    (f := fun u : ℝ => 2 * G * Real.exp (-u^2))
    (Filter.Eventually.of_forall (fun β => by
      unfold laplaceSaddleDensity
      apply Measurable.aestronglyMeasurable
      apply Measurable.ite (measurableSet_le measurable_const measurable_id)
      · exact (by fun_prop : Continuous (fun u : ℝ =>
          2 * Real.sqrt (1 + u / (β * Real.sqrt β)) * g (β + u / Real.sqrt β) *
          Real.exp (-u^2 - (2/3) * u^3 / (β * Real.sqrt β)))).measurable
      · exact measurable_const))
    (by
      filter_upwards [eventually_ge_atTop 1] with β hβ
      exact ae_of_all _ (fun u => laplaceSaddle_density_bound g M β u hM hb hβ))
    (laplaceSaddle_envelope_integrable M)
    (ae_of_all _ (fun u => laplaceSaddle_pointwise_tendsto g G hg u))
  have hi : (∫ u : ℝ, 2 * G * Real.exp (-u^2)) = 2 * G * Real.sqrt Real.pi := by
    rw [integral_const_mul]
    have h := integral_gaussian (1 : ℝ)
    simpa using congrArg (fun r : ℝ => 2 * G * r) h
  rw [hi] at hh
  exact hh
theorem laplaceSaddle_joint_probe :
    (0 : ℝ) < 1 ∧ Continuous (fun _ : ℝ => (1 : ℝ)) ∧
    (∀ r : ℝ, 0 ≤ r → |(1 : ℝ)| ≤ 1) ∧
    Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun β => ∫ u : ℝ, laplaceSaddleDensity (fun _ => 1) β u)
      atTop (𝓝 (2 * Real.sqrt Real.pi)) := by
  refine ⟨zero_lt_one, continuous_const, (fun _ _ => by norm_num), tendsto_const_nhds, ?_⟩
  simpa using laplaceSaddle_integral_tendsto (fun _ => 1) 1 1 zero_le_one continuous_const
    (fun _ _ => by norm_num) tendsto_const_nhds
theorem laplaceSaddle_cubic_identity (q u : ℝ /- [definition] -/)
    (hq : q ≠ 0 /- [standing] -/) :
    (2/3)*(q^2+u/q)^3 - u^2 - (2/3)*u^3/q^3 =
      q^2*(q^2+u/q)^2-(q^2)^3/3 := by
  field_simp <;> ring
noncomputable def airyLaplaceSquareDensity (β r : ℝ /- [definition] -/) : ℝ :=
  if 0 < r then 2 * r * airyAiReal (r^2) * Real.exp (β*r^2-β^3/3) else 0
theorem airyLaplaceSaddle_pointwise (β u : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    laplaceSaddleDensity airyLaplaceProfile β u =
      (Real.sqrt β)⁻¹ * airyLaplaceSquareDensity β (β + u / Real.sqrt β) := by
  let r := β + u / Real.sqrt β
  have hq : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hsq : (Real.sqrt β)^2 = β := Real.sq_sqrt hβ.le
  have hcube : (Real.sqrt β)^3 = β * Real.sqrt β := by rw [pow_succ, hsq]
  have hr : 0 ≤ r ↔ -(β * Real.sqrt β) ≤ u := by
    dsimp [r]
    constructor
    · intro h
      have hh := mul_nonneg h hq.le
      field_simp at hh
      nlinarith
    · intro h
      apply (mul_le_mul_iff_of_pos_right hq).mp
      calc (0 : ℝ) * Real.sqrt β ≤ β * Real.sqrt β + u := by linarith
        _ = (β + u / Real.sqrt β) * Real.sqrt β := by field_simp <;> ring
  change (if -(β * Real.sqrt β) ≤ u then
    2 * Real.sqrt (1 + u / (β * Real.sqrt β)) * airyLaplaceProfile r *
      Real.exp (-u^2 - (2/3)*u^3/(β*Real.sqrt β)) else 0) =
    (Real.sqrt β)⁻¹ * (if 0 < r then
      2*r*airyAiReal (r^2)*Real.exp (β*r^2-β^3/3) else 0)
  by_cases hrp : 0 < r
  · have hu := hr.mp hrp.le
    have hs : 1 + u / (β * Real.sqrt β) = r / β := by dsimp [r]; field_simp <;> ring
    have hroot : Real.sqrt (r / β) * Real.sqrt r = r / Real.sqrt β := by
      rw [Real.sqrt_div hrp.le]
      calc Real.sqrt r / Real.sqrt β * Real.sqrt r = (Real.sqrt r)^2 / Real.sqrt β := by ring
        _ = _ := by rw [Real.sq_sqrt hrp.le]
    have he := laplaceSaddle_cubic_identity (Real.sqrt β) u hq.ne'
    rw [hsq, hcube] at he
    change (2/3)*r^3 - u^2 - (2/3)*u^3/(β*Real.sqrt β) = β*r^2-β^3/3 at he
    simp only [if_pos hu, if_pos hrp, airyLaplaceProfile, hs]
    calc _ = 2 * (Real.sqrt (r / β) * Real.sqrt r) * airyAiReal (r^2) *
        (Real.exp ((2/3)*r^3) * Real.exp (-u^2-(2/3)*u^3/(β*Real.sqrt β))) := by ring
      _ = _ := by
        rw [hroot, ← Real.exp_add]
        have he' : (2/3)*r^3 + (-u^2-(2/3)*u^3/(β*Real.sqrt β)) =
            β*r^2-β^3/3 := by linarith [he]
        rw [he']
        ring
  · by_cases hrz : r = 0
    · have hu := hr.mp (hrz ▸ le_rfl)
      have hzero : u = -(β * Real.sqrt β) := by
        have hh := congrArg (fun t : ℝ => t * Real.sqrt β) hrz
        dsimp [r] at hh
        field_simp at hh
        linarith
      simp [hu, airyLaplaceProfile, hrz, hzero, hβ.ne', hq.ne']
    · have hneg : ¬ -(β * Real.sqrt β) ≤ u := by
        intro hu
        exact hrz (le_antisymm (le_of_not_gt hrp) (hr.mpr hu))
      simp only [if_neg hneg, if_neg hrp, mul_zero]
theorem airyLaplaceSaddle_integral_eq (β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    (∫ u : ℝ, laplaceSaddleDensity airyLaplaceProfile β u) =
      ∫ x in Set.Ioi (0 : ℝ), airyAiReal x * Real.exp (β*x-β^3/3) := by
  have hq : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  calc (∫ u : ℝ, laplaceSaddleDensity airyLaplaceProfile β u) =
      (Real.sqrt β)⁻¹ * ∫ u : ℝ, airyLaplaceSquareDensity β (β + u / Real.sqrt β) := by
        simp_rw [airyLaplaceSaddle_pointwise β _ hβ]
        rw [integral_const_mul]
    _ = ∫ r : ℝ, airyLaplaceSquareDensity β r := by
      rw [Measure.integral_comp_div (fun v : ℝ => airyLaplaceSquareDensity β (β+v)),
        abs_of_pos hq, smul_eq_mul,
        integral_add_left_eq_self (airyLaplaceSquareDensity β) β]
      field_simp
    _ = ∫ r in Set.Ioi (0 : ℝ), 2*r*airyAiReal (r^2)*Real.exp (β*r^2-β^3/3) := by
      change (∫ r : ℝ, (Set.Ioi (0 : ℝ)).indicator
        (fun r => 2*r*airyAiReal (r^2)*Real.exp (β*r^2-β^3/3)) r) = _
      rw [integral_indicator measurableSet_Ioi]
    _ = _ := by
      have h := integral_comp_rpow_Ioi_of_pos
        (g := fun x : ℝ => airyAiReal x * Real.exp (β*x-β^3/3))
        (by norm_num : (0 : ℝ) < 2)
      norm_num only at h
      simpa only [Real.rpow_one, Real.rpow_two, Real.rpow_natCast, smul_eq_mul, mul_assoc] using h
/-- The positive half alone already determines the prospective Laplace normalization. -/
theorem airyLaplacePositive_normalized_tendsto :
    Tendsto (fun β : ℝ => ∫ x in Set.Ioi (0 : ℝ), airyAiReal x * Real.exp (β*x-β^3/3))
      atTop (𝓝 1) := by
  obtain ⟨M, hM, hb⟩ := airyLaplaceProfile_bounded
  have hh := laplaceSaddle_integral_tendsto airyLaplaceProfile M
    (1 / (2 * Real.sqrt Real.pi)) hM.le airyLaplaceProfile_continuous hb
    airyLaplaceProfile_tendsto
  have hc : 2 * (1 / (2 * Real.sqrt Real.pi)) * Real.sqrt Real.pi = 1 := by
    field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']
  rw [hc] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop 0] with β hβ
  exact airyLaplaceSaddle_integral_eq β hβ
theorem airyLaplacePositive_integrable (β : ℝ /- [definition] -/) :
    IntegrableOn (fun x : ℝ => airyAiReal x * Real.exp (β*x)) (Set.Ioi 0) volume := by
  have hn := airyLaplacePositive_normalized_tendsto.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)
  obtain ⟨B, hBβ, hB⟩ := (hn.and (eventually_gt_atTop β)).exists
  have hi : IntegrableOn (fun x : ℝ => airyAiReal x * Real.exp (B*x-B^3/3)) (Set.Ioi 0) volume := by
    by_contra hh
    exact hBβ (integral_undef hh)
  have hi' : IntegrableOn (fun x : ℝ => airyAiReal x * Real.exp (B*x)) (Set.Ioi 0) volume := by
    have ht := hi.mul_const (Real.exp (B^3/3))
    change Integrable _ (volume.restrict (Set.Ioi 0))
    convert! ht using 1
    funext x
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  apply hi'.mono' ((continuous_airyAiReal.mul (by fun_prop)).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (airyAiReal_pos_of_nonneg (le_of_lt hx)).le (Real.exp_pos _).le)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hB.le hx.le))
    (airyAiReal_pos_of_nonneg hx.le).le

theorem airyLaplaceNegative_integrable (β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    IntegrableOn (fun x : ℝ => airyAiReal x * Real.exp (β*x)) (Set.Iic 0) volume := by
  obtain ⟨M, hM, hb⟩ := airyAiReal_globally_bounded
  apply ((integrableOn_exp_mul_Iic hβ 0).const_mul M).mono'
    ((continuous_airyAiReal.mul (by fun_prop)).aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem measurableSet_Iic fun x hx => ?_
  simp only [Pi.mul_apply]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (hb x) (Real.exp_pos _).le

theorem airyLaplace_integrable (β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    Integrable (fun x : ℝ => airyAiReal x * Real.exp (β*x)) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨airyLaplaceNegative_integrable β hβ, airyLaplacePositive_integrable β⟩

theorem laplaceMomentNegative_bound (β x : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) (hx : x ≤ 0 /- [standing] -/) :
    |x| * Real.exp (β*x) ≤ (2/β) * Real.exp ((β/2)*x) := by
  have hh := Real.add_one_le_exp (-(β/2)*x)
  have hxx : |x| ≤ (2/β) * Real.exp (-(β/2)*x) := by
    rw [abs_of_nonpos hx]
    apply (mul_le_mul_iff_of_pos_left hβ).mp
    have hb : β * (2/β) = 2 := by field_simp
    rw [← mul_assoc, hb]
    nlinarith
  calc |x| * Real.exp (β*x) ≤ (2/β) * Real.exp (-(β/2)*x) * Real.exp (β*x) :=
    mul_le_mul_of_nonneg_right hxx (Real.exp_pos _).le
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem airyLaplaceCoordinate_integrable (β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    Integrable (fun x : ℝ => x * airyAiReal x * Real.exp (β*x)) := by
  have hm : AEStronglyMeasurable (fun x : ℝ => x * airyAiReal x * Real.exp (β*x)) volume :=
    ((continuous_id.mul continuous_airyAiReal).mul (by fun_prop)).aestronglyMeasurable
  have hp : IntegrableOn (fun x : ℝ => x * airyAiReal x * Real.exp (β*x)) (Set.Ioi 0) volume := by
    apply (airyLaplacePositive_integrable (β+1)).mono' hm.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    have ha := (airyAiReal_pos_of_nonneg hx.le).le
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hx.le ha) (Real.exp_pos _).le)]
    have he : x * Real.exp (β*x) ≤ Real.exp ((β+1)*x) := by
      calc x * Real.exp (β*x) ≤ Real.exp x * Real.exp (β*x) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp x]) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    nlinarith [mul_le_mul_of_nonneg_left he ha]
  have hn : IntegrableOn (fun x : ℝ => x * airyAiReal x * Real.exp (β*x)) (Set.Iic 0) volume := by
    obtain ⟨M, hM, hb⟩ := airyAiReal_globally_bounded
    apply ((integrableOn_exp_mul_Iic (by positivity : 0 < β/2) 0).const_mul ((2/β)*M)).mono' hm.restrict ?_
    refine ae_restrict_of_forall_mem measurableSet_Iic fun x hx => ?_
    rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc
      |x| * |airyAiReal x| * Real.exp (β*x) ≤ |x| * M * Real.exp (β*x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg x)) (Real.exp_pos _).le
      _ = M * (|x| * Real.exp (β*x)) := by ring
      _ ≤ M * ((2/β) * Real.exp ((β/2)*x)) :=
        mul_le_mul_of_nonneg_left (laplaceMomentNegative_bound β x hβ hx) hM.le
      _ = _ := by ring
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨hn, hp⟩
theorem laplaceCubic_exp_tendsto_zero :
    Tendsto (fun β : ℝ => Real.exp (-β^3/3)) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop (by norm_num : (3 : ℕ) ≠ 0) :
    Tendsto (fun β : ℝ => β^3) atTop atTop)
  have hm := h.atTop_mul_const (by norm_num : (0 : ℝ) < 1/3)
  have hn := tendsto_neg_atTop_atBot.comp hm
  have ht : Tendsto (fun β : ℝ => -β^3/3) atTop atBot := by
    convert! hn using 1
    funext β
    dsimp
    ring
  exact Real.tendsto_exp_atBot.comp ht

theorem airyLaplaceNegative_normalized_tendsto :
    Tendsto (fun β : ℝ => ∫ x in Set.Iic (0 : ℝ), airyAiReal x * Real.exp (β*x-β^3/3))
      atTop (𝓝 0) := by
  obtain ⟨M, hM, hb⟩ := airyAiReal_globally_bounded
  have hh := tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => M * Real.exp x)
    (F := fun β x : ℝ => airyAiReal x * Real.exp (β*x-β^3/3))
    (μ := volume.restrict (Set.Iic (0 : ℝ))) (f := fun _ : ℝ => (0 : ℝ))
    (Eventually.of_forall (fun β =>
      (continuous_airyAiReal.mul (by fun_prop : Continuous (fun x : ℝ => Real.exp (β*x-β^3/3)))).aestronglyMeasurable))
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with β hβ
      refine ae_restrict_of_forall_mem measurableSet_Iic fun x hx => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul (hb x) ?_ (Real.exp_pos _).le hM.le
      apply Real.exp_le_exp.mpr
      have hp : 0 ≤ β^3 := by positivity
      nlinarith [mul_le_mul_of_nonpos_right hβ hx])
    (by simpa only [one_mul] using (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1) 0).const_mul M)
    (by
      refine ae_restrict_of_forall_mem measurableSet_Iic fun x hx => ?_
      have he : Tendsto (fun β : ℝ => Real.exp (β*x-β^3/3)) atTop (𝓝 0) := by
        apply squeeze_zero' (Eventually.of_forall (fun β => (Real.exp_pos _).le)) ?_
          laplaceCubic_exp_tendsto_zero
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with β hβ
        apply Real.exp_le_exp.mpr
        have hh : β*x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hβ hx
        linarith
      simpa only [mul_zero] using (tendsto_const_nhds (x := airyAiReal x)).mul he)
  simpa only [integral_zero] using hh

theorem airyLaplace_normalized_tendsto :
    Tendsto (fun β : ℝ => (∫ x : ℝ, airyAiReal x * Real.exp (β*x)) * Real.exp (-β^3/3))
      atTop (𝓝 1) := by
  have hh := airyLaplaceNegative_normalized_tendsto.add airyLaplacePositive_normalized_tendsto
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with β hβ
  have hi : Integrable (fun x : ℝ => airyAiReal x * Real.exp (β*x-β^3/3)) := by
    have h := (airyLaplace_integrable β hβ).mul_const (Real.exp (-β^3/3))
    convert! h using 1
    funext x
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
    hi.integrableOn hi.integrableOn, Set.Iic_union_Ioi, Measure.restrict_univ]
  rw [← integral_mul_const]
  congr 1
  funext x
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring


open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

noncomputable def laplaceCutoffBump : 𝓢(ℝ, ℂ) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  exact (b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp b.contDiff)
theorem laplaceCutoffBump_hasCompactSupport : HasCompactSupport (laplaceCutoffBump : ℝ → ℂ) := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  exact b.hasCompactSupport.comp_left (g := Complex.ofReal) (by simp)
theorem laplaceCutoffBump_zero : laplaceCutoffBump 0 = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  change (b 0 : ℂ) = 1
  rw [b.one_of_mem_closedBall (by simp [b])]
  norm_num
noncomputable def laplaceCutoffTest (κ : ℂ /- [definition] -/)
    (R : ℝ /- [definition] -/) (hR : R ≠ 0 /- [standing] -/) : 𝓢(ℝ, ℂ) := by
  have hc : HasCompactSupport (fun x : ℝ => laplaceCutoffBump (x / R)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using!
      laplaceCutoffBump_hasCompactSupport.comp_smul (c := R⁻¹) (inv_ne_zero hR)
  have hm : HasCompactSupport (fun x : ℝ => Complex.exp (κ * (x : ℂ)) * laplaceCutoffBump (x / R)) := by
    exact hc.mul_left
  exact hm.toSchwartzMap (by
    have hcast : ContDiff ℝ ∞ (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
    have hb : ContDiff ℝ ∞ (laplaceCutoffBump : ℝ → ℂ) := laplaceCutoffBump.smooth ⊤
    fun_prop)
theorem laplaceCutoffTest_apply (κ : ℂ /- [definition] -/)
    (R : ℝ /- [definition] -/) (hR : R ≠ 0 /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    laplaceCutoffTest κ R hR x = Complex.exp (κ * (x : ℂ)) * laplaceCutoffBump (x / R) := rfl
theorem laplaceCutoffTest_zero (κ : ℂ /- [definition] -/)
    (R : ℝ /- [definition] -/) (hR : R ≠ 0 /- [standing] -/) :
    laplaceCutoffTest κ R hR 0 = 1 := by simp [laplaceCutoffTest_apply, laplaceCutoffBump_zero]
noncomputable def laplaceCutoffDerivative (κ : ℂ /- [definition] -/)
    (R x : ℝ /- [definition] -/) : ℂ :=
  Complex.exp (κ * (x : ℂ)) *
    (κ * laplaceCutoffBump (x/R) + (R : ℂ)⁻¹ * (SchwartzMap.derivCLM ℂ ℂ laplaceCutoffBump) (x/R))
theorem laplaceCutoffTest_hasDerivAt (κ : ℂ /- [definition] -/)
    (R : ℝ /- [definition] -/) (hR : R ≠ 0 /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    HasDerivAt (laplaceCutoffTest κ R hR) (laplaceCutoffDerivative κ R x) x := by
  have he := (((hasDerivAt_id x).ofReal_comp).const_mul κ).cexp
  have hb := (laplaceCutoffBump.hasDerivAt (x/R)).scomp x ((hasDerivAt_id x).div_const R)
  have h := he.fun_mul hb
  convert! h using 1
  simp only [laplaceCutoffDerivative, id_eq, Complex.real_smul, Complex.ofReal_div,
    Complex.ofReal_one, one_div, Complex.ofReal_inv, Function.comp_apply,
    SchwartzMap.derivCLM_apply]
  ring
theorem laplaceCutoffDerivative_hasDerivAt (κ : ℂ /- [definition] -/)
    (R x : ℝ /- [definition] -/) :
    HasDerivAt (laplaceCutoffDerivative κ R)
      (Complex.exp (κ * (x : ℂ)) *
        (κ^2 * laplaceCutoffBump (x/R) +
          2 * κ * (R : ℂ)⁻¹ * (SchwartzMap.derivCLM ℂ ℂ laplaceCutoffBump) (x/R) +
          ((R : ℂ)⁻¹)^2 * (SchwartzMap.derivCLM ℂ ℂ
            (SchwartzMap.derivCLM ℂ ℂ laplaceCutoffBump)) (x/R))) x := by
  have he := (((hasDerivAt_id x).ofReal_comp).const_mul κ).cexp
  have hb := (laplaceCutoffBump.hasDerivAt (x/R)).scomp x ((hasDerivAt_id x).div_const R)
  have hb' := ((SchwartzMap.derivCLM ℂ ℂ laplaceCutoffBump).hasDerivAt (x/R)).scomp x
    ((hasDerivAt_id x).div_const R)
  have h := he.fun_mul ((hb.const_mul κ).add (hb'.const_mul (R : ℂ)⁻¹))
  convert! h using 1
  simp only [laplaceCutoffDerivative, id_eq, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, one_div, Complex.ofReal_inv,
    Function.comp_apply, Pi.add_apply, SchwartzMap.derivCLM_apply]
  ring
theorem laplaceCutoffTest_second_deriv (κ : ℂ /- [definition] -/)
    (R : ℝ /- [definition] -/) (hR : R ≠ 0 /- [standing] -/)
    (x : ℝ /- [definition] -/) :
    deriv (deriv (laplaceCutoffTest κ R hR)) x =
      Complex.exp (κ * (x : ℂ)) *
        (κ^2 * laplaceCutoffBump (x/R) +
          2 * κ * (R : ℂ)⁻¹ * (SchwartzMap.derivCLM ℂ ℂ laplaceCutoffBump) (x/R) +
          ((R : ℂ)⁻¹)^2 * (SchwartzMap.derivCLM ℂ ℂ
            (SchwartzMap.derivCLM ℂ ℂ laplaceCutoffBump)) (x/R)) := by
  have h : deriv (laplaceCutoffTest κ R hR) = laplaceCutoffDerivative κ R :=
    funext (fun t => (laplaceCutoffTest_hasDerivAt κ R hR t).deriv)
  rw [h]
  exact (laplaceCutoffDerivative_hasDerivAt κ R x).deriv
/-- Nondegenerate inhabitation: every allowed test has value one at zero. -/
theorem laplaceCutoffTest_joint_probe :
    (1 : ℝ) ≠ 0 ∧ laplaceCutoffBump 0 = 1 ∧
    laplaceCutoffTest (1 : ℂ) 1 (by norm_num) 0 = 1 ∧
    laplaceCutoffTest (1 : ℂ) 1 (by norm_num) ≠ 0 := by
  refine ⟨by norm_num, laplaceCutoffBump_zero, laplaceCutoffTest_zero 1 1 (by norm_num), ?_⟩
  intro h
  have hh := congrArg (fun f : 𝓢(ℝ, ℂ) => f 0) h
  simpa [laplaceCutoffTest_zero] using hh


open Filter

theorem schwartz_scaled_integrable (g : ℝ → ℂ /- [definition] -/)
    (hg : Integrable g /- [standing] -/) (ψ : 𝓢(ℝ, ℂ) /- [definition] -/ )
    (R : ℝ /- [definition] -/) :
    Integrable (fun x : ℝ => g x * ψ (x/R)) := by
  apply hg.mul_bdd ((ψ.continuous.comp (by fun_prop)).aestronglyMeasurable)
  exact ae_of_all _ (fun x => ψ.norm_le_seminorm ℂ (x/R))

theorem schwartz_scaled_integral_tendsto (g : ℝ → ℂ /- [definition] -/)
    (hg : Integrable g /- [standing] -/) (ψ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    Tendsto (fun R : ℝ => ∫ x : ℝ, g x * ψ (x/R)) atTop (𝓝 ((∫ x : ℝ, g x) * ψ 0)) := by
  have hh := tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => ‖g x‖ * SchwartzMap.seminorm ℂ 0 0 ψ)
    (f := fun x : ℝ => g x * ψ 0)
    (Eventually.of_forall (fun R => (schwartz_scaled_integrable g hg ψ R).aestronglyMeasurable))
    (Eventually.of_forall (fun R => ae_of_all _ (fun x => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (ψ.norm_le_seminorm ℂ (x/R)) (norm_nonneg _))))
    (hg.norm.mul_const _)
    (ae_of_all _ (fun x => by
      have hi : Tendsto (fun R : ℝ => x/R) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using (tendsto_const_nhds (x := x)).mul tendsto_inv_atTop_zero
      exact (tendsto_const_nhds (x := g x)).mul (ψ.continuous.continuousAt.tendsto.comp hi)))
  simpa only [integral_mul_const] using hh

theorem weakAiry_laplace_identity (f : ℝ → ℂ /- [definition] -/)
    (κ : ℂ /- [definition] -/)
    (hf : Integrable (fun x : ℝ => Complex.exp (κ * (x : ℂ)) * f x) /- [standing] -/ )
    (hxf : Integrable (fun x : ℝ => (x : ℂ) * (Complex.exp (κ * (x : ℂ)) * f x)) /- [standing] -/ )
    (hode : ∀ φ : 𝓢(ℝ, ℂ), (∫ x : ℝ, deriv (deriv φ) x * f x) =
      ∫ x : ℝ, φ x * ((x : ℂ) * f x) /- [standing] -/ ) :
    (∫ x : ℝ, (x : ℂ) * (Complex.exp (κ * (x : ℂ)) * f x)) =
      κ^2 * ∫ x : ℝ, Complex.exp (κ * (x : ℂ)) * f x := by
  let g : ℝ → ℂ := fun x => Complex.exp (κ * (x : ℂ)) * f x
  let ψ := laplaceCutoffBump
  let ψ' := SchwartzMap.derivCLM ℂ ℂ ψ
  let ψ'' := SchwartzMap.derivCLM ℂ ℂ ψ'
  have hi (R : ℝ) (hR : R ≠ 0) :
      (∫ x : ℝ, g x * ψ (x/R)) * κ^2 +
      (∫ x : ℝ, g x * ψ' (x/R)) * (2*κ*(R : ℂ)⁻¹) +
      (∫ x : ℝ, g x * ψ'' (x/R)) * ((R : ℂ)⁻¹)^2 =
      ∫ x : ℝ, ((x : ℂ)*g x) * ψ (x/R) := by
    have hh := hode (laplaceCutoffTest κ R hR)
    simp only [laplaceCutoffTest_apply, laplaceCutoffTest_second_deriv] at hh
    have he : (fun x : ℝ => Complex.exp (κ*(x:ℂ)) *
        (κ^2 * ψ (x/R) + 2*κ*(R:ℂ)⁻¹ * ψ' (x/R) + ((R:ℂ)⁻¹)^2 * ψ'' (x/R)) * f x) =
        fun x : ℝ => (g x * ψ (x/R))*κ^2 +
          (g x * ψ' (x/R))*(2*κ*(R:ℂ)⁻¹) +
          (g x * ψ'' (x/R))*((R:ℂ)⁻¹)^2 := by
      funext x
      dsimp [g]
      ring
    have hr : (fun x : ℝ => Complex.exp (κ*(x:ℂ)) * ψ (x/R) * ((x:ℂ)*f x)) =
        fun x : ℝ => ((x:ℂ)*g x) * ψ (x/R) := by
      funext x
      dsimp [g]
      ring
    change (∫ x : ℝ, Complex.exp (κ*(x:ℂ)) *
      (κ^2 * ψ (x/R) + 2*κ*(R:ℂ)⁻¹ * ψ' (x/R) + ((R:ℂ)⁻¹)^2 * ψ'' (x/R)) * f x) = _ at hh
    rw [he, hr] at hh
    have hA := (schwartz_scaled_integrable g hf ψ R).mul_const (κ^2)
    have hB := (schwartz_scaled_integrable g hf ψ' R).mul_const (2*κ*(R:ℂ)⁻¹)
    have hC := (schwartz_scaled_integrable g hf ψ'' R).mul_const (((R:ℂ)⁻¹)^2)
    have hsum : (∫ x : ℝ, (g x*ψ (x/R))*κ^2 +
        (g x*ψ' (x/R))*(2*κ*(R:ℂ)⁻¹) + (g x*ψ'' (x/R))*((R:ℂ)⁻¹)^2) =
        (∫ x : ℝ, (g x*ψ (x/R))*κ^2) +
        (∫ x : ℝ, (g x*ψ' (x/R))*(2*κ*(R:ℂ)⁻¹)) +
        (∫ x : ℝ, (g x*ψ'' (x/R))*((R:ℂ)⁻¹)^2) := by
      have ht := integral_add (hA.add hB) hC
      simp only [Pi.add_apply] at ht
      rw [integral_add hA hB] at ht
      exact ht
    rw [hsum, integral_mul_const, integral_mul_const, integral_mul_const] at hh
    exact hh
  have hb := schwartz_scaled_integral_tendsto g hf ψ
  have hb' := schwartz_scaled_integral_tendsto g hf ψ'
  have hb'' := schwartz_scaled_integral_tendsto g hf ψ''
  have hx := schwartz_scaled_integral_tendsto (fun x => (x:ℂ)*g x) hxf ψ
  have hz : Tendsto (fun R : ℝ => (R : ℂ)⁻¹) atTop (𝓝 0) := by
    have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))
    change Tendsto (fun R : ℝ => Complex.ofReal (R⁻¹)) atTop (𝓝 (Complex.ofReal 0)) at ht
    simpa only [Complex.ofReal_zero, Complex.ofReal_inv] using ht
  have hl := ((hb.mul_const (κ^2)).add (hb'.mul ((tendsto_const_nhds (x := 2*κ)).mul hz))).add
    (hb''.mul (hz.pow 2))
  simp only [ψ, laplaceCutoffBump_zero, mul_one, mul_zero, zero_pow (by norm_num : 2 ≠ 0), add_zero] at hl hx
  have hh : Tendsto (fun R : ℝ => ∫ x : ℝ, ((x : ℂ)*g x) * ψ (x/R)) atTop
      (𝓝 ((∫ x : ℝ, g x)*κ^2)) := hl.congr' (by
        filter_upwards [eventually_ne_atTop (0 : ℝ)] with R hR
        exact hi R hR)
  simpa [g, mul_comm] using tendsto_nhds_unique hx hh

open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

noncomputable def realLaplaceIntegral (f : ℝ → ℝ /- [definition] -/)
    (β : ℝ /- [definition] -/) : ℝ := ∫ x : ℝ, f x * Real.exp (β*x)
theorem realLaplaceIntegral_hasDerivAt (f : ℝ → ℝ /- [definition] -/)
    (hf : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => f x * Real.exp (β*x)) /- [standing] -/ )
    (hxf : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => x * f x * Real.exp (β*x)) /- [standing] -/ )
    (β : ℝ /- [definition] -/) (hβ : 0 < β /- [standing] -/) :
    HasDerivAt (realLaplaceIntegral f) (∫ x : ℝ, x*f x*Real.exp (β*x)) β := by
  have hlo : 0 < β/2 := by positivity
  have hhi : 0 < 2*β := by positivity
  have hs : Set.Ioo (β/2) (2*β) ∈ 𝓝 β := Ioo_mem_nhds (by linarith) (by linarith)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun y x : ℝ => f x * Real.exp (y*x))
    (F' := fun y x : ℝ => x*f x*Real.exp (y*x))
    (bound := fun x : ℝ => ‖x*f x*Real.exp ((β/2)*x)‖ + ‖x*f x*Real.exp ((2*β)*x)‖)
    hs
    (by
      filter_upwards [hs] with y hy
      exact (hf y (by linarith [hy.1])).aestronglyMeasurable)
    (hf β hβ) (hxf β hβ).aestronglyMeasurable
    (ae_of_all _ (fun x y hy => by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      by_cases hx : 0 ≤ x
      · have he : Real.exp (y*x) ≤ Real.exp ((2*β)*x) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hy.2.le hx)
        have ht := mul_le_mul_of_nonneg_left he (mul_nonneg (abs_nonneg x) (abs_nonneg (f x)))
        linarith [mul_nonneg (mul_nonneg (abs_nonneg x) (abs_nonneg (f x)))
          (Real.exp_pos ((β/2)*x)).le]
      · have he : Real.exp (y*x) ≤ Real.exp ((β/2)*x) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right hy.1.le (le_of_not_ge hx))
        have ht := mul_le_mul_of_nonneg_left he (mul_nonneg (abs_nonneg x) (abs_nonneg (f x)))
        linarith [mul_nonneg (mul_nonneg (abs_nonneg x) (abs_nonneg (f x)))
          (Real.exp_pos ((2*β)*x)).le]))
    ((hxf (β/2) hlo).norm.add (hxf (2*β) hhi).norm)
    (ae_of_all _ (fun x y hy => by
      have h := (((hasDerivAt_id y).mul_const x).exp).const_mul (f x)
      convert! h using 1 <;> first | rfl | (simp only [id_eq, one_mul]; ring)))
  exact hd.2

theorem realLaplaceIntegral_eq_exp_cubic (f : ℝ → ℝ /- [definition] -/)
    (hf : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => f x * Real.exp (β*x)) /- [standing] -/ )
    (hxf : ∀ β : ℝ, 0 < β → Integrable (fun x : ℝ => x*f x*Real.exp (β*x)) /- [standing] -/ )
    (hm : ∀ β : ℝ, 0 < β → (∫ x : ℝ, x*f x*Real.exp (β*x)) = β^2*realLaplaceIntegral f β /- [standing] -/)
    (hl : Tendsto (fun β : ℝ => realLaplaceIntegral f β * Real.exp (-β^3/3)) atTop (𝓝 1) /- [standing] -/ )
    (β : ℝ /- [definition] -/) (hβ : 0 < β /- [standing] -/) :
    realLaplaceIntegral f β = Real.exp (β^3/3) := by
  let g : ℝ → ℝ := fun t => realLaplaceIntegral f (Real.exp t) * Real.exp (-(Real.exp t)^3/3)
  have hg (t : ℝ) : HasDerivAt g 0 t := by
    have hL := realLaplaceIntegral_hasDerivAt f hf hxf (Real.exp t) (Real.exp_pos t)
    rw [hm (Real.exp t) (Real.exp_pos t)] at hL
    have hL' := hL.comp t (Real.hasDerivAt_exp t)
    have he := (((((Real.hasDerivAt_exp t).pow 3).neg).div_const 3).exp)
    have h := hL'.fun_mul he
    convert! h using 1 <;> first | rfl | (simp only [pow_succ, Function.comp_apply, Pi.pow_apply, Pi.neg_apply]; ring)
  have hc (t : ℝ) : g t = g 0 :=
    is_const_of_deriv_eq_zero (fun u => (hg u).differentiableAt)
      (fun u => (hg u).deriv) t 0
  have ht : Tendsto g atTop (𝓝 1) := hl.comp Real.tendsto_exp_atTop
  have hz : g 0 = 1 := tendsto_nhds_unique
    (tendsto_const_nhds.congr' (Eventually.of_forall (fun t => (hc t).symm))) ht
  have hb : realLaplaceIntegral f β * Real.exp (-β^3/3) = 1 := by
    simpa only [g, Real.exp_log hβ] using (hc (Real.log β)).trans hz
  have he : Real.exp (-β^3/3) * Real.exp (β^3/3) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 1 <;> ring
  have hh := congrArg (fun r : ℝ => r*Real.exp (β^3/3)) hb
  simpa only [mul_assoc, he, mul_one, one_mul] using hh
open MeasureTheory Filter
open scoped Topology SchwartzMap TemperedDistribution ContDiff

noncomputable def airyLaplaceFrequency (β ξ : ℝ /- [definition] -/) : ℂ :=
  (β : ℂ) - (2*Real.pi : ℝ)*Complex.I*(ξ : ℂ)
noncomputable def complexLaplaceIntegral (f : ℝ → ℂ /- [definition] -/)
    (κ : ℂ /- [definition] -/) : ℂ := ∫ x : ℝ, Complex.exp (κ*(x:ℂ))*f x

theorem airyLaplaceFrequency_re (β ξ : ℝ /- [definition] -/) :
    (airyLaplaceFrequency β ξ).re = β := by simp [airyLaplaceFrequency, Complex.mul_re, Complex.mul_im]

theorem complexLaplaceIntegral_vertical_hasDerivAt (f : ℝ → ℂ /- [definition] -/)
    (β ξ : ℝ /- [definition] -/) (hβ : 0 < β /- [standing] -/)
    (hf : ∀ κ : ℂ, 0 < κ.re → Integrable (fun x : ℝ => Complex.exp (κ*(x:ℂ))*f x) /- [standing] -/ )
    (hxf : ∀ κ : ℂ, 0 < κ.re → Integrable (fun x : ℝ => (x:ℂ)*(Complex.exp (κ*(x:ℂ))*f x)) /- [standing] -/ ) :
    HasDerivAt (fun η : ℝ => complexLaplaceIntegral f (airyLaplaceFrequency β η))
      ((-(2*Real.pi : ℝ)*Complex.I)*
        (∫ x : ℝ, (x:ℂ)*(Complex.exp (airyLaplaceFrequency β ξ*(x:ℂ))*f x))) ξ := by
  let q : ℂ := -(2*Real.pi : ℝ)*Complex.I
  have hpos (η : ℝ) : 0 < (airyLaplaceFrequency β η).re := by rwa [airyLaplaceFrequency_re]
  have hkp : 0 < (β : ℂ).re := by simpa using hβ
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun η x : ℝ => Complex.exp (airyLaplaceFrequency β η*(x:ℂ))*f x)
    (F' := fun η x : ℝ => q*((x:ℂ)*(Complex.exp (airyLaplaceFrequency β η*(x:ℂ))*f x)))
    (s := Set.univ) (x₀ := ξ) (by simp)
    (Eventually.of_forall (fun η => (hf _ (hpos η)).aestronglyMeasurable))
    (hf _ (hpos ξ)) ((hxf _ (hpos ξ)).const_mul q).aestronglyMeasurable
    (bound := fun x : ℝ => ‖q‖*‖(x:ℂ)*(Complex.exp ((β:ℂ)*(x:ℂ))*f x)‖)
    (ae_of_all _ (fun x η _ => by
      simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero, airyLaplaceFrequency_re]
      rfl))
    ((hxf _ hkp).norm.const_mul ‖q‖)
    (ae_of_all _ (fun x η _ => by
      have hk : HasDerivAt (fun η : ℝ => airyLaplaceFrequency β η) q η := by
        have h := (((hasDerivAt_id η).ofReal_comp).const_mul ((2*Real.pi : ℝ)*Complex.I)).const_sub (β : ℂ)
        convert! h using 1 <;> first | rfl | (simp only [q, Complex.ofReal_one, mul_one]; ring)
      have h := (hk.mul_const (x : ℂ)).cexp |>.mul_const (f x)
      convert! h using 1 <;> first | rfl | (dsimp [q]; ring)))
  have hh := hd.2
  rw [integral_const_mul] at hh
  exact hh

theorem complexLaplaceIntegral_vertical_eq_exp_cubic (f : ℝ → ℂ /- [definition] -/)
    (β ξ : ℝ /- [definition] -/) (hβ : 0 < β /- [standing] -/)
    (hf : ∀ κ : ℂ, 0 < κ.re → Integrable (fun x : ℝ => Complex.exp (κ*(x:ℂ))*f x) /- [standing] -/ )
    (hxf : ∀ κ : ℂ, 0 < κ.re → Integrable (fun x : ℝ => (x:ℂ)*(Complex.exp (κ*(x:ℂ))*f x)) /- [standing] -/ )
    (hm : ∀ κ : ℂ, 0 < κ.re →
      (∫ x : ℝ, (x:ℂ)*(Complex.exp (κ*(x:ℂ))*f x)) = κ^2*complexLaplaceIntegral f κ /- [standing] -/)
    (hr : complexLaplaceIntegral f (β : ℂ) = Complex.exp ((β : ℂ)^3/3) /- [standing] -/ ) :
    complexLaplaceIntegral f (airyLaplaceFrequency β ξ) =
      Complex.exp ((airyLaplaceFrequency β ξ)^3/3) := by
  let q : ℂ := -(2*Real.pi : ℝ)*Complex.I
  let g : ℝ → ℂ := fun η => complexLaplaceIntegral f (airyLaplaceFrequency β η) *
    Complex.exp (-(airyLaplaceFrequency β η)^3/3)
  have hg (η : ℝ) : HasDerivAt g 0 η := by
    have hk : HasDerivAt (fun η : ℝ => airyLaplaceFrequency β η) q η := by
      have h := (((hasDerivAt_id η).ofReal_comp).const_mul ((2*Real.pi : ℝ)*Complex.I)).const_sub (β : ℂ)
      convert! h using 1 <;> first | rfl | (simp only [q, Complex.ofReal_one, mul_one]; ring)
    have hL := complexLaplaceIntegral_vertical_hasDerivAt f β η hβ hf hxf
    rw [hm _ (by rwa [airyLaplaceFrequency_re])] at hL
    have he := (((hk.pow 3).neg).div_const 3).cexp
    have h := hL.fun_mul he
    convert! h using 1 <;> first | rfl | (dsimp [q]; simp only [pow_succ]; ring)
  have hc : g ξ = g 0 := is_const_of_deriv_eq_zero
    (fun η => (hg η).differentiableAt) (fun η => (hg η).deriv) ξ 0
  have hzero : airyLaplaceFrequency β 0 = (β : ℂ) := by simp [airyLaplaceFrequency]
  have hb : complexLaplaceIntegral f (airyLaplaceFrequency β ξ) *
      Complex.exp (-(airyLaplaceFrequency β ξ)^3/3) = 1 := by
    dsimp [g] at hc
    rw [hzero, hr, ← Complex.exp_add] at hc
    simpa only [add_neg_cancel, neg_div, Complex.exp_zero] using hc
  have he : Complex.exp (-(airyLaplaceFrequency β ξ)^3/3) *
      Complex.exp ((airyLaplaceFrequency β ξ)^3/3) = 1 := by
    rw [← Complex.exp_add]; convert Complex.exp_zero using 1 <;> ring
  have hh := congrArg (fun r : ℂ => r*Complex.exp ((airyLaplaceFrequency β ξ)^3/3)) hb
  simpa only [mul_assoc, he, mul_one, one_mul] using hh
theorem airyLaplaceComplex_integrable (κ : ℂ /- [definition] -/)
    (hκ : 0 < κ.re /- [standing] -/) :
    Integrable (fun x : ℝ => Complex.exp (κ*(x:ℂ))*airyAiComplexReal x) := by
  apply (airyLaplace_integrable κ.re hκ).norm.mono' ?_ ?_
  · exact ((by fun_prop : Continuous (fun x : ℝ => Complex.exp (κ*(x:ℂ)))).mul
      (Complex.continuous_ofReal.comp continuous_airyAiReal)).aestronglyMeasurable
  · exact ae_of_all _ (fun x => by
      simp only [airyAiComplexReal, norm_mul, Complex.norm_exp, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [mul_comm])

theorem airyLaplaceComplexCoordinate_integrable (κ : ℂ /- [definition] -/)
    (hκ : 0 < κ.re /- [standing] -/) :
    Integrable (fun x : ℝ => (x:ℂ)*(Complex.exp (κ*(x:ℂ))*airyAiComplexReal x)) := by
  apply (airyLaplaceCoordinate_integrable κ.re hκ).norm.mono' ?_ ?_
  · have hcast := Complex.continuous_ofReal
    exact (hcast.mul (((by fun_prop : Continuous (fun x : ℝ => Complex.exp (κ*(x:ℂ)))).mul
      (Complex.continuous_ofReal.comp continuous_airyAiReal)))).aestronglyMeasurable
  · exact ae_of_all _ (fun x => by
      simp only [airyAiComplexReal, norm_mul, Complex.norm_exp, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      ring_nf
      exact le_rfl)

theorem airyLaplaceComplex_coordinate_identity (κ : ℂ /- [definition] -/)
    (hκ : 0 < κ.re /- [standing] -/) :
    (∫ x : ℝ, (x:ℂ)*(Complex.exp (κ*(x:ℂ))*airyAiComplexReal x)) =
      κ^2*complexLaplaceIntegral airyAiComplexReal κ := by
  exact weakAiry_laplace_identity airyAiComplexReal κ
    (airyLaplaceComplex_integrable κ hκ) (airyLaplaceComplexCoordinate_integrable κ hκ)
    (fun φ => by
      simpa only [airyAiComplexReal, Complex.ofReal_mul] using airyAi_schwartz_weak_ode φ)

theorem airyLaplaceReal_coordinate_identity (β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    (∫ x : ℝ, x*airyAiReal x*Real.exp (β*x)) = β^2*realLaplaceIntegral airyAiReal β := by
  have hh := airyLaplaceComplex_coordinate_identity (β : ℂ) (by simpa using hβ)
  simp only [complexLaplaceIntegral, airyAiComplexReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, ← Complex.ofReal_pow, integral_complex_ofReal] at hh
  have hr := congrArg Complex.re hh
  simpa [realLaplaceIntegral, pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_comm, mul_left_comm, mul_assoc] using hr

theorem airyLaplaceReal_eq_exp_cubic (β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    realLaplaceIntegral airyAiReal β = Real.exp (β^3/3) := by
  exact realLaplaceIntegral_eq_exp_cubic airyAiReal airyLaplace_integrable
    airyLaplaceCoordinate_integrable airyLaplaceReal_coordinate_identity
    airyLaplace_normalized_tendsto β hβ

theorem airyLaplaceComplex_real_eq_exp_cubic (β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    complexLaplaceIntegral airyAiComplexReal (β : ℂ) = Complex.exp ((β : ℂ)^3/3) := by
  simp only [complexLaplaceIntegral, airyAiComplexReal, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, integral_complex_ofReal]
  rw [show (∫ x : ℝ, Real.exp (β*x)*airyAiReal x) = realLaplaceIntegral airyAiReal β by
    simp only [realLaplaceIntegral, mul_comm]]
  rw [airyLaplaceReal_eq_exp_cubic β hβ]
  simp only [Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_ofNat]

theorem airyLaplaceComplex_vertical_eq_exp_cubic (β ξ : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    complexLaplaceIntegral airyAiComplexReal (airyLaplaceFrequency β ξ) =
      Complex.exp ((airyLaplaceFrequency β ξ)^3/3) := by
  exact complexLaplaceIntegral_vertical_eq_exp_cubic airyAiComplexReal β ξ hβ
    airyLaplaceComplex_integrable airyLaplaceComplexCoordinate_integrable
    airyLaplaceComplex_coordinate_identity (airyLaplaceComplex_real_eq_exp_cubic β hβ)

/-- All analytic readiness fields hold jointly on the same nonzero genuine Ai. -/
theorem airyAi_laplace_all_binder_probe :
    ∃ M : ℝ, 0 < M ∧ (∀ x : ℝ, ‖airyAiComplexReal x‖ ≤ M) ∧
    AEStronglyMeasurable airyAiComplexReal volume ∧
    (∀ β : ℝ, 0 < β →
      Integrable (fun x : ℝ => airyAiReal x * Real.exp (β*x)) ∧
      Integrable (fun x : ℝ => x*airyAiReal x*Real.exp (β*x)) ∧
      (∫ x : ℝ, x*airyAiReal x*Real.exp (β*x)) = β^2*realLaplaceIntegral airyAiReal β) ∧
    (∀ κ : ℂ, 0 < κ.re →
      Integrable (fun x : ℝ => Complex.exp (κ*(x:ℂ))*airyAiComplexReal x) ∧
      Integrable (fun x : ℝ => (x:ℂ)*(Complex.exp (κ*(x:ℂ))*airyAiComplexReal x)) ∧
      (∫ x : ℝ, (x:ℂ)*(Complex.exp (κ*(x:ℂ))*airyAiComplexReal x)) =
        κ^2*complexLaplaceIntegral airyAiComplexReal κ) ∧
    Tendsto (fun β : ℝ => realLaplaceIntegral airyAiReal β * Real.exp (-β^3/3)) atTop (𝓝 1) ∧
    (∀ β : ℝ, 0 < β → complexLaplaceIntegral airyAiComplexReal (β : ℂ) = Complex.exp ((β : ℂ)^3/3)) ∧
    laplaceCutoffTest (1 : ℂ) 1 (by norm_num) ≠ 0 ∧ airyAiReal 0 > 0 := by
  obtain ⟨M, hM, hb⟩ := airyAiReal_globally_bounded
  refine ⟨M, hM, ?_, ?_, ?_, ?_, airyLaplace_normalized_tendsto,
    airyLaplaceComplex_real_eq_exp_cubic, laplaceCutoffTest_joint_probe.2.2.2,
    airyAiReal_zero_pos⟩
  · intro x
    simpa only [airyAiComplexReal, Complex.norm_real, Real.norm_eq_abs] using hb x
  · exact (Complex.continuous_ofReal.comp continuous_airyAiReal).aestronglyMeasurable
  · intro β hβ
    exact ⟨airyLaplace_integrable β hβ, airyLaplaceCoordinate_integrable β hβ,
      airyLaplaceReal_coordinate_identity β hβ⟩
  · intro κ hκ
    exact ⟨airyLaplaceComplex_integrable κ hκ, airyLaplaceComplexCoordinate_integrable κ hκ,
      airyLaplaceComplex_coordinate_identity κ hκ⟩


open FourierTransform
open scoped SchwartzMap

noncomputable def laplaceDampingSequence (n : ℕ /- [definition] -/) : ℝ := ((n : ℝ)+1)⁻¹
theorem laplaceDampingSequence_pos (n : ℕ /- [definition] -/) : 0 < laplaceDampingSequence n := by
  unfold laplaceDampingSequence
  positivity
theorem laplaceDampingSequence_le_one (n : ℕ /- [definition] -/) : laplaceDampingSequence n ≤ 1 := by
  unfold laplaceDampingSequence
  rw [inv_le_one₀ (by positivity : 0 < (n : ℝ)+1)]
  linarith [Nat.cast_nonneg (α := ℝ) n]
theorem laplaceDampingSequence_tendsto : Tendsto laplaceDampingSequence atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp (((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).atTop_add (tendsto_const_nhds (x := (1 : ℝ)))))

noncomputable def laplaceDamped (f : ℝ → ℂ /- [definition] -/)
    (β x : ℝ /- [definition] -/) : ℂ := Complex.exp ((β : ℂ)*(x:ℂ))*f x

theorem fourier_laplaceDamped_eq (f : ℝ → ℂ /- [definition] -/)
    (β ξ : ℝ /- [definition] -/) :
    𝓕 (laplaceDamped f β) ξ = complexLaplaceIntegral f (airyLaplaceFrequency β ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold complexLaplaceIntegral
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, laplaceDamped, ← mul_assoc, ← Complex.exp_add,
    airyLaplaceFrequency, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
  congr 2
  ring

theorem fourier_integral_pairing (f : ℝ → ℂ /- [definition] -/)
    (hf : Integrable f /- [standing] -/) (φ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    (∫ ξ : ℝ, (𝓕 f) ξ * φ ξ) = ∫ x : ℝ, f x * (𝓕 φ) x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := innerₗ ℝ)
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (f := f) (g := (φ : ℝ → ℂ))
    Real.continuous_fourierChar (by simpa only [innerₗ_apply_apply] using continuous_inner)
    hf φ.integrable
  rw [flip_innerₗ] at h
  simp only [smul_eq_mul] at h
  exact h

theorem airyLaplaceFrequency_cubic_re (β ξ : ℝ /- [definition] -/) :
    (((airyLaplaceFrequency β ξ)^3/3).re) = β^3/3 - β*(2*Real.pi*ξ)^2 := by
  simp only [airyLaplaceFrequency, pow_succ, pow_zero, mul_one,
    Complex.div_ofNat_re, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
  ring

theorem laplaceCubicPhase_bound (β ξ : ℝ /- [definition] -/)
    (hβ : 0 ≤ β /- [standing] -/) (hβ1 : β ≤ 1 /- [standing] -/) :
    ‖Complex.exp ((airyLaplaceFrequency β ξ)^3/3)‖ ≤ Real.exp 1 := by
  rw [Complex.norm_exp, airyLaplaceFrequency_cubic_re]
  apply Real.exp_le_exp.mpr
  have hp : β^3 ≤ 1 := by simpa using pow_le_pow_left₀ hβ hβ1 3
  have hnn : 0 ≤ β*(2*Real.pi*ξ)^2 := mul_nonneg hβ (sq_nonneg _)
  norm_num at hp
  linarith

theorem laplaceCubicPhase_tendsto (ξ : ℝ /- [definition] -/) :
    Tendsto (fun n : ℕ => Complex.exp ((airyLaplaceFrequency (laplaceDampingSequence n) ξ)^3/3))
      atTop (𝓝 (Complex.exp (Complex.I*(2*Real.pi*(ξ:ℂ))^3/3))) := by
  have hb := Complex.continuous_ofReal.continuousAt.tendsto.comp laplaceDampingSequence_tendsto
  change Tendsto (fun n : ℕ => (laplaceDampingSequence n : ℂ)) atTop (𝓝 (0 : ℂ)) at hb
  have hk := hb.sub_const ((2*Real.pi : ℝ)*Complex.I*(ξ:ℂ))
  have he := (Complex.continuous_exp.continuousAt.tendsto.comp ((hk.pow 3).div_const 3))
  have hv : (0 - (2*Real.pi : ℝ)*Complex.I*(ξ:ℂ))^3/3 = Complex.I*(2*Real.pi*(ξ:ℂ))^3/3 := by
    simp only [Complex.ofReal_mul, Complex.ofReal_ofNat]
    ring_nf
    simp [Complex.I_sq]
    ring
  rw [hv] at he
  exact he

theorem laplaceCubicPhase_schwartz_integral_tendsto (φ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    Tendsto (fun n : ℕ => ∫ ξ : ℝ,
      Complex.exp ((airyLaplaceFrequency (laplaceDampingSequence n) ξ)^3/3)*φ ξ)
      atTop (𝓝 (∫ ξ : ℝ, Complex.exp (Complex.I*(2*Real.pi*(ξ:ℂ))^3/3)*φ ξ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun ξ : ℝ => Real.exp 1 * ‖φ ξ‖)
  · exact Eventually.of_forall (fun n => by
      have hc : Continuous (fun ξ : ℝ => Complex.exp ((airyLaplaceFrequency (laplaceDampingSequence n) ξ)^3/3)) := by
        unfold airyLaplaceFrequency
        have hcast := Complex.continuous_ofReal
        fun_prop
      exact (hc.mul φ.continuous).aestronglyMeasurable)
  · exact Eventually.of_forall (fun n => ae_of_all _ (fun ξ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (laplaceCubicPhase_bound _ ξ
        (laplaceDampingSequence_pos n).le (laplaceDampingSequence_le_one n)) (norm_nonneg _)))
  · exact φ.integrable.norm.const_mul _
  · exact ae_of_all _ (fun ξ => (laplaceCubicPhase_tendsto ξ).mul_const (φ ξ))

theorem laplaceDamped_schwartz_integral_tendsto (f : ℝ → ℂ /- [definition] -/)
    (M : ℝ /- [definition] -/) (hM : 0 ≤ M /- [standing] -/)
    (hbound : ∀ x : ℝ, ‖f x‖ ≤ M /- [standing] -/)
    (hmeas : AEStronglyMeasurable f volume /- [standing] -/)
    (hf : Integrable (laplaceDamped f 1) /- [standing] -/ )
    (φ : 𝓢(ℝ, ℂ) /- [definition] -/ ) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, laplaceDamped f (laplaceDampingSequence n) x * φ x)
      atTop (𝓝 (∫ x : ℝ, f x * φ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x : ℝ => M*‖φ x‖ + ‖laplaceDamped f 1 x‖*SchwartzMap.seminorm ℂ 0 0 φ)
  · exact Eventually.of_forall (fun n => by
      have he : Continuous (fun x : ℝ => Complex.exp ((laplaceDampingSequence n : ℂ)*(x:ℂ))) := by fun_prop
      exact (he.aestronglyMeasurable.mul hmeas).mul φ.continuous.aestronglyMeasurable)
  · exact Eventually.of_forall (fun n => ae_of_all _ (fun x => by
      have hp := laplaceDampingSequence_pos n
      have h1 := laplaceDampingSequence_le_one n
      have hn := norm_nonneg (f x)
      have hφ := φ.norm_le_seminorm ℂ x
      have hφn := norm_nonneg (φ x)
      simp only [laplaceDamped, norm_mul, Complex.norm_exp, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, one_mul]
      by_cases hx : 0 ≤ x
      · have he : Real.exp (laplaceDampingSequence n*x) ≤ Real.exp x := by
          apply Real.exp_le_exp.mpr
          nlinarith
        have hh := mul_le_mul_of_nonneg_right he hn
        have hh' := mul_le_mul hh hφ hφn (mul_nonneg (Real.exp_pos x).le hn)
        linarith [mul_nonneg hM hφn]
      · have he : Real.exp (laplaceDampingSequence n*x) ≤ 1 := by
          rw [← Real.exp_zero]
          apply Real.exp_le_exp.mpr
          exact mul_nonpos_of_nonneg_of_nonpos hp.le (le_of_not_ge hx)
        have hh := mul_le_mul he (hbound x) hn (by norm_num : (0 : ℝ) ≤ 1)
        simp only [one_mul] at hh
        have hh' := mul_le_mul_of_nonneg_right hh hφn
        have hs : 0 ≤ SchwartzMap.seminorm ℂ 0 0 φ := apply_nonneg _ _
        linarith [mul_nonneg (mul_nonneg (Real.exp_pos x).le hn) hs]))
  · exact (φ.integrable.norm.const_mul M).add (hf.norm.mul_const _)
  · exact ae_of_all _ (fun x => by
      have hb := Complex.continuous_ofReal.continuousAt.tendsto.comp laplaceDampingSequence_tendsto
      change Tendsto (fun n : ℕ => (laplaceDampingSequence n : ℂ)) atTop (𝓝 (0 : ℂ)) at hb
      have he := Complex.continuous_exp.continuousAt.tendsto.comp (hb.mul_const (x : ℂ))
      simpa only [laplaceDamped, Function.comp_apply, zero_mul, Complex.exp_zero, one_mul] using! (he.mul_const (f x)).mul_const (φ x))
theorem airyAi_fourier_unit_normalization :
    𝓕 airyAiTempered = fourierAiryPhaseTempered := by
  ext φ
  obtain ⟨M, hM, hb⟩ := airyAiReal_globally_bounded
  have hbc : ∀ x : ℝ, ‖airyAiComplexReal x‖ ≤ M := by
    intro x
    simpa only [airyAiComplexReal, Complex.norm_real, Real.norm_eq_abs] using hb x
  have hm : AEStronglyMeasurable airyAiComplexReal volume :=
    (Complex.continuous_ofReal.comp continuous_airyAiReal).aestronglyMeasurable
  have h1 : Integrable (laplaceDamped airyAiComplexReal 1) :=
    airyLaplaceComplex_integrable (1 : ℂ) (by norm_num)
  have hs := laplaceDamped_schwartz_integral_tendsto airyAiComplexReal M hM.le hbc hm h1 (𝓕 φ)
  have ht := laplaceCubicPhase_schwartz_integral_tendsto φ
  have he (n : ℕ) :
      (∫ ξ : ℝ, Complex.exp ((airyLaplaceFrequency (laplaceDampingSequence n) ξ)^3/3)*φ ξ) =
      ∫ x : ℝ, laplaceDamped airyAiComplexReal (laplaceDampingSequence n) x * (𝓕 φ) x := by
    have hf : Integrable (laplaceDamped airyAiComplexReal (laplaceDampingSequence n)) :=
      airyLaplaceComplex_integrable (laplaceDampingSequence n : ℂ)
        (by simpa only [Complex.ofReal_re] using laplaceDampingSequence_pos n)
    calc
      _ = ∫ ξ : ℝ, (𝓕 (laplaceDamped airyAiComplexReal (laplaceDampingSequence n))) ξ * φ ξ := by
        apply integral_congr_ae
        filter_upwards [] with ξ
        rw [fourier_laplaceDamped_eq, airyLaplaceComplex_vertical_eq_exp_cubic _ ξ (laplaceDampingSequence_pos n)]
      _ = _ := fourier_integral_pairing _ hf φ
  have hs' := hs.congr' (Eventually.of_forall (fun n => (he n).symm))
  have hv := tendsto_nhds_unique hs' ht
  rw [TemperedDistribution.fourier_apply, airyAiTempered_apply]
  change (∫ x : ℝ, (𝓕 φ) x * (airyAiReal x : ℂ)) =
    ∫ ξ : ℝ, φ ξ • fourierAiryPhase ξ
  simpa only [airyAiComplexReal, fourierAiryPhase, smul_eq_mul, mul_comm] using hv

theorem airyFourierCoefficient_eq_one : airyFourierCoefficient = 1 :=
  airyAi_fourier_eq_phase_iff_coefficient_one.mp airyAi_fourier_unit_normalization

theorem airyAi_fourier_normalized_joint_probe :
    airyAiTempered ≠ 0 ∧ airyAiReal 0 > 0 ∧
    (∀ κ : ℂ, 0 < κ.re → Integrable (fun x : ℝ => Complex.exp (κ*(x:ℂ))*airyAiComplexReal x)) ∧
    (∀ κ : ℂ, 0 < κ.re →
      (∫ x : ℝ, (x:ℂ)*(Complex.exp (κ*(x:ℂ))*airyAiComplexReal x)) =
        κ^2*complexLaplaceIntegral airyAiComplexReal κ) ∧
    realLaplaceIntegral airyAiReal 1 = Real.exp (1/3) ∧
    airyFourierCoefficient = 1 ∧ 𝓕 airyAiTempered = fourierAiryPhaseTempered := by
  refine ⟨airyAiTempered_ne_zero, airyAiReal_zero_pos,
    airyLaplaceComplex_integrable, airyLaplaceComplex_coordinate_identity, ?_,
    airyFourierCoefficient_eq_one, airyAi_fourier_unit_normalization⟩
  simpa using airyLaplaceReal_eq_exp_cubic 1 (by norm_num)



theorem airyDamped_fourier_eq
    (β ξ : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    (𝓕 (laplaceDamped airyAiComplexReal β)) ξ =
      Complex.exp ((airyLaplaceFrequency β ξ)^3 / 3) := by
  rw [fourier_laplaceDamped_eq, airyLaplaceComplex_vertical_eq_exp_cubic β ξ hβ]

theorem airyDamped_fourier_norm
    (β ξ : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    ‖(𝓕 (laplaceDamped airyAiComplexReal β)) ξ‖ =
      Real.exp (β^3 / 3 - β * (2 * Real.pi * ξ)^2) := by
  rw [airyDamped_fourier_eq β ξ hβ, Complex.norm_exp, airyLaplaceFrequency_cubic_re]

theorem airyDamped_fourier_norm_le
    (β ξ : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    ‖(𝓕 (laplaceDamped airyAiComplexReal β)) ξ‖ ≤ Real.exp (β^3 / 3) := by
  rw [airyDamped_fourier_norm β ξ hβ]
  apply Real.exp_le_exp.mpr
  exact sub_le_self _ (mul_nonneg hβ.le (sq_nonneg _))

theorem airyDamped_fourier_integrable
    (β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    Integrable (𝓕 (laplaceDamped airyAiComplexReal β)) := by
  have hd : Integrable (fun ξ : ℝ =>
      Real.exp (β^3 / 3) * Real.exp (-(β * (2 * Real.pi)^2) * ξ^2)) :=
    (integrable_exp_neg_mul_sq (mul_pos hβ (sq_pos_of_pos (by positivity)))).const_mul _
  apply hd.mono' ?_ ?_
  · exact (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂
      (airyLaplaceComplex_integrable (β : ℂ) (by simpa using hβ))).aestronglyMeasurable
  · exact ae_of_all _ (fun ξ => by
      rw [airyDamped_fourier_norm β ξ hβ, ← Real.exp_add]
      apply le_of_eq
      congr 1
      ring)

/-- Genuine Airy inversion at every point, with positive damping and no improper integral. -/
theorem airyDamped_inverse_fourier
    (β x : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    (𝓕⁻ (𝓕 (laplaceDamped airyAiComplexReal β))) x =
      laplaceDamped airyAiComplexReal β x := by
  apply congrFun (Continuous.fourierInv_fourier_eq ?_ ?_ ?_) x
  · exact (by fun_prop : Continuous (fun x : ℝ => Complex.exp ((β : ℂ) * (x : ℂ)))).mul
      (Complex.continuous_ofReal.comp continuous_airyAiReal)
  · exact airyLaplaceComplex_integrable (β : ℂ) (by simpa using hβ)
  · exact airyDamped_fourier_integrable β hβ

theorem airyDamped_joint_probe
    (β : ℝ /- [definition] -/)
    (hβ : 0 < β /- [standing] -/) :
    airyAiReal 0 > 0 ∧ Integrable (laplaceDamped airyAiComplexReal β) ∧
      Integrable (𝓕 (laplaceDamped airyAiComplexReal β)) ∧
      (∀ ξ, ‖(𝓕 (laplaceDamped airyAiComplexReal β)) ξ‖ ≤ Real.exp (β^3 / 3)) ∧
      (∀ x, (𝓕⁻ (𝓕 (laplaceDamped airyAiComplexReal β))) x =
        laplaceDamped airyAiComplexReal β x) := by
  exact ⟨airyAiReal_zero_pos,
    airyLaplaceComplex_integrable (β : ℂ) (by simpa using hβ),
    airyDamped_fourier_integrable β hβ, fun ξ => airyDamped_fourier_norm_le β ξ hβ,
    fun x => airyDamped_inverse_fourier β x hβ⟩
end RMTFoundations.Airy

#print axioms RMTFoundations.Airy.airyAiReal_globally_bounded
#print axioms RMTFoundations.Airy.airyAiComplexReal
#print axioms RMTFoundations.Airy.airyAiComplexReal_memLp_top
#print axioms RMTFoundations.Airy.airyAiTempered
#print axioms RMTFoundations.Airy.airyAiTempered_apply
#print axioms RMTFoundations.Airy.airyAiReal_deriv_polynomial_bound
#print axioms RMTFoundations.Airy.schwartz_mul_polynomial_bound_integrable
#print axioms RMTFoundations.Airy.airyAi_schwartz_integrable
#print axioms RMTFoundations.Airy.airyAi_deriv_schwartz_integrable
#print axioms RMTFoundations.Airy.airyAi_coordinate_schwartz_integrable
#print axioms RMTFoundations.Airy.airyAi_schwartz_weak_ode
#print axioms RMTFoundations.Airy.coordinateMultiplier
#print axioms RMTFoundations.Airy.coordinateMultiplier_fourier_deriv
#print axioms RMTFoundations.Airy.coordinateMultiplier_fourier
#print axioms RMTFoundations.Airy.airy_tempered_fourier_ode
#print axioms RMTFoundations.Airy.fourierAiryPhase
#print axioms RMTFoundations.Airy.fourierAiryPhase_hasDerivAt
#print axioms RMTFoundations.Airy.classical_fourier_ode_solution
#print axioms RMTFoundations.Airy.fourierAiryPhase_norm
#print axioms RMTFoundations.Airy.polynomial_real_eval_hasTemperateGrowth
#print axioms RMTFoundations.Airy.fourierAiryPhaseDerivativePolynomial
#print axioms RMTFoundations.Airy.fourierAiryPhase_iteratedDeriv
#print axioms RMTFoundations.Airy.fourierAiryPhase_hasTemperateGrowth
#print axioms RMTFoundations.Airy.inverseFourierAiryPhase
#print axioms RMTFoundations.Airy.inverseFourierAiryPhase_hasTemperateGrowth
#print axioms RMTFoundations.Airy.inverseFourierAiryPhase_hasDerivAt
#print axioms RMTFoundations.Airy.fourierAiryPhase_mul_inverse
#print axioms RMTFoundations.Airy.schwartzCumulative
#print axioms RMTFoundations.Airy.schwartzCumulative_eq_interval
#print axioms RMTFoundations.Airy.schwartzCumulative_hasDerivAt
#print axioms RMTFoundations.Airy.schwartzCumulative_deriv
#print axioms RMTFoundations.Airy.schwartzCumulative_smooth
#print axioms RMTFoundations.Airy.schwartz_tail_moment_bound
#print axioms RMTFoundations.Airy.schwartzCumulative_decay
#print axioms RMTFoundations.Airy.schwartzZeroIntegralPrimitive
#print axioms RMTFoundations.Airy.schwartzZeroIntegralPrimitive_deriv
#print axioms RMTFoundations.Airy.tempered_deriv_zero_eq_constant_on_tests
#print axioms RMTFoundations.Airy.normalizedSchwartzTest
#print axioms RMTFoundations.Airy.normalizedSchwartzTest_integral
#print axioms RMTFoundations.Airy.tempered_deriv_zero_eq_constant
#print axioms RMTFoundations.Airy.schwartz_deriv_integral_zero
#print axioms RMTFoundations.Airy.schwartzPrimitive_nonzero_probe
#print axioms RMTFoundations.Airy.schwartz_deriv_smulLeft
#print axioms RMTFoundations.Airy.tempered_deriv_smulLeft
#print axioms RMTFoundations.Airy.schwartz_lineDeriv_one
#print axioms RMTFoundations.Airy.tempered_lineDeriv_one
#print axioms RMTFoundations.Airy.fourierAiryPhaseTempered
#print axioms RMTFoundations.Airy.tempered_cubic_ode_integrating_factor
#print axioms RMTFoundations.Airy.phase_multiplier_inverse
#print axioms RMTFoundations.Airy.phase_multiplier_volume
#print axioms RMTFoundations.Airy.tempered_cubic_ode_solution
#print axioms RMTFoundations.Airy.tempered_airy_fourier_proportional
#print axioms RMTFoundations.Airy.airyAiTempered_ode
#print axioms RMTFoundations.Airy.airyAiTempered_ne_zero
#print axioms RMTFoundations.Airy.airyFourierNormalizationTest
#print axioms RMTFoundations.Airy.fourierAiryPhaseTempered_normalization_test
#print axioms RMTFoundations.Airy.airyFourierCoefficient
#print axioms RMTFoundations.Airy.airyAi_fourier_eq_coefficient_phase
#print axioms RMTFoundations.Airy.airyFourierCoefficient_integral
#print axioms RMTFoundations.Airy.airyFourierCoefficient_ne_zero
#print axioms RMTFoundations.Airy.airyAi_fourier_joint_probe
#print axioms RMTFoundations.Airy.fourierAiryPhaseTempered_ne_zero
#print axioms RMTFoundations.Airy.airyAi_fourier_eq_phase_iff_coefficient_one
#print axioms RMTFoundations.Airy.airyAi_fourier_eq_phase_iff_scalar_integral_one
#print axioms RMTFoundations.Airy.airyLeadF
#print axioms RMTFoundations.Airy.continuous_airyLeadF
#print axioms RMTFoundations.Airy.cosh_sub_one_sub_half_sq_le
#print axioms RMTFoundations.Airy.tendsto_div_sqrt_atTop
#print axioms RMTFoundations.Airy.mul_cosh_div_sqrt_sub_one_ge
#print axioms RMTFoundations.Airy.tendsto_mul_cosh_div_sqrt_sub_one
#print axioms RMTFoundations.Airy.tendsto_integral_airyLeadF_mul
#print axioms RMTFoundations.Airy.sqrt_two_div_pi_mul_integral_exp_neg_half_sq
#print axioms RMTFoundations.Airy.schlaefli_master_isEquivalent
#print axioms RMTFoundations.Airy.schlaefliK13_isEquivalent
#print axioms RMTFoundations.Airy.sqrt_pi_div_two_mul_g
#print axioms RMTFoundations.Airy.sqrt_pi_div_two_mul_pi
#print axioms RMTFoundations.Airy.airyAiReal_prefactor
#print axioms RMTFoundations.Airy.airyAiReal_isEquivalent
#print axioms RMTFoundations.Airy.airyLaplaceProfile
#print axioms RMTFoundations.Airy.airyLaplaceProfile_continuous
#print axioms RMTFoundations.Airy.airyLaplaceProfile_tendsto
#print axioms RMTFoundations.Airy.airyLaplaceProfile_bounded
#print axioms RMTFoundations.Airy.laplaceSaddleDensity
#print axioms RMTFoundations.Airy.laplaceSaddle_exponent_le
#print axioms RMTFoundations.Airy.laplaceSaddle_factor_le
#print axioms RMTFoundations.Airy.laplaceSaddle_density_bound
#print axioms RMTFoundations.Airy.laplaceSaddle_envelope_integrable
#print axioms RMTFoundations.Airy.laplaceSaddle_pointwise_tendsto
#print axioms RMTFoundations.Airy.laplaceSaddle_integral_tendsto
#print axioms RMTFoundations.Airy.laplaceSaddle_joint_probe
#print axioms RMTFoundations.Airy.laplaceSaddle_cubic_identity
#print axioms RMTFoundations.Airy.airyLaplaceSquareDensity
#print axioms RMTFoundations.Airy.airyLaplaceSaddle_pointwise
#print axioms RMTFoundations.Airy.airyLaplaceSaddle_integral_eq
#print axioms RMTFoundations.Airy.airyLaplacePositive_normalized_tendsto
#print axioms RMTFoundations.Airy.airyLaplacePositive_integrable
#print axioms RMTFoundations.Airy.airyLaplaceNegative_integrable
#print axioms RMTFoundations.Airy.airyLaplace_integrable
#print axioms RMTFoundations.Airy.laplaceMomentNegative_bound
#print axioms RMTFoundations.Airy.airyLaplaceCoordinate_integrable
#print axioms RMTFoundations.Airy.laplaceCubic_exp_tendsto_zero
#print axioms RMTFoundations.Airy.airyLaplaceNegative_normalized_tendsto
#print axioms RMTFoundations.Airy.airyLaplace_normalized_tendsto
#print axioms RMTFoundations.Airy.laplaceCutoffBump
#print axioms RMTFoundations.Airy.laplaceCutoffBump_hasCompactSupport
#print axioms RMTFoundations.Airy.laplaceCutoffBump_zero
#print axioms RMTFoundations.Airy.laplaceCutoffTest
#print axioms RMTFoundations.Airy.laplaceCutoffTest_apply
#print axioms RMTFoundations.Airy.laplaceCutoffTest_zero
#print axioms RMTFoundations.Airy.laplaceCutoffDerivative
#print axioms RMTFoundations.Airy.laplaceCutoffTest_hasDerivAt
#print axioms RMTFoundations.Airy.laplaceCutoffDerivative_hasDerivAt
#print axioms RMTFoundations.Airy.laplaceCutoffTest_second_deriv
#print axioms RMTFoundations.Airy.laplaceCutoffTest_joint_probe
#print axioms RMTFoundations.Airy.schwartz_scaled_integrable
#print axioms RMTFoundations.Airy.schwartz_scaled_integral_tendsto
#print axioms RMTFoundations.Airy.weakAiry_laplace_identity
#print axioms RMTFoundations.Airy.realLaplaceIntegral
#print axioms RMTFoundations.Airy.realLaplaceIntegral_hasDerivAt
#print axioms RMTFoundations.Airy.realLaplaceIntegral_eq_exp_cubic
#print axioms RMTFoundations.Airy.airyLaplaceFrequency
#print axioms RMTFoundations.Airy.complexLaplaceIntegral
#print axioms RMTFoundations.Airy.airyLaplaceFrequency_re
#print axioms RMTFoundations.Airy.complexLaplaceIntegral_vertical_hasDerivAt
#print axioms RMTFoundations.Airy.complexLaplaceIntegral_vertical_eq_exp_cubic
#print axioms RMTFoundations.Airy.airyLaplaceComplex_integrable
#print axioms RMTFoundations.Airy.airyLaplaceComplexCoordinate_integrable
#print axioms RMTFoundations.Airy.airyLaplaceComplex_coordinate_identity
#print axioms RMTFoundations.Airy.airyLaplaceReal_coordinate_identity
#print axioms RMTFoundations.Airy.airyLaplaceReal_eq_exp_cubic
#print axioms RMTFoundations.Airy.airyLaplaceComplex_real_eq_exp_cubic
#print axioms RMTFoundations.Airy.airyLaplaceComplex_vertical_eq_exp_cubic
#print axioms RMTFoundations.Airy.airyAi_laplace_all_binder_probe
#print axioms RMTFoundations.Airy.laplaceDampingSequence
#print axioms RMTFoundations.Airy.laplaceDampingSequence_pos
#print axioms RMTFoundations.Airy.laplaceDampingSequence_le_one
#print axioms RMTFoundations.Airy.laplaceDampingSequence_tendsto
#print axioms RMTFoundations.Airy.laplaceDamped
#print axioms RMTFoundations.Airy.fourier_laplaceDamped_eq
#print axioms RMTFoundations.Airy.fourier_integral_pairing
#print axioms RMTFoundations.Airy.airyLaplaceFrequency_cubic_re
#print axioms RMTFoundations.Airy.laplaceCubicPhase_bound
#print axioms RMTFoundations.Airy.laplaceCubicPhase_tendsto
#print axioms RMTFoundations.Airy.laplaceCubicPhase_schwartz_integral_tendsto
#print axioms RMTFoundations.Airy.laplaceDamped_schwartz_integral_tendsto
#print axioms RMTFoundations.Airy.airyAi_fourier_unit_normalization
#print axioms RMTFoundations.Airy.airyFourierCoefficient_eq_one
#print axioms RMTFoundations.Airy.airyAi_fourier_normalized_joint_probe
#print axioms RMTFoundations.Airy.airyDamped_fourier_eq
#print axioms RMTFoundations.Airy.airyDamped_fourier_norm
#print axioms RMTFoundations.Airy.airyDamped_fourier_norm_le
#print axioms RMTFoundations.Airy.airyDamped_fourier_integrable
#print axioms RMTFoundations.Airy.airyDamped_inverse_fourier
#print axioms RMTFoundations.Airy.airyDamped_joint_probe
