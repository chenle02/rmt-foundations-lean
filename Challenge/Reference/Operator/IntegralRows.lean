import Challenge.Reference.Operator.KernelCompatibility

namespace RMTFoundations.Fredholm

open MeasureTheory Filter Topology InnerProductSpace

/-- Countable Hilbert expansions turn genuine L2 application formulas into measurable rows. -/
theorem l2_operator_rows_aestronglyMeasurable
    {X ι : Type* /- [definition] -/ }
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)  /- [definition] -/ )
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ /- [definition] -/ )
    (r : X → Lp ℝ 2 μ /- [definition] -/ )
    (heval : ∀ f, ∀ᵐ x ∂μ, (A f) x = inner ℝ (r x) f /- [standing] -/ )
    : AEStronglyMeasurable r μ := by
  classical
  have hc (i : ι) : AEStronglyMeasurable (fun x => inner ℝ (b i) (r x)) μ := by
    apply (Lp.aestronglyMeasurable (A (b i))).congr
    filter_upwards [heval (b i)] with x hx
    exact hx.trans (real_inner_comm _ _)
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset ι))
    (f := fun s x => realBasisProjection b s (r x))
  · intro s
    simp only [realBasisProjection, ContinuousLinearMap.sum_apply, rankOne_apply]
    exact s.aestronglyMeasurable_fun_sum (fun i _ => (hc i).smul aestronglyMeasurable_const)
  · exact Eventually.of_forall (fun x => realBasisProjection_tendsto b (r x))

/-- The rows representing a genuine Hilbert--Schmidt L2 operator are themselves in L2.
No row measurability or row-norm integrability is postulated. -/
theorem l2_operator_rows_memLp
    {X ι : Type* /- [definition] -/ }
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)  /- [definition] -/ )
    (A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (r : X → Lp ℝ 2 μ /- [definition] -/ )
    (heval : ∀ f, ∀ᵐ x ∂μ, (A f) x = inner ℝ (r x) f /- [standing] -/ )
    : MemLp r 2 μ := by
  classical
  have hm := l2_operator_rows_aestronglyMeasurable μ b A r heval
  have hc (i : ι) : (fun x => inner ℝ (b i) (r x)) =ᵐ[μ] (fun x => (A (b i)) x) := by
    filter_upwards [heval (b i)] with x hx
    exact (real_inner_comm _ _).trans hx.symm
  have hi (i : ι) : Integrable (fun x => ‖inner ℝ (b i) (r x)‖ ^ 2) μ := by
    apply ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (A (b i)))).1
      (Lp.memLp (A (b i)))).congr
    filter_upwards [hc i] with x hx
    rw [hx]
  have hint (i : ι) : (∫ x, ‖inner ℝ (b i) (r x)‖ ^ 2 ∂μ) = ‖A (b i)‖ ^ 2 := by
    calc
      _ = ∫ x, ‖(A (b i)) x‖ ^ 2 ∂μ := integral_congr_ae ((hc i).fun_comp (fun t : ℝ => ‖t‖ ^ 2))
      _ = ‖A (b i)‖ ^ 2 := by
        simpa only [L2.inner_def, RCLike.inner_apply, starRingEnd_apply, star_trivial,
          Real.norm_eq_abs, sq_abs, ← pow_two] using real_inner_self_eq_norm_sq (A (b i))
  have hparseval (x : X) : ENNReal.ofReal (‖r x‖ ^ 2) =
      ∑' i, ENNReal.ofReal (‖inner ℝ (b i) (r x)‖ ^ 2) := by
    rw [← (realHilbertBasis_norm_sq_hasSum b (r x)).tsum_eq]
    exact ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (realHilbertBasis_norm_sq_hasSum b (r x)).summable
  have hlin : (∫⁻ x, ENNReal.ofReal (‖r x‖ ^ 2) ∂μ) =
      ∑' i, ENNReal.ofReal (‖A (b i)‖ ^ 2) := by
    simp_rw [hparseval]
    have hmeas (i : ι) : AEMeasurable
        (fun x => ENNReal.ofReal (‖inner ℝ (b i) (r x)‖ ^ 2)) μ := by
      simpa only [Pi.pow_apply] using
        ((hm.const_inner (𝕜 := ℝ) (c := b i)).norm.pow 2).aemeasurable.ennreal_ofReal
    rw [lintegral_tsum hmeas]
    apply tsum_congr
    intro i
    rw [← ofReal_integral_eq_lintegral_ofReal (hi i) (Eventually.of_forall (fun _ => sq_nonneg _)), hint i]
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hm).2 ?_
  norm_num only [ENNReal.toReal_ofNat]
  simp_rw [ENNReal.rpow_two, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  rw [hlin, ← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hA]
  exact ENNReal.ofReal_lt_top

/-- Genuine HS integral factors supply the row L2 conditions required by the canonical bridge. -/
theorem kernelFredholm_convolution_eq_of_integral_factors
    {X ι : Type* /- [definition] -/ }
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)  /- [definition] -/ )
    (A B : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ /- [definition] -/ )
    (hA : Summable (fun i => ‖A (b i)‖ ^ 2)  /- [standing] -/ )
    (hB : Summable (fun i => ‖B (b i)‖ ^ 2)  /- [standing] -/ )
    (a d : X → X → ℝ /- [definition] -/ )
    (r c : X → Lp ℝ 2 μ /- [definition] -/ )
    (S : Set X /- [definition] -/ )
    (hS : ∀ᵐ x ∂μ, x ∈ S /- [standing] -/ )
    (hra : ∀ x ∈ S, ∀ᵐ t ∂μ, (r x) t = a x t /- [standing] -/ )
    (hcd : ∀ y ∈ S, ∀ᵐ t ∂μ, (c y) t = d t y /- [standing] -/ )
    (happlyA : ∀ f, ∀ᵐ x ∂μ, (A f) x = ∫ t, a x t * f t ∂μ /- [standing] -/ )
    (happlyBadj : ∀ f, ∀ᵐ y ∂μ, (B.adjoint f) y = ∫ t, d t y * f t ∂μ /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : RMTFoundations.AiryKernel.kernelFredholm μ
        (fun x y => ∫ t, a x t * d t y ∂μ) (z : ℂ) =
      (realOperatorDet b (A ∘L B) z : ℂ)  := by
  have hevA (f : Lp ℝ 2 μ) : ∀ᵐ x ∂μ, (A f) x = inner ℝ (r x) f := by
    filter_upwards [hS, happlyA f] with x hx hAx
    rw [hAx, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hra x hx] with t ht
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, ht, mul_comm]
  have hevBadj (f : Lp ℝ 2 μ) : ∀ᵐ y ∂μ, (B.adjoint f) y = inner ℝ (c y) f := by
    filter_upwards [hS, happlyBadj f] with y hy hBy
    rw [hBy, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hcd y hy] with t ht
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, ht, mul_comm]
  exact kernelFredholm_convolution_eq_realOperatorDet_comp μ b A B hA hB a d r c
    (l2_operator_rows_memLp μ b A hA r hevA)
    (l2_operator_rows_memLp μ b B.adjoint (realHs_adjoint_square_summable b B hB) c hevBadj)
    S hS hra hcd happlyA happlyBadj z

/-- All hypotheses of row reconstruction and the reduced kernel bridge hold together nontrivially. -/
theorem integral_rows_all_binder_probe
    : ∃ b : HilbertBasis (Fin 1) ℝ (Lp ℝ 2 (Measure.dirac (0 : ℝ))),
      ∃ H : Lp ℝ 2 (Measure.dirac (0 : ℝ)) →L[ℝ] Lp ℝ 2 (Measure.dirac (0 : ℝ)),
      ∃ r : ℝ → Lp ℝ 2 (Measure.dirac (0 : ℝ)),
      Summable (fun i => ‖H (b i)‖ ^ 2) ∧ H.adjoint = H ∧
      ‖H (b 0)‖ = 2 ∧ ‖r 0‖ = 2 ∧
      (∀ f, ∀ᵐ x ∂Measure.dirac (0 : ℝ), (H f) x = inner ℝ (r x) f) ∧
      (∀ y, ∀ᵐ t ∂Measure.dirac (0 : ℝ), (r y) t = 2) ∧
      (∀ f, ∀ᵐ x ∂Measure.dirac (0 : ℝ), (H f) x = ∫ t, (2 : ℝ) * f t ∂Measure.dirac (0 : ℝ)) ∧
      AEStronglyMeasurable r (Measure.dirac (0 : ℝ)) ∧ MemLp r 2 (Measure.dirac (0 : ℝ)) ∧
      RMTFoundations.AiryKernel.kernelFredholm (Measure.dirac (0 : ℝ))
        (fun x y => ∫ t : ℝ, (2 : ℝ) * 2 ∂Measure.dirac (0 : ℝ)) (-1) =
        (realOperatorDet b (H ∘L H) (-1) : ℂ) := by
  obtain ⟨b, H, r, hH, hself, _, hnorm, hrnorm, hev, hrow, _⟩ := kernel_operator_all_binder_probe
  have hap (f : Lp ℝ 2 (Measure.dirac (0 : ℝ))) : ∀ᵐ x ∂Measure.dirac (0 : ℝ),
      (H f) x = ∫ t, (2 : ℝ) * f t ∂Measure.dirac (0 : ℝ) := by
    filter_upwards [hev f] with x hx
    rw [hx, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hrow x] with t ht
    simp [RCLike.inner_apply, ht, mul_comm]
  refine ⟨b, H, r, hH, hself, hnorm, hrnorm, hev, hrow, hap,
    l2_operator_rows_aestronglyMeasurable _ b H r hev, l2_operator_rows_memLp _ b H hH r hev, ?_⟩
  have h := kernelFredholm_convolution_eq_of_integral_factors
    (Measure.dirac (0 : ℝ)) b H H hH hH (fun _ _ => 2) (fun _ _ => 2) r r
    Set.univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
    (fun x _ => hrow x) (fun y _ => hrow y) hap (by simpa only [hself] using hap) (-1)
  simpa only [Complex.ofReal_neg, Complex.ofReal_one] using h


end RMTFoundations.Fredholm

#print axioms RMTFoundations.Fredholm.l2_operator_rows_aestronglyMeasurable
#print axioms RMTFoundations.Fredholm.l2_operator_rows_memLp
#print axioms RMTFoundations.Fredholm.kernelFredholm_convolution_eq_of_integral_factors
#print axioms RMTFoundations.Fredholm.integral_rows_all_binder_probe
