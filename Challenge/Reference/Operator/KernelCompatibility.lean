import Challenge.Reference.Operator.Fredholm
import Challenge.Reference.Airy.KernelDeterminant

namespace RMTFoundations.Fredholm

open MeasureTheory Filter Topology

/-- Canonical TWC kernelFredholm agrees with the entire Gram series at real couplings. -/
theorem kernelFredholm_eq_gram
    {E X : Type* /- [definition] -/ }
    [NormedAddCommGroup E /- [definition] -/ ]
    [InnerProductSpace ℝ E /- [definition] -/ ]
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    (r c : X → E /- [definition] -/ )
    (hr : MemLp r 2 μ /- [standing] -/ )
    (hc : MemLp c 2 μ /- [standing] -/ )
    (k : X → X → ℝ /- [definition] -/ )
    (S : Set X /- [definition] -/ )
    (hS : ∀ᵐ x ∂μ, x ∈ S /- [standing] -/ )
    (hk : ∀ x ∈ S, ∀ y ∈ S, k x y = inner ℝ (r x) (c y)  /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : RMTFoundations.AiryKernel.kernelFredholm μ k (z : ℂ) =
      (kernelFredholmSeries (𝕜 := ℝ) μ r c z : ℂ)  := by
  unfold RMTFoundations.AiryKernel.kernelFredholm RMTFoundations.AiryKernel.kernelSeries
    RMTFoundations.AiryKernel.kernelCoefficient RMTFoundations.AiryKernel.kernelMinor
  exact kernelIntegralSeries_eq_gram μ r c hr hc k S hS hk z

/-- Canonical kernel/operator equality for two genuine HS integral factors. -/
theorem kernelFredholm_convolution_eq_realOperatorDet_comp
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
    (hr : MemLp r 2 μ /- [standing] -/ )
    (hc : MemLp c 2 μ /- [standing] -/ )
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
  unfold RMTFoundations.AiryKernel.kernelFredholm RMTFoundations.AiryKernel.kernelSeries
    RMTFoundations.AiryKernel.kernelCoefficient RMTFoundations.AiryKernel.kernelMinor
  exact kernelIntegralSeries_convolution_eq_realOperatorDet_comp μ b A B hA hB a d r c hr hc
    S hS hra hcd happlyA happlyBadj z

/-- Canonical basis-free kernel formula for the symmetric HS square needed by TW2. -/
theorem kernelFredholm_gram_eq_realOperatorDet_square
    {X ι : Type* /- [definition] -/ }
    [MeasurableSpace X /- [definition] -/ ]
    (μ : Measure X /- [definition] -/ )
    [SigmaFinite μ /- [definition] -/ ]
    [Countable ι /- [definition] -/ ]
    (b : HilbertBasis ι ℝ (Lp ℝ 2 μ)  /- [definition] -/ )
    (H : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ /- [definition] -/ )
    (hH : Summable (fun i => ‖H (b i)‖ ^ 2)  /- [standing] -/ )
    (hself : H.adjoint = H /- [standing] -/ )
    (r : X → Lp ℝ 2 μ /- [definition] -/ )
    (hr : MemLp r 2 μ /- [standing] -/ )
    (heval : ∀ f, ∀ᵐ x ∂μ, (H f) x = inner ℝ (r x) f /- [standing] -/ )
    (z : ℝ /- [definition] -/ )
    : RMTFoundations.AiryKernel.kernelFredholm μ
        (fun x y => inner ℝ (r x) (r y)) (z : ℂ) = (realOperatorDet b (H ∘L H) z : ℂ)  := by
  rw [kernelFredholm_eq_gram μ r r hr hr (fun x y => inner ℝ (r x) (r y))
    Set.univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _)) (fun _ _ _ _ => rfl) z,
    kernelFredholmSeries_gram_eq_realOperatorDet_square μ b H hH hself r hr heval z]

/-- A simultaneous nonzero L2 witness for the canonical-name theorem, beyond the unit disk. -/
theorem kernelFredholm_operator_joint_probe
    : ∃ b : HilbertBasis (Fin 1) ℝ (Lp ℝ 2 (Measure.dirac (0 : ℝ))),
      ∃ H : Lp ℝ 2 (Measure.dirac (0 : ℝ)) →L[ℝ] Lp ℝ 2 (Measure.dirac (0 : ℝ)),
      ∃ r : ℝ → Lp ℝ 2 (Measure.dirac (0 : ℝ)),
      Summable (fun i => ‖H (b i)‖ ^ 2) ∧ H.adjoint = H ∧
      MemLp r 2 (Measure.dirac (0 : ℝ)) ∧ ‖H (b 0)‖ = 2 ∧ ‖r 0‖ = 2 ∧
      (∀ f, ∀ᵐ x ∂Measure.dirac (0 : ℝ), (H f) x = inner ℝ (r x) f) ∧
      RMTFoundations.AiryKernel.kernelFredholm (Measure.dirac (0 : ℝ))
        (fun x y => inner ℝ (r x) (r y)) (-1) = (realOperatorDet b (H ∘L H) (-1) : ℂ) := by
  obtain ⟨b, H, r, hH, hself, hr, hnorm, hrnorm, hev, _, _⟩ := kernel_operator_all_binder_probe
  refine ⟨b, H, r, hH, hself, hr, hnorm, hrnorm, hev, ?_⟩
  simpa only [Complex.ofReal_neg, Complex.ofReal_one] using
    kernelFredholm_gram_eq_realOperatorDet_square (Measure.dirac (0 : ℝ)) b H hH hself r hr hev (-1)


end RMTFoundations.Fredholm

#print axioms RMTFoundations.Fredholm.kernelFredholm_eq_gram
#print axioms RMTFoundations.Fredholm.kernelFredholm_convolution_eq_realOperatorDet_comp
#print axioms RMTFoundations.Fredholm.kernelFredholm_gram_eq_realOperatorDet_square
#print axioms RMTFoundations.Fredholm.kernelFredholm_operator_joint_probe
