import RMTFoundations.Airy.KernelDeterminant


set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open MeasureTheory Set Filter
open scoped Topology

/-- Complex GOE Airy-Hankel Fredholm function on the positive half-line. -/
noncomputable abbrev TW1 : ℝ → ℂ := RMTFoundations.AiryKernel.TW1
/-- Complex GUE Airy-kernel Fredholm function on the positive half-line. -/
noncomputable abbrev TW2 : ℝ → ℂ := RMTFoundations.AiryKernel.TW2
/-- Real part of TW1; its imaginary part is proved zero. -/
noncomputable abbrev TW1R : ℝ → ℝ := RMTFoundations.AiryKernel.TW1R
/-- Real part of TW2; its imaginary part is proved zero. -/
noncomputable abbrev TW2R : ℝ → ℝ := RMTFoundations.AiryKernel.TW2R

/-- The real GOE function recovers the full complex Fredholm value. -/
theorem TW1R_coe (s : ℝ /- [definition] -/) : (TW1R s : ℂ) = TW1 s :=
  RMTFoundations.AiryKernel.TW1R_coe s
/-- The real GUE function recovers the full complex Fredholm value. -/
theorem TW2R_coe (s : ℝ /- [definition] -/) : (TW2R s : ℂ) = TW2 s :=
  RMTFoundations.AiryKernel.TW2R_coe s
/-- TW1 is a continuous complex-valued function of the real cutoff. -/
theorem continuous_TW1 : Continuous TW1 := RMTFoundations.AiryKernel.TW1_continuous
/-- TW2 is a continuous complex-valued function of the real cutoff. -/
theorem continuous_TW2 : Continuous TW2 := RMTFoundations.AiryKernel.TW2_continuous
/-- The real GOE function is continuous on the entire real line. -/
theorem continuous_TW1R : Continuous TW1R := RMTFoundations.AiryKernel.TW1R_continuous
/-- The real GUE function is continuous on the entire real line. -/
theorem continuous_TW2R : Continuous TW2R := RMTFoundations.AiryKernel.TW2R_continuous
/-- GOE Fredholm formula with the physical kernel Ai(x+y+s) on (0,infinity). -/
theorem TW1_fredholm (s : ℝ /- [definition] -/) :
    TW1 s = RMTFoundations.AiryKernel.kernelFredholm
      RMTFoundations.Airy.halfLineMeasure
      (fun x y => RMTFoundations.Airy.airyAiReal (x+y+s)) (-1) := rfl
/-- GUE Fredholm formula with the physical shifted Airy kernel on (0,infinity). -/
theorem TW2_fredholm (s : ℝ /- [definition] -/) :
    TW2 s = RMTFoundations.AiryKernel.kernelFredholm
      RMTFoundations.Airy.halfLineMeasure
      (fun x y => RMTFoundations.Airy.airyKernelIntegral (x+s) (y+s)) (-1) := rfl
/-- GOE on the moving half-line (s/2,infinity); the half-shift is essential. -/
theorem TW1_fredholm_halfLine (s : ℝ /- [definition] -/) :
    TW1 s = RMTFoundations.AiryKernel.kernelFredholm
      (RMTFoundations.AiryKernel.fredholmHalfLineMeasure (s/2))
      (fun x y => RMTFoundations.Airy.airyAiReal (x+y)) (-1) :=
  RMTFoundations.AiryKernel.TW1_halfLine s
/-- GUE on its physical moving half-line (s,infinity). -/
theorem TW2_fredholm_halfLine (s : ℝ /- [definition] -/) :
    TW2 s = RMTFoundations.AiryKernel.kernelFredholm
      (RMTFoundations.AiryKernel.fredholmHalfLineMeasure s)
      RMTFoundations.Airy.airyKernelIntegral (-1) :=
  RMTFoundations.AiryKernel.TW2_halfLine s
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW1
#print axioms RMTFoundations.TracyWidom.TW2
#print axioms RMTFoundations.TracyWidom.TW1R
#print axioms RMTFoundations.TracyWidom.TW2R
#print axioms RMTFoundations.TracyWidom.TW1R_coe
#print axioms RMTFoundations.TracyWidom.TW2R_coe
#print axioms RMTFoundations.TracyWidom.continuous_TW1
#print axioms RMTFoundations.TracyWidom.continuous_TW2
#print axioms RMTFoundations.TracyWidom.continuous_TW1R
#print axioms RMTFoundations.TracyWidom.continuous_TW2R
#print axioms RMTFoundations.TracyWidom.TW1_fredholm
#print axioms RMTFoundations.TracyWidom.TW2_fredholm
#print axioms RMTFoundations.TracyWidom.TW1_fredholm_halfLine
#print axioms RMTFoundations.TracyWidom.TW2_fredholm_halfLine
