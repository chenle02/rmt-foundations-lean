import RMTFoundations.Airy.ODE
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Kernels of arbitrary Airy solutions

This layer assumes only the Airy ODE predicate, not a construction of Ai or Bi.
It proves the self-kernel's removable diagonal and assigns the limiting value
there. Its polarized kernel accepts two solution pairs without introducing the
nonremovable Wronskian pole of the unsymmetrized mixed quotient.

No Airy asymptotics, positivity, trace-class property, Fredholm determinant,
or joint continuity in both variables is asserted here.
-/

namespace RMTFoundations.Airy

variable {f df g dg : ℝ → ℝ /- [definition] -/ }

/-- The quotient away from the diagonal; division gives zero on the diagonal. -/
noncomputable def kernelQuotient (f df : ℝ → ℝ /- [definition] -/ ) (x y : ℝ /- [definition] -/ ) : ℝ :=
  (f x * df y - df x * f y) / (x - y)

theorem kernelQuotient_symm (f df : ℝ → ℝ /- [definition] -/ ) (x y : ℝ /- [definition] -/ ) :
    kernelQuotient f df x y = kernelQuotient f df y x := by
  unfold kernelQuotient
  rw [show f y * df x - df y * f x = -(f x * df y - df x * f y) by ring,
    show y - x = -(x - y) by ring, neg_div_neg_eq]

/-- The diagonal limit depends only on the ODE, not on an Ai construction. -/
theorem tendsto_kernelQuotient_diagonal (hf : IsAirySolution f df /- [standing] -/ ) (x : ℝ /- [definition] -/ ) :
    Filter.Tendsto (fun y => kernelQuotient f df x y) (nhdsWithin x {x}ᶜ)
      (nhds (df x ^ 2 - x * f x ^ 2)) := by
  have hd : HasDerivAt (fun y => f x * df y - df x * f y)
      (f x * (x * f x) - df x * df x) x :=
    ((hf.hasDerivAt_right x).const_mul (f x)).sub
      ((hf.hasDerivAt_left x).const_mul (df x))
  have h := (hasDerivAt_iff_tendsto_slope.1 hd).neg
  rw [show -(f x * (x * f x) - df x * df x) = df x ^ 2 - x * f x ^ 2 by ring] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [slope_def_field, show f x * df x - df x * f x = 0 by ring, sub_zero,
    kernelQuotient, show x - y = -(y - x) by ring, div_neg]

/-- The self-kernel with the genuine continuous diagonal value. -/
noncomputable def solutionKernel (f df : ℝ → ℝ /- [definition] -/ ) (x y : ℝ /- [definition] -/ ) : ℝ :=
  if x = y then df x ^ 2 - x * f x ^ 2 else kernelQuotient f df x y

theorem solutionKernel_self (f df : ℝ → ℝ /- [definition] -/ ) (x : ℝ /- [definition] -/ ) :
    solutionKernel f df x x = df x ^ 2 - x * f x ^ 2 := by
  simp [solutionKernel]

theorem solutionKernel_of_ne (f df : ℝ → ℝ /- [definition] -/ ) {x y : ℝ /- [definition] -/ } (h : x ≠ y /- [standing] -/ ) :
    solutionKernel f df x y = kernelQuotient f df x y := by
  simp [solutionKernel, h]

theorem solutionKernel_symm (f df : ℝ → ℝ /- [definition] -/ ) (x y : ℝ /- [definition] -/ ) :
    solutionKernel f df x y = solutionKernel f df y x := by
  by_cases h : x = y
  · subst y; rfl
  · rw [solutionKernel_of_ne f df h, solutionKernel_of_ne f df (Ne.symm h)]
    exact kernelQuotient_symm f df x y

theorem continuousAt_solutionKernel_diagonal (hf : IsAirySolution f df /- [standing] -/ ) (x : ℝ /- [definition] -/ ) :
    ContinuousAt (solutionKernel f df x) x := by
  rw [continuousAt_iff_punctured_nhds, solutionKernel_self]
  refine (tendsto_kernelQuotient_diagonal hf x).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (solutionKernel_of_ne f df (Ne.symm hy)).symm

/-- Each fixed-first-coordinate section is continuous, including on the diagonal. -/
theorem continuous_solutionKernel (hf : IsAirySolution f df /- [standing] -/ ) (x : ℝ /- [definition] -/ ) :
    Continuous (solutionKernel f df x) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases h : x = y
  · subst y; exact continuousAt_solutionKernel_diagonal hf x
  · have hc : ContinuousAt (kernelQuotient f df x) y :=
      ((continuousAt_const.mul hf.continuous_deriv.continuousAt).sub
        (continuousAt_const.mul hf.continuous.continuousAt)).div
        (continuousAt_const.sub continuousAt_id) (sub_ne_zero.mpr h)
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds (Ne.symm h)] with z hz
    exact solutionKernel_of_ne f df (Ne.symm hz)

/-- The symmetric bilinear polarization of the self-kernel. -/
noncomputable def polarizedKernel (f df g dg : ℝ → ℝ /- [definition] -/ ) (x y : ℝ /- [definition] -/ ) : ℝ :=
  (solutionKernel (fun t => f t + g t) (fun t => df t + dg t) x y -
    solutionKernel f df x y - solutionKernel g dg x y) / 2

theorem polarizedKernel_self (f df g dg : ℝ → ℝ /- [definition] -/ ) (x : ℝ /- [definition] -/ ) :
    polarizedKernel f df g dg x x = df x * dg x - x * f x * g x := by
  simp only [polarizedKernel, solutionKernel_self]
  ring

theorem polarizedKernel_of_ne (f df g dg : ℝ → ℝ /- [definition] -/ ) {x y : ℝ /- [definition] -/ } (h : x ≠ y /- [standing] -/ ) :
    polarizedKernel f df g dg x y =
      (f x * dg y + g x * df y - df x * g y - dg x * f y) / (2 * (x - y)) := by
  simp only [polarizedKernel, solutionKernel_of_ne _ _ h, kernelQuotient]
  field_simp
  ring

theorem polarizedKernel_symm (f df g dg : ℝ → ℝ /- [definition] -/ ) (x y : ℝ /- [definition] -/ ) :
    polarizedKernel f df g dg x y = polarizedKernel f df g dg y x := by
  simp only [polarizedKernel, solutionKernel_symm _ _ x y]

/-- Polarization is symmetric in its two solution pairs as well as in space. -/
theorem polarizedKernel_comm (f df g dg : ℝ → ℝ /- [definition] -/ ) (x y : ℝ /- [definition] -/ ) :
    polarizedKernel f df g dg x y = polarizedKernel g dg f df x y := by
  unfold polarizedKernel
  rw [show (fun t => f t + g t) = (fun t => g t + f t) by funext t; ring,
    show (fun t => df t + dg t) = (fun t => dg t + df t) by funext t; ring]
  ring

/-- The bilinear extension specializes exactly to the self-kernel. -/
theorem polarizedKernel_same (f df : ℝ → ℝ /- [definition] -/ ) (x y : ℝ /- [definition] -/ ) :
    polarizedKernel f df f df x y = solutionKernel f df x y := by
  by_cases h : x = y
  · subst y
    rw [polarizedKernel_self, solutionKernel_self]
    ring
  · rw [polarizedKernel_of_ne f df f df h, solutionKernel_of_ne f df h,
      kernelQuotient]
    field_simp
    ring

theorem continuous_polarizedKernel (hf : IsAirySolution f df /- [standing] -/ )
    (hg : IsAirySolution g dg /- [standing] -/ ) (x : ℝ /- [definition] -/ ) : Continuous (polarizedKernel f df g dg x) :=
  (((continuous_solutionKernel (airySolution_add hf hg) x).sub
    (continuous_solutionKernel hf x)).sub (continuous_solutionKernel hg x)).div_const 2

/-- The naive mixed numerator on the diagonal is the Wronskian, not zero. -/
theorem mixed_numerator_diagonal (hf : IsAirySolution f df /- [standing] -/ ) (hg : IsAirySolution g dg /- [standing] -/ )
    (x : ℝ /- [definition] -/ ) : f x * dg x - df x * g x = f 0 * dg 0 - df 0 * g 0 :=
  airyWronskian_eq hf hg x 0

end RMTFoundations.Airy

#print axioms RMTFoundations.Airy.kernelQuotient
#print axioms RMTFoundations.Airy.kernelQuotient_symm
#print axioms RMTFoundations.Airy.tendsto_kernelQuotient_diagonal
#print axioms RMTFoundations.Airy.solutionKernel
#print axioms RMTFoundations.Airy.solutionKernel_self
#print axioms RMTFoundations.Airy.solutionKernel_of_ne
#print axioms RMTFoundations.Airy.solutionKernel_symm
#print axioms RMTFoundations.Airy.continuousAt_solutionKernel_diagonal
#print axioms RMTFoundations.Airy.continuous_solutionKernel
#print axioms RMTFoundations.Airy.polarizedKernel
#print axioms RMTFoundations.Airy.polarizedKernel_self
#print axioms RMTFoundations.Airy.polarizedKernel_of_ne
#print axioms RMTFoundations.Airy.polarizedKernel_symm
#print axioms RMTFoundations.Airy.polarizedKernel_comm
#print axioms RMTFoundations.Airy.polarizedKernel_same
#print axioms RMTFoundations.Airy.continuous_polarizedKernel
#print axioms RMTFoundations.Airy.mixed_numerator_diagonal
