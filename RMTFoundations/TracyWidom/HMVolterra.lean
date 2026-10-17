import Mathlib
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace RMTFoundations.TracyWidom.HMVolterra
open Filter Set
open scoped Topology
/-- Difference of two cubic Painleve right-hand sides factors linearly. -/
theorem pii_difference_factor (s x y : ℝ /- [definition] -/)
    : (s*x+2*x^3)-(s*y+2*y^3) =
      (s+2*(x^2+x*y+y^2))*(x-y) := by ring
/-- The cubic divided difference is nonnegative even for opposite signs. -/
theorem cubic_divided_difference_nonneg (x y : ℝ /- [definition] -/)
    : 0 ≤ x^2+x*y+y^2 := by nlinarith [sq_nonneg (x+y),sq_nonneg x,sq_nonneg y]
/-- Sharp elementary cubic Lipschitz bound on a real bounded interval. -/
theorem cubic_lipschitz (x y M : ℝ /- [definition] -/)
    (hx : |x| ≤ M /- [standing] -/)
    (hy : |y| ≤ M /- [standing] -/)
    : |x^3-y^3| ≤ 3*M^2*|x-y| := by
  have hm : 0 ≤ M := (abs_nonneg x).trans hx
  have hxx : |x|^2 ≤ M^2 := pow_le_pow_left₀ (abs_nonneg x) hx 2
  have hyy : |y|^2 ≤ M^2 := pow_le_pow_left₀ (abs_nonneg y) hy 2
  have hxy : |x| *|y| ≤ M*M := mul_le_mul hx hy (abs_nonneg y) hm
  calc
    |x^3-y^3| = |x-y| *|x^2+x*y+y^2| := by rw [show x^3-y^3=(x-y)*(x^2+x*y+y^2) by ring,abs_mul]
    _ ≤ |x-y| *(|x|^2+|x| *|y| +|y|^2) := by
      gcongr
      calc
        |x^2+x*y+y^2| ≤ |x^2+x*y| +|y^2| := abs_add_le _ _
        _ ≤ |x^2| +|x*y| +|y^2| := by gcongr; exact abs_add_le _ _
        _ = _ := by simp [abs_mul,abs_pow]
    _ ≤ 3*M^2*|x-y| := by nlinarith [abs_nonneg (x-y)]
/-- Nonzero, opposite-sign joint witness exercises the sharp cubic bound. -/
theorem cubic_joint_probe : (1:ℝ) ≠ 0 ∧ (-1:ℝ) ≠ 0 ∧
    |(1:ℝ)| ≤ 1 ∧ |(-1:ℝ)| ≤ 1 ∧
    |(1:ℝ)^3-(-1:ℝ)^3| ≤ 3*(1:ℝ)^2*|1-(-1:ℝ)| := by
  refine ⟨by norm_num,by norm_num,by norm_num,by norm_num,?_⟩
  exact cubic_lipschitz 1 (-1) 1 (by norm_num) (by norm_num)

open MeasureTheory
/-- Tail uniqueness of bounded solutions to a genuine cubic integral equation.
This is a conditional Volterra theorem; the physical Airy representation and
small kernel mass for arbitrary PII solutions must be supplied separately. -/
theorem cubic_volterra_unique
    (u v g : ℝ → ℝ /- [definition] -/)
    (K : ℝ → ℝ → ℝ /- [definition] -/)
    (a M μ : ℝ /- [definition] -/)
    (hμ : 0 ≤ μ /- [standing] -/)
    (hu : ∀ t ≥ a, |u t| ≤ M /- [standing] -/)
    (hv : ∀ t ≥ a, |v t| ≤ M /- [standing] -/)
    (hsmall : 3*M^2*μ < 1 /- [standing] -/)
    (hK : ∀ s ≥ a, IntegrableOn (K s) (Ici s) /- [standing] -/)
    (hKu : ∀ s ≥ a, IntegrableOn (fun t => K s t*(u t)^3) (Ici s) /- [standing] -/)
    (hKv : ∀ s ≥ a, IntegrableOn (fun t => K s t*(v t)^3) (Ici s) /- [standing] -/)
    (hmass : ∀ s ≥ a, (∫ t in Ici s, |K s t|) ≤ μ /- [standing] -/)
    (hueq : ∀ s ≥ a, u s = g s+∫ t in Ici s, K s t*(u t)^3 /- [standing] -/)
    (hveq : ∀ s ≥ a, v s = g s+∫ t in Ici s, K s t*(v t)^3 /- [standing] -/)
    : EqOn u v (Ici a) := by
  let S : Set ℝ := (fun t => |u t-v t|) '' Ici a
  have hn : S.Nonempty := ⟨|u a-v a|,mem_image_of_mem _ (mem_Ici.mpr le_rfl)⟩
  have hb : BddAbove S := by
    refine ⟨2*M,?_⟩
    rintro x ⟨t,ht,rfl⟩
    calc
      |u t-v t| ≤ |u t| +|v t| := abs_sub _ _
      _ ≤ 2*M := by linarith [hu t ht,hv t ht]
  let D := sSup S
  have hD : 0 ≤ D := (abs_nonneg (u a-v a)).trans (le_csSup hb (mem_image_of_mem _ (mem_Ici.mpr le_rfl)))
  have hle : ∀ t ≥ a, |u t-v t| ≤ D := fun t ht => le_csSup hb (mem_image_of_mem _ ht)
  have hstep : ∀ s ≥ a, |u s-v s| ≤ 3*M^2*μ*D := by
    intro s hs
    have hint := (hKu s hs).sub (hKv s hs)
    have heq : u s-v s = ∫ t in Ici s, K s t*((u t)^3-(v t)^3) := by
      rw [hueq s hs,hveq s hs,show g s+(∫ t in Ici s,K s t*(u t)^3)-(g s+(∫ t in Ici s,K s t*(v t)^3))=
        (∫ t in Ici s,K s t*(u t)^3)-(∫ t in Ici s,K s t*(v t)^3) by ring,
        ← integral_sub (hKu s hs) (hKv s hs)]
      congr 1; funext t; ring
    have hdom : ∀ᵐ t ∂volume.restrict (Ici s),
        |K s t*((u t)^3-(v t)^3)| ≤ |K s t| *(3*M^2*D) := by
      filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (cubic_lipschitz (u t) (v t) M (hu t (hs.trans ht)) (hv t (hs.trans ht))).trans
        (mul_le_mul_of_nonneg_left (hle t (hs.trans ht)) (by positivity))
    have hi : IntegrableOn (fun t => K s t*((u t)^3-(v t)^3)) (Ici s) := by
      refine hint.congr (Eventually.of_forall (fun t => ?_))
      simp only [Pi.sub_apply]
      ring
    calc
      |u s-v s| = |∫ t in Ici s,K s t*((u t)^3-(v t)^3)| := congrArg abs heq
      _ ≤ ∫ t in Ici s,|K s t*((u t)^3-(v t)^3)| := abs_integral_le_integral_abs
      _ ≤ ∫ t in Ici s,|K s t| *(3*M^2*D) := integral_mono_ae hi.abs ((hK s hs).abs.mul_const _) hdom
      _ = (∫ t in Ici s,|K s t|)*(3*M^2*D) := integral_mul_const _ _
      _ ≤ μ*(3*M^2*D) := mul_le_mul_of_nonneg_right (hmass s hs) (by positivity)
      _ = 3*M^2*μ*D := by ring
  have hsup : D ≤ 3*M^2*μ*D := by
    apply csSup_le hn
    rintro x ⟨t,ht,rfl⟩
    exact hstep t ht
  have hk0 : 0 ≤ 3*M^2*μ := by positivity
  have hzero : D=0 := by nlinarith [hk0]
  intro t ht
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (by simpa [hzero] using hle t ht) (abs_nonneg _)))

noncomputable def compactKernel (s t : ℝ /- [definition] -/)
    : ℝ := (Icc s (s+1)).indicator (fun _ => (1/100:ℝ)) t
theorem kernel_integrable (s : ℝ /- [definition] -/)
    : Integrable (compactKernel s) := by
  exact (integrableOn_const (s := Icc s (s+1)) (C := (1/100:ℝ)) isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
theorem kernel_integral (s : ℝ /- [definition] -/)
    : (∫ t in Ici s,compactKernel s t)=(1/100:ℝ) := by
  simp only [compactKernel]
  rw [integral_indicator measurableSet_Icc]
  rw [Measure.restrict_restrict measurableSet_Icc]
  have he : Icc s (s+1) ∩ Ici s = Icc s (s+1) := inter_eq_left.mpr (fun _ ht => ht.1)
  rw [he]
  simp [integral_const]
theorem kernel_nonnegative (s t : ℝ /- [definition] -/)
    : 0 ≤ compactKernel s t := by
  simp only [compactKernel,Set.indicator]; split_ifs <;> norm_num

/-- Every Volterra binder is simultaneously realized by a nonzero integral
kernel and the nonzero constant solution; all tail times are covered. This
probe is not a PII solution and is not evidence for the physical Airy bridge. -/
theorem cubic_volterra_all_binder_joint_probe :
    compactKernel 0 (1/2) ≠ 0 ∧
    ∃ u v g : ℝ → ℝ,
      u 0 ≠ 0 ∧ v 0 ≠ 0 ∧ (0:ℝ) ≤ 1/100 ∧
      (∀ t ≥ (0:ℝ), |u t| ≤ 2) ∧ (∀ t ≥ (0:ℝ), |v t| ≤ 2) ∧
      3*(2:ℝ)^2*(1/100)<1 ∧
      (∀ s ≥ (0:ℝ), IntegrableOn (compactKernel s) (Ici s)) ∧
      (∀ s ≥ (0:ℝ), IntegrableOn (fun t => compactKernel s t*(u t)^3) (Ici s)) ∧
      (∀ s ≥ (0:ℝ), IntegrableOn (fun t => compactKernel s t*(v t)^3) (Ici s)) ∧
      (∀ s ≥ (0:ℝ), (∫ t in Ici s, |compactKernel s t|) ≤ 1/100) ∧
      (∀ s ≥ (0:ℝ), u s=g s+∫ t in Ici s, compactKernel s t*(u t)^3) ∧
      (∀ s ≥ (0:ℝ), v s=g s+∫ t in Ici s, compactKernel s t*(v t)^3) ∧
      EqOn u v (Ici 0) := by
  have hk : ∀ s ≥ (0:ℝ), IntegrableOn (compactKernel s) (Ici s) :=
    fun s _ => (kernel_integrable s).integrableOn
  have hku : ∀ s ≥ (0:ℝ), IntegrableOn (fun t => compactKernel s t*(1:ℝ)^3) (Ici s) := by
    simpa only [one_pow,mul_one] using hk
  have hm : ∀ s ≥ (0:ℝ), (∫ t in Ici s, |compactKernel s t|) ≤ 1/100 := by
    intro s _
    simp only [abs_of_nonneg (kernel_nonnegative s _),kernel_integral]
    exact le_rfl
  have heq : ∀ s ≥ (0:ℝ), (1:ℝ)=(99/100:ℝ)+∫ t in Ici s,compactKernel s t*(1:ℝ)^3 := by
    intro s _
    rw [show (fun t => compactKernel s t*(1:ℝ)^3)=compactKernel s by funext t;ring,kernel_integral]
    norm_num
  have hb : ∀ t ≥ (0:ℝ), |(1:ℝ)| ≤ 2 := by intro t ht;norm_num
  refine ⟨?_,(fun _ => 1),(fun _ => 1),(fun _ => 99/100),by norm_num,by norm_num,
    by norm_num,hb,hb,by norm_num,hk,hku,hku,hm,heq,heq,?_⟩
  · norm_num [compactKernel,Set.indicator]
  · exact cubic_volterra_unique (fun _ => 1) (fun _ => 1) (fun _ => 99/100)
      compactKernel 0 2 (1/100) (by norm_num) hb hb (by norm_num) hk hku hku hm heq heq
end RMTFoundations.TracyWidom.HMVolterra

#print axioms RMTFoundations.TracyWidom.HMVolterra.pii_difference_factor
#print axioms RMTFoundations.TracyWidom.HMVolterra.cubic_divided_difference_nonneg
#print axioms RMTFoundations.TracyWidom.HMVolterra.cubic_lipschitz
#print axioms RMTFoundations.TracyWidom.HMVolterra.cubic_joint_probe
#print axioms RMTFoundations.TracyWidom.HMVolterra.cubic_volterra_unique
#print axioms RMTFoundations.TracyWidom.HMVolterra.compactKernel
#print axioms RMTFoundations.TracyWidom.HMVolterra.kernel_integrable
#print axioms RMTFoundations.TracyWidom.HMVolterra.kernel_integral
#print axioms RMTFoundations.TracyWidom.HMVolterra.kernel_nonnegative
#print axioms RMTFoundations.TracyWidom.HMVolterra.cubic_volterra_all_binder_joint_probe
