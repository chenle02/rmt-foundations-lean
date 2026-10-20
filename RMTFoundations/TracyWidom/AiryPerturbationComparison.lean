import Mathlib
import RMTFoundations.TracyWidom.AiryGreenKernelFoundation
import RMTFoundations.TracyWidom.PerturbationBudgetFoundation
import RMTFoundations.TracyWidom.ODEVolterraFoundation
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.AiryPerturbationComparison
open MeasureTheory Set Filter Real
open scoped Topology
open RMTFoundations.Airy RMTFoundations.TracyWidom.AiryGreenKernelFoundation

/-- Actual L1 tail budget supplied by a sup-amplitude and an integrable envelope. -/
noncomputable def tailBudget
    (s η : ℝ /- [definition] -/)
    (b : ℝ → ℝ /- [definition] -/) : ℝ :=
  (1 / (2 * sqrt s)) * η * ∫ t in Ioi s, b t

/-- Quantitative weighted comparison for the actual Ai Volterra operator. -/
theorem ai_volterra_error
    (s η : ℝ /- [definition] -/)
    (b ε y : ℝ → ℝ /- [definition] -/)
    (hs : 0 < s /- [standing] -/)
    (hη : 0 ≤ η /- [standing] -/)
    (hb : IntegrableOn b (Ioi s) /- [standing] -/)
    (hbn : ∀ t, s ≤ t → 0 ≤ b t /- [standing] -/)
    (hε : ∀ t, s ≤ t → |ε t| ≤ η*b t /- [standing] -/)
    (hbdd : BddAbove ((fun t => |y t/airyAiReal t|) '' Ici s) /- [standing] -/)
    (hsol : ∀ x, s ≤ x → y x/airyAiReal x = 1 +
      ∫ t in Ioi s, halflineKernel x t*ε t*(y t/airyAiReal t) /- [standing] -/)
    (hsmall : tailBudget s η b < 1 /- [standing] -/) :
    ∀ x, s ≤ x →
      |y x/airyAiReal x-1| ≤ tailBudget s η b/(1-tailBudget s η b) ∧
      |y x-airyAiReal x| ≤ (tailBudget s η b/(1-tailBudget s η b))*airyAiReal x := by
  have H := RMTFoundations.TracyWidom.PerturbationBudgetFoundation.amplitude_tail_bound
    (volume.restrict (Ioi s)) (Ici s) b ε (fun t => y t/airyAiReal t)
    halflineKernel (1/(2*sqrt s)) η
    ⟨s,(by change s ≤ s; exact le_rfl)⟩
    (ae_restrict_of_forall_mem measurableSet_Ioi (by
      intro t ht; change s ≤ t; exact (show s < t from ht).le))
    (by positivity) hη hb hbn hε
    (fun x hx t ht => halflineKernel_bound s x t hs hx ht)
    (by simpa [Function.comp_def] using hbdd) hsol hsmall
  intro x hx
  have Hr : |y x/airyAiReal x-1| ≤ tailBudget s η b/(1-tailBudget s η b) := H x hx
  have hA : 0 < airyAiReal x := airyAiReal_pos_of_nonneg (hs.le.trans hx)
  refine ⟨Hr,?_⟩
  have he : y x-airyAiReal x = (y x/airyAiReal x-1)*airyAiReal x := by
    field_simp [ne_of_gt hA]
  rw [he,abs_mul,abs_of_pos hA]
  exact mul_le_mul_of_nonneg_right Hr hA.le

/-- Perturbed Airy ODE to an explicit weighted half-line comparison. All source,
boundary and Fubini hypotheses concern the literal ODE solution. The actual Ai
ODE and kernel facts are discharged by the Airy foundations. -/
theorem ai_ode_comparison
    (s η : ℝ /- [definition] -/)
    (b ε y yp : ℝ → ℝ /- [definition] -/)
    (hs : 0 < s /- [standing] -/)
    (hη : 0 ≤ η /- [standing] -/)
    (hy : ∀ t, HasDerivAt y (yp t) t /- [standing] -/)
    (hyp : ∀ t, HasDerivAt yp ((t+ε t)*y t) t /- [standing] -/)
    (hb : IntegrableOn b (Ioi s) /- [standing] -/)
    (hbn : ∀ t, s ≤ t → 0 ≤ b t /- [standing] -/)
    (hε : ∀ t, s ≤ t → |ε t| ≤ η*b t /- [standing] -/)
    (hbdd : BddAbove ((fun t => |y t/airyAiReal t|) '' Ici s) /- [standing] -/)
    (hsource : ∀ x, s ≤ x → IntegrableOn (fun t => ε t*airyAiReal t*y t) (Ioi x) /- [standing] -/)
    (hflux : Tendsto (fun t => airyAiReal t*yp t-deriv airyAiReal t*y t) atTop (𝓝 0) /- [standing] -/)
    (hrelative : Tendsto (fun t => y t/airyAiReal t) atTop (𝓝 1) /- [standing] -/)
    (houter : ∀ x, s ≤ x → IntegrableOn
      (fun t => (airyAiReal t*yp t-deriv airyAiReal t*y t)/(airyAiReal t)^2) (Ioi x) /- [standing] -/)
    (hjoint : ∀ x, s ≤ x → Integrable
      (fun z : ℝ × ℝ => if z.1 < z.2 then ((airyAiReal z.1)^2)⁻¹ *
        (ε z.2*airyAiReal z.2*y z.2) else 0)
      ((volume.restrict (Ioi x)).prod (volume.restrict (Ioi x))) /- [standing] -/)
    (hsmall : tailBudget s η b < 1 /- [standing] -/) :
    ∀ x, s ≤ x →
      |y x/airyAiReal x-1| ≤ tailBudget s η b/(1-tailBudget s η b) ∧
      |y x-airyAiReal x| ≤ (tailBudget s η b/(1-tailBudget s η b))*airyAiReal x := by
  have H := RMTFoundations.TracyWidom.ODEVolterraFoundation.normalized_volterra_of_ode y yp airyAiReal
    (deriv airyAiReal) id ε s 1 hy hyp hasDerivAt_airyAiReal' hasDerivAt_deriv_airyAiReal'
    (fun t ht => ne_of_gt (airyAiReal_pos_of_nonneg (hs.le.trans ht)))
    hsource hflux hrelative houter hjoint
  apply ai_volterra_error s η b ε y hs hη hb hbn hε hbdd
  · intro x hx
    have Hx := H x hx
    rw [← fixed_domain_integral s x ε (fun t => y t/airyAiReal t) hx] at Hx
    exact Hx
  · exact hsmall




theorem actual_airy_all_binder_joint_probe
    (x : ℝ /- [definition] -/)
    (hx : 1 ≤ x /- [standing] -/) :
    |airyAiReal x/airyAiReal x-1| ≤ 0 ∧ |airyAiReal x-airyAiReal x| ≤ 0 := by
  have hzero (t : ℝ) : airyAiReal t*deriv airyAiReal t-deriv airyAiReal t*airyAiReal t=0 := by ring
  have hz : (fun t => airyAiReal t*deriv airyAiReal t-deriv airyAiReal t*airyAiReal t) =
      (fun _ => (0 : ℝ)) := by ext t; exact hzero t
  have hlim : Tendsto (fun t => airyAiReal t/airyAiReal t) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    exact (div_self (ne_of_gt (airyAiReal_pos_of_nonneg (zero_le_one.trans ht)))).symm
  have H := ai_ode_comparison 1 0 (fun t => exp (-t)) (fun _ => 0)
    airyAiReal (deriv airyAiReal) (by norm_num) (by norm_num)
    hasDerivAt_airyAiReal' (by simpa using hasDerivAt_deriv_airyAiReal')
    (integrableOn_exp_neg_Ioi 1) (fun t ht => (exp_pos _).le)
    (by intros; simp)
    (by refine ⟨1,?_⟩; rintro z ⟨t,ht,rfl⟩
        change |airyAiReal t/airyAiReal t| ≤ 1
        simp only [div_self (ne_of_gt (airyAiReal_pos_of_nonneg (zero_le_one.trans ht))),abs_one,le_refl])
    (by intros; simp only [zero_mul]; exact integrableOn_zero)
    (by rw [hz]; exact tendsto_const_nhds) hlim
    (by intros; simp only [hzero,zero_div]; exact integrableOn_zero)
    (by intros; simp only [zero_mul,mul_zero,ite_self]; exact integrable_zero _ _ _)
    (by simp [tailBudget])
  simpa [tailBudget] using H x hx

/-- Zero coefficient error permits a distinct amplitude without normalization. -/
theorem amplitude_counterinstance :
    (∀ t : ℝ, HasDerivAt (fun x => 2 * airyAiReal x) (2 * deriv airyAiReal t) t) ∧
    (∀ t : ℝ, HasDerivAt (fun x => 2 * deriv airyAiReal x) (t * (2 * airyAiReal t)) t) ∧
    (∀ t : ℝ, 0 ≤ t → (2 * airyAiReal t) / airyAiReal t = 2) ∧
    (2 * airyAiReal 0) / airyAiReal 0 ≠ 1 := by
  refine ⟨?_,?_,?_,?_⟩
  · intro t; exact (hasDerivAt_airyAiReal' t).const_mul 2
  · intro t; convert! (hasDerivAt_deriv_airyAiReal' t).const_mul 2 using 1 <;> ring
  · intro t ht; field_simp [ne_of_gt (airyAiReal_pos_of_nonneg ht)]
  · have h : (2 * airyAiReal 0) / airyAiReal 0 = 2 := by field_simp [ne_of_gt airyAiReal_zero_pos]
    rw [h]; norm_num

end RMTFoundations.TracyWidom.AiryPerturbationComparison

#print axioms RMTFoundations.TracyWidom.AiryPerturbationComparison.tailBudget
#print axioms RMTFoundations.TracyWidom.AiryPerturbationComparison.ai_volterra_error
#print axioms RMTFoundations.TracyWidom.AiryPerturbationComparison.ai_ode_comparison
#print axioms RMTFoundations.TracyWidom.AiryPerturbationComparison.actual_airy_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.AiryPerturbationComparison.amplitude_counterinstance
