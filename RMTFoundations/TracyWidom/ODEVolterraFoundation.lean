import Mathlib
import RMTFoundations.TracyWidom.NormalizedODEFoundation
import RMTFoundations.TracyWidom.TriangleVolterraFoundation
import RMTFoundations.TracyWidom.ExponentialGreenFoundation
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.ODEVolterraFoundation
open MeasureTheory Set Filter
open scoped Topology
open RMTFoundations.TracyWidom.NormalizedODEFoundation RMTFoundations.TracyWidom.ExponentialGreenFoundation

/-- A normalized decaying ODE solution satisfies the genuine half-line
Volterra equation. Boundary terms and the actual Fubini integrability condition
are explicit; no comparison or Volterra equation is assumed. -/
theorem normalized_volterra_of_ode
    (y yp A Ap q ε : ℝ → ℝ /- [definition] -/)
    (s L : ℝ /- [definition] -/)
    (hy : ∀ t, HasDerivAt y (yp t) t /- [standing] -/)
    (hyp : ∀ t, HasDerivAt yp ((q t + ε t) * y t) t /- [standing] -/)
    (hA : ∀ t, HasDerivAt A (Ap t) t /- [standing] -/)
    (hAp : ∀ t, HasDerivAt Ap (q t * A t) t /- [standing] -/)
    (hAn : ∀ t, s ≤ t → A t ≠ 0 /- [standing] -/)
    (hsource : ∀ x, s ≤ x → IntegrableOn (fun t => ε t * A t * y t) (Ioi x) /- [standing] -/)
    (hflux : Tendsto (fun t => A t*yp t-Ap t*y t) atTop (𝓝 0) /- [standing] -/)
    (hrelative : Tendsto (fun t => y t/A t) atTop (𝓝 L) /- [standing] -/)
    (houter : ∀ x, s ≤ x → IntegrableOn
      (fun t => (A t*yp t-Ap t*y t)/(A t)^2) (Ioi x) /- [standing] -/)
    (hjoint : ∀ x, s ≤ x → Integrable
      (fun z : ℝ × ℝ => if z.1 < z.2 then ((A z.1)^2)⁻¹ * (ε z.2*A z.2*y z.2) else 0)
      ((volume.restrict (Ioi x)).prod (volume.restrict (Ioi x))) /- [standing] -/)
    (x : ℝ /- [definition] -/)
    (hx : s ≤ x /- [standing] -/) :
    y x/A x = L + ∫ t in Ioi x, normalizedGreen A x t * ε t * (y t/A t) := by
  have hin (t : ℝ) (ht : s ≤ t) : A t*yp t-Ap t*y t =
      -(∫ r in Ioi t, ε r*A r*y r) :=
    flux_tail_identity y yp A Ap q ε t hy hyp hA hAp (hsource t ht) hflux
  have H := relative_tail_identity y yp A Ap x L hy hA
    (fun t ht => hAn t (hx.trans ht)) (houter x hx) hrelative
  have ho : (∫ t in Ioi x, (A t*yp t-Ap t*y t)/(A t)^2) =
      -(∫ t in Ioi x, ∫ r in Ioi t, ((A t)^2)⁻¹*(ε r*A r*y r)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro t ht
    change (A t*yp t-Ap t*y t)/(A t)^2 =
      -(∫ r in Ioi t, ((A t)^2)⁻¹*(ε r*A r*y r))
    rw [hin t (hx.trans ht.le), integral_const_mul]
    simp only [div_eq_mul_inv]
    ring
  have hs := RMTFoundations.TracyWidom.TriangleVolterraFoundation.triangle_swap
    (fun t => ((A t)^2)⁻¹) (fun r => ε r*A r*y r) x (hjoint x hx)
  have he : (∫ r in Ioi x, (∫ t in x..r, ((A t)^2)⁻¹)*(ε r*A r*y r)) =
      ∫ r in Ioi x, normalizedGreen A x r*ε r*(y r/A r) := by
    apply integral_congr_ae
    apply ae_restrict_of_forall_mem measurableSet_Ioi
    intro r hr
    change (∫ t in x..r, ((A t)^2)⁻¹)*(ε r*A r*y r) =
      normalizedGreen A x r*ε r*(y r/A r)
    rw [normalizedGreen_factor]
    field_simp [hAn r (hx.trans hr.le)]
  rw [ho,hs,he,sub_neg_eq_add] at H
  exact H

/-- Nonzero decaying exponential reference jointly realizes every ODE,
boundary, improper-integral and two-dimensional-integrability binder. Separate
nonzero-forcing examples are supplied by NormalizedODEFoundation. -/
theorem ode_volterra_all_binder_joint_probe
    (x : ℝ /- [definition] -/)
    (hx : 0 ≤ x /- [standing] -/) :
    (Real.exp (-x))/Real.exp (-x) = 1 +
      ∫ t in Ioi x, normalizedGreen (fun r => Real.exp (-r)) x t * 0 *
        (Real.exp (-t)/Real.exp (-t)) := by
  let A : ℝ → ℝ := fun t => Real.exp (-t)
  let Ap : ℝ → ℝ := fun t => -A t
  have hA (t : ℝ) : HasDerivAt A (Ap t) t := by
    simpa [A,Ap] using ((hasDerivAt_id t).neg).exp
  have hAp (t : ℝ) : HasDerivAt Ap (1*A t) t := by
    convert! (hA t).neg using 1 <;> ring
  have hzero : (fun t => A t*Ap t-Ap t*A t) = (fun _ => (0 : ℝ)) := by
    ext t; ring
  have hzeroPoint (t : ℝ) : A t*Ap t-Ap t*A t = 0 := by ring
  have hone : (fun t => A t/A t) = (fun _ => (1 : ℝ)) := by
    ext t; exact div_self (ne_of_gt (Real.exp_pos _))
  have H := normalized_volterra_of_ode A Ap A Ap (fun _ => 1) (fun _ => 0) 0 1
    hA (by simpa using hAp) hA hAp
    (by intro t ht; exact ne_of_gt (Real.exp_pos _))
    (by intro t ht; simp only [zero_mul]; exact integrableOn_zero)
    (by rw [hzero]; exact tendsto_const_nhds)
    (by rw [hone]; exact tendsto_const_nhds)
    (by intro t ht; simp only [hzeroPoint,zero_div]; exact integrableOn_zero)
    (by intro t ht; simp only [zero_mul,mul_zero,ite_self]; exact integrable_zero _ _ _)
    x hx
  simpa [A] using H

end RMTFoundations.TracyWidom.ODEVolterraFoundation

#print axioms RMTFoundations.TracyWidom.ODEVolterraFoundation.normalized_volterra_of_ode
#print axioms RMTFoundations.TracyWidom.ODEVolterraFoundation.ode_volterra_all_binder_joint_probe
