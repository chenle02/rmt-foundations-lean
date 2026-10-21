import Mathlib
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.NormalizedODEFoundation
open MeasureTheory Set Filter
open scoped Topology

/-- Relative derivative expressed through the literal Wronskian flux. -/
theorem relative_derivative
    (y yp A Ap : ℝ → ℝ /- [definition] -/)
    (x : ℝ /- [definition] -/)
    (hy : HasDerivAt y (yp x) x /- [standing] -/)
    (hA : HasDerivAt A (Ap x) x /- [standing] -/)
    (hAn : A x ≠ 0 /- [standing] -/) :
    HasDerivAt (fun t => y t / A t)
      ((A x * yp x - Ap x * y x) / (A x)^2) x := by
  convert! hy.div hA hAn using 1 <;> ring

/-- Perturbed and reference ODEs produce the exact flux source. -/
theorem flux_derivative
    (y yp A Ap q ε : ℝ → ℝ /- [definition] -/)
    (x : ℝ /- [definition] -/)
    (hy : HasDerivAt y (yp x) x /- [standing] -/)
    (hyp : HasDerivAt yp ((q x + ε x) * y x) x /- [standing] -/)
    (hA : HasDerivAt A (Ap x) x /- [standing] -/)
    (hAp : HasDerivAt Ap (q x * A x) x /- [standing] -/) :
    HasDerivAt (fun t => A t * yp t - Ap t * y t)
      (ε x * A x * y x) x := by
  convert! ((hA.mul hyp).sub (hAp.mul hy)) using 1 <;> ring

/-- Boundary flux zero at infinity gives the exact inner tail integral. -/
theorem flux_tail_identity
    (y yp A Ap q ε : ℝ → ℝ /- [definition] -/)
    (s : ℝ /- [definition] -/)
    (hy : ∀ t, HasDerivAt y (yp t) t /- [standing] -/)
    (hyp : ∀ t, HasDerivAt yp ((q t + ε t) * y t) t /- [standing] -/)
    (hA : ∀ t, HasDerivAt A (Ap t) t /- [standing] -/)
    (hAp : ∀ t, HasDerivAt Ap (q t * A t) t /- [standing] -/)
    (hint : IntegrableOn (fun t => ε t * A t * y t) (Ioi s) /- [standing] -/)
    (hboundary : Tendsto (fun t => A t * yp t - Ap t * y t) atTop (𝓝 0) /- [standing] -/) :
    A s * yp s - Ap s * y s = -(∫ t in Ioi s, ε t * A t * y t) := by
  have hd (t : ℝ) := flux_derivative y yp A Ap q ε t (hy t) (hyp t) (hA t) (hAp t)
  have H := integral_Ioi_of_hasDerivAt_of_tendsto
    ((hd s).continuousAt.continuousWithinAt) (fun t _ => hd t) hint hboundary
  linarith

/-- The normalized boundary value gives the exact outer tail integral.
Together with flux_tail_identity this is the nested Volterra equation,
with both improper-integral boundary terms discharged. -/
theorem relative_tail_identity
    (y yp A Ap : ℝ → ℝ /- [definition] -/)
    (s L : ℝ /- [definition] -/)
    (hy : ∀ t, HasDerivAt y (yp t) t /- [standing] -/)
    (hA : ∀ t, HasDerivAt A (Ap t) t /- [standing] -/)
    (hAn : ∀ t, s ≤ t → A t ≠ 0 /- [standing] -/)
    (hint : IntegrableOn (fun t => (A t * yp t - Ap t * y t) / (A t)^2)
      (Ioi s) /- [standing] -/)
    (hboundary : Tendsto (fun t => y t / A t) atTop (𝓝 L) /- [standing] -/) :
    y s / A s = L - ∫ t in Ioi s, (A t * yp t - Ap t * y t) / (A t)^2 := by
  have hd (t : ℝ) (ht : s ≤ t) := relative_derivative y yp A Ap t (hy t) (hA t) (hAn t ht)
  have H := integral_Ioi_of_hasDerivAt_of_tendsto
    ((hd s le_rfl).continuousAt.continuousWithinAt)
    (fun t ht => hd t ht.le) hint hboundary
  linarith

/-- Nonzero decaying reference and nonzero exponentially decaying perturbation
jointly realize the relative and flux derivative hypotheses. -/
theorem derivative_all_binder_joint_probe (x : ℝ /- [definition] -/) :
    HasDerivAt (fun t : ℝ => 1 + Real.exp (-t) / 8)
      (-Real.exp (-x) / 8) x ∧
    HasDerivAt (fun t : ℝ => -Real.exp (-3 * t) / 8)
      (3 * Real.exp (-3 * x) / 8) x := by
  constructor
  · convert! ((((hasDerivAt_id x).neg).exp).div_const 8).const_add 1 using 1 <;>
      (try simp only [Pi.sub_apply,Pi.neg_apply,id_eq]) <;> ring
  · convert! ((((hasDerivAt_id x).const_mul (-3)).exp).neg).div_const 8 using 1 <;>
      (try simp only [Pi.sub_apply,Pi.neg_apply,id_eq]) <;> ring

/-- Full inner-tail witness: A=exp(-t), y=exp(-t)+exp(-2t)/8,
q=1, epsilon=(3 exp(-2t)/8)/y. The perturbation is strictly positive. -/
theorem flux_all_binder_joint_probe (s : ℝ /- [definition] -/) :
    ∃ y yp A Ap q ε : ℝ → ℝ,
      (∀ t, HasDerivAt y (yp t) t) ∧
      (∀ t, HasDerivAt yp ((q t + ε t) * y t) t) ∧
      (∀ t, HasDerivAt A (Ap t) t) ∧
      (∀ t, HasDerivAt Ap (q t * A t) t) ∧
      IntegrableOn (fun t => ε t * A t * y t) (Ioi s) ∧
      Tendsto (fun t => A t * yp t - Ap t * y t) atTop (𝓝 0) ∧
      (∀ t, 0 < A t ∧ 0 < y t ∧ 0 < ε t) := by
  let A : ℝ → ℝ := fun t => Real.exp (-t)
  let B : ℝ → ℝ := fun t => Real.exp (-2*t) / 8
  let y : ℝ → ℝ := fun t => A t + B t
  let yp : ℝ → ℝ := fun t => -A t - 2*B t
  let Ap : ℝ → ℝ := fun t => -A t
  let ε : ℝ → ℝ := fun t => 3*B t/y t
  have hAd (t : ℝ) : HasDerivAt A (-A t) t := by
    simpa [A] using ((hasDerivAt_id t).neg).exp
  have hBd (t : ℝ) : HasDerivAt B (-2*B t) t := by
    convert! (((hasDerivAt_id t).const_mul (-2)).exp).div_const 8 using 1 <;>
      simp only [B,id_eq] <;> ring
  have hyn (t : ℝ) : 0 < y t := by dsimp [y,A,B]; positivity
  have hsource (t : ℝ) : ε t * A t * y t = 3 / 8 * Real.exp (-3*t) := by
    dsimp [ε, B, A]
    field_simp [ne_of_gt (hyn t)]
    rw [← Real.exp_add]
    congr 1 <;> ring
  have hflux (t : ℝ) : A t * yp t - Ap t * y t = -Real.exp (-3*t) / 8 := by
    dsimp [A,yp,Ap,y,B]
    have he : Real.exp (-t) * Real.exp (-2*t) = Real.exp (-3*t) := by
      rw [← Real.exp_add]; congr 1; ring
    nlinarith [he]
  refine ⟨y,yp,A,Ap,(fun _ => 1),ε,?_,?_,?_,?_,?_,?_,?_⟩
  · intro t; convert! (hAd t).add (hBd t) using 1 <;> ring
  · intro t
    convert! (hAd t).neg.sub ((hBd t).const_mul 2) using 1
    (try dsimp [yp,ε,y])
    have hn : A t + B t ≠ 0 := ne_of_gt (hyn t)
    field_simp [hn]
    ring
  · exact hAd
  · intro t; convert! (hAd t).neg using 1 <;> ring
  · have H : IntegrableOn (fun t : ℝ => Real.exp (-3*t)) (Ioi s) :=
      integrableOn_exp_mul_Ioi (by norm_num : (-3:ℝ)<0) s
    exact (H.const_mul (3/8)).congr (Eventually.of_forall fun t => (hsource t).symm)
  · have H := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_mul_const (by norm_num : (0:ℝ)<3))
    convert! H.neg.div_const 8 using 1
    · funext t; simpa [Function.comp_def,id_eq,mul_comm] using hflux t
    · simp
  · intro t; dsimp [A,y,B,ε]; exact ⟨by positivity, by positivity, by positivity⟩

/-- Explicit outer-tail witness has normalized limit one and nonzero flux,
so the boundary and integrability premises are simultaneously satisfiable. -/
theorem relative_all_binder_joint_probe
    (s : ℝ /- [definition] -/) :
    ∃ y yp A Ap : ℝ → ℝ,
      (∀ t, HasDerivAt y (yp t) t) ∧
      (∀ t, HasDerivAt A (Ap t) t) ∧
      (∀ t, s ≤ t → A t ≠ 0) ∧
      IntegrableOn (fun t => (A t * yp t - Ap t * y t) / (A t)^2) (Ioi s) ∧
      Tendsto (fun t => y t/A t) atTop (𝓝 1) ∧
      y s / A s = 1 - ∫ t in Ioi s, (A t * yp t - Ap t * y t) / (A t)^2 := by
  let A : ℝ → ℝ := fun t => Real.exp (-t)
  let u : ℝ → ℝ := fun t => 1 + Real.exp (-t) / 8
  let Ap : ℝ → ℝ := fun t => -A t
  let up : ℝ → ℝ := fun t => -A t / 8
  let y : ℝ → ℝ := fun t => A t*u t
  let yp : ℝ → ℝ := fun t => Ap t*u t+A t*up t
  have hdA (t : ℝ) : HasDerivAt A (Ap t) t := by
    simpa [A,Ap] using ((hasDerivAt_id t).neg).exp
  have hdu (t : ℝ) : HasDerivAt u (up t) t := by
    convert! ((hdA t).div_const 8).const_add 1 using 1 <;> ring
  have hdy (t : ℝ) : HasDerivAt y (yp t) t := (hdA t).mul (hdu t)
  have hn (t : ℝ) : A t ≠ 0 := by exact ne_of_gt (Real.exp_pos _)
  have hnorm (t : ℝ) : y t/A t=u t := by dsimp [y]; field_simp [hn t]
  have hflux (t : ℝ) : (A t*yp t-Ap t*y t)/(A t)^2 = -Real.exp (-t)/8 := by
    dsimp [yp,y,up]; field_simp [hn t]; ring
  have hint : IntegrableOn (fun t => (A t*yp t-Ap t*y t)/(A t)^2) (Ioi s) := by
    have H := (integrableOn_exp_neg_Ioi s).neg.div_const (8 : ℝ)
    exact H.congr (Eventually.of_forall fun t => (hflux t).symm)
  have hlim : Tendsto (fun t => y t/A t) atTop (𝓝 1) := by
    have H := Real.tendsto_exp_neg_atTop_nhds_zero.div_const 8
    convert! H.const_add 1 using 1
    · funext t; exact hnorm t
    · simp
  have hAn : ∀ t, s ≤ t → A t ≠ 0 := fun t _ => hn t
  refine ⟨y,yp,A,Ap,hdy,hdA,hAn,hint,hlim,?_⟩
  exact relative_tail_identity y yp A Ap s 1 hdy hdA hAn hint hlim

end RMTFoundations.TracyWidom.NormalizedODEFoundation

#print axioms RMTFoundations.TracyWidom.NormalizedODEFoundation.relative_derivative
#print axioms RMTFoundations.TracyWidom.NormalizedODEFoundation.flux_derivative
#print axioms RMTFoundations.TracyWidom.NormalizedODEFoundation.flux_tail_identity
#print axioms RMTFoundations.TracyWidom.NormalizedODEFoundation.relative_tail_identity
#print axioms RMTFoundations.TracyWidom.NormalizedODEFoundation.derivative_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.NormalizedODEFoundation.flux_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.NormalizedODEFoundation.relative_all_binder_joint_probe
