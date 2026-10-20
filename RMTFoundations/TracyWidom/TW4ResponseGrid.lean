import RMTFoundations.TracyWidom.TW4ResponseDerivative
import RMTFoundations.TracyWidom.TW4GridCertificate
import RMTFoundations.TracyWidom.TW4EasySign
import RMTFoundations.TracyWidom.PhysicalPainleveII
set_option autoImplicit false
namespace RMTFoundations.TracyWidom
open Set Filter
open scoped Topology
open RMTFoundations.TWOneBounds RMTFoundations.TracyWidom.ResolventCoordinates
open RMTFoundations.TracyWidom.PhysicalPainleveII RMTFoundations.TracyWidom.OrderTwoLogDerivative

/-- The normalized sign has a genuinely continuous derivative on the whole line. -/
theorem TW4Response_deriv_continuous : Continuous (deriv TW4Response) := by
  rw [show deriv TW4Response = fun s =>
    -(resolventQ s)^2-
      (RMTFoundations.TracyWidom.EndpointCalculus.resolventP s-resolventU s*resolventQ s)*
        Real.tanh (TWEndpointTail s/2)+
      (resolventQ s)^2/(2*(Real.cosh (TWEndpointTail s/2))^2) from
    funext fun s => (TW4Response_hasDerivAt s).deriv]
  have hq := resolventQ_continuous_for_TW4
  have hu := resolventU_continuous
  have hp : Continuous RMTFoundations.TracyWidom.EndpointCalculus.resolventP :=
    (show Differentiable ℝ RMTFoundations.TracyWidom.EndpointCalculus.resolventP from
      fun s => (hasDerivAt_resolventP s).differentiableAt).continuous
  have ht : Continuous (fun s => TWEndpointTail s/2) :=
    (continuous_iff_continuousAt.mpr fun s => (TWEndpointTail_hasDerivAt s).continuousAt).div_const 2
  have hc := Real.continuous_cosh.comp ht
  have hs := Real.continuous_sinh.comp ht
  have hm : Continuous (fun s => Real.tanh (TWEndpointTail s/2)) := by
    simp_rw [Real.tanh_eq_sinh_div_cosh]
    exact hs.div hc (fun s => (Real.cosh_pos _).ne')
  exact ((hq.pow 2).neg.sub ((hp.sub (hu.mul hq)).mul hm)).add
    ((hq.pow 2).div (continuous_const.mul (hc.pow 2))
      (fun s => mul_ne_zero (by norm_num) (pow_ne_zero 2 (Real.cosh_pos _).ne')))

theorem TW4Response_contDiff_one : ContDiff ℝ 1 TW4Response := by
  apply contDiff_one_iff_deriv.mpr
  exact ⟨fun s => (TW4Response_hasDerivAt s).differentiableAt,TW4Response_deriv_continuous⟩

/-- A physical finite-grid certificate with a derivative bound yields a positive
GSE density throughout the covered window. Grid bounds must be proved by the caller. -/
theorem TW4_density_positive_of_grid_certificate
    (ι : Type*) -- [definition]
    [Fintype ι] -- [definition]
    (grid : ι → ℝ) -- [definition]
    (a b radius L margin : ℝ) -- [definition]
    (hL : 0 ≤ L) -- [standing]
    (hsites : ∀ i, grid i ∈ Icc a b) -- [standing]
    (hcover : ∀ x ∈ Icc a b, ∃ i, |x-grid i| ≤ radius) -- [standing]
    (hderiv : ∀ x ∈ Icc a b, |deriv TW4Response x| ≤ L) -- [standing]
    (hgrid : ∀ i, margin ≤ TW4Response (grid i)) -- [standing]
    (hbudget : L*radius < margin) -- [standing]
    : ∀ s ∈ Icc a b, 0 < TW4AirySlope s := by
  have hv : ∀ x ∈ Icc a b, ∀ i,
      |TW4Response x-TW4Response (grid i)| ≤ L*|x-grid i| := by
    intro x hx i
    have h := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun y _ => (TW4Response_hasDerivAt y).differentiableAt)
      (fun y hy => by simpa only [Real.norm_eq_abs] using hderiv y hy)
      (convex_Icc a b) (hsites i) hx
    simpa only [Real.norm_eq_abs] using h
  have hp := finite_grid_positive_of_margin ι TW4Response grid a b radius L margin
    hL hcover hv hgrid hbudget
  exact fun s hs => (TW4AirySlope_positive_iff_response s).mpr (hp s hs)

/-- The actual model supplies every grid-certificate binder jointly on a genuine
nondegenerate compact window. This existential window is not a certificate for [-6,6]. -/
theorem physical_GSE_grid_all_binder_joint_probe :
    ∃ (grid : Fin 1 → ℝ) (a b radius L margin : ℝ),
      a < b ∧ 0 < radius ∧ 0 < L ∧ 0 < margin ∧
      (∀ i, grid i ∈ Icc a b) ∧
      (∀ x ∈ Icc a b, ∃ i, |x-grid i| ≤ radius) ∧
      (∀ x ∈ Icc a b, |deriv TW4Response x| ≤ L) ∧
      (∀ i, margin ≤ TW4Response (grid i)) ∧ L*radius < margin ∧
      (∀ s ∈ Icc a b, 0 < TW4AirySlope s) := by
  obtain ⟨z,hz,hqu⟩ := exists_physical_endpoint_lt_diagonal
  have hsign : 0 < TW4Response z := (TW4AirySlope_positive_iff_response z).mp
    (TW4AirySlope_positive_of_q_le_u z hqu.le)
  obtain ⟨M,hM⟩ := (show IsCompact (Icc (z-1) (z+1)) from isCompact_Icc).bddAbove_image
    TW4Response_deriv_continuous.abs.continuousOn
  have hMz : |deriv TW4Response z| ≤ M := hM ⟨z,by constructor <;> linarith,rfl⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hMz
  let L := M+1
  let margin := TW4Response z
  let radius := min 1 (margin/(2*L))
  let grid : Fin 1 → ℝ := fun _ => z
  have hLp : 0 < L := by dsimp [L]; linarith
  have hrp : 0 < radius := lt_min (by norm_num)
    (div_pos hsign (mul_pos (by norm_num) hLp))
  have hr1 : radius ≤ 1 := min_le_left _ _
  have hrm : radius ≤ margin/(2*L) := min_le_right _ _
  have hbudget : L*radius < margin := by
    have h := (le_div_iff₀ (mul_pos (by norm_num : (0:ℝ)<2) hLp)).mp hrm
    dsimp [margin] at h ⊢
    nlinarith
  have hsites : ∀ i, grid i ∈ Icc (z-radius) (z+radius) := by
    intro i
    dsimp [grid]
    constructor <;> linarith
  have hcover : ∀ x ∈ Icc (z-radius) (z+radius), ∃ i, |x-grid i| ≤ radius := by
    intro x hx
    refine ⟨0,?_⟩
    dsimp [grid]
    rw [abs_le]
    constructor <;> linarith [hx.1,hx.2]
  have hderiv : ∀ x ∈ Icc (z-radius) (z+radius), |deriv TW4Response x| ≤ L := by
    intro x hx
    have hx' : x ∈ Icc (z-1) (z+1) := by constructor <;> linarith [hx.1,hx.2]
    have hb : |deriv TW4Response x| ≤ M := hM ⟨x,hx',rfl⟩
    dsimp [L]
    linarith
  have hgrid : ∀ i, margin ≤ TW4Response (grid i) := by intro i; exact le_rfl
  exact ⟨grid,z-radius,z+radius,radius,L,margin,by linarith,hrp,hLp,hsign,
    hsites,hcover,hderiv,hgrid,hbudget,
    TW4_density_positive_of_grid_certificate (Fin 1) grid (z-radius) (z+radius)
      radius L margin hLp.le hsites hcover hderiv hgrid hbudget⟩
end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.TW4Response_deriv_continuous
#print axioms RMTFoundations.TracyWidom.TW4Response_contDiff_one
#print axioms RMTFoundations.TracyWidom.TW4_density_positive_of_grid_certificate
#print axioms RMTFoundations.TracyWidom.physical_GSE_grid_all_binder_joint_probe
