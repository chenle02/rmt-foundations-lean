import Mathlib



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom

/-- Scalar resolvent-kernel differentiation from actual derivative data. Only
the derivative action on `y s` and one selfadjoint pairing are needed. This
lemma does not identify any of its arguments with Airy/Fredholm objects. -/
theorem hasDerivAt_scalar_resolvent_kernel
    {E : Type*} -- [definition]
    [NormedAddCommGroup E] -- [standing]
    [InnerProductSpace ℝ E] -- [standing]
    (k : ℝ → ℝ) -- [definition]
    (x y : ℝ → E) -- [definition]
    (T : ℝ → E →L[ℝ] E) -- [definition]
    (U : E →L[ℝ] E) -- [definition]
    (s a b : ℝ) -- [definition]
    (z Q : E) -- [definition]
    (hk : HasDerivAt k (-(a * b)) s) -- [standing]
    (hx : HasDerivAt x ((-a) • z) s) -- [standing]
    (hy : HasDerivAt y ((-b) • z) s) -- [standing]
    (hT : HasDerivAt T U s) -- [standing]
    (hUy : U (y s) = (-(inner ℝ Q (y s))) • Q) -- [standing]
    (hTz : T s z = Q) -- [standing]
    (hpair : inner ℝ z (T s (y s)) = inner ℝ (T s z) (y s)) -- [standing]
    : HasDerivAt (fun t => k t + inner ℝ (x t) (T t (y t)))
        (-((a + inner ℝ (x s) Q) * (b + inner ℝ (y s) Q))) s := by
  have hTy := hT.clm_apply hy
  have hd := hk.fun_add (HasDerivAt.inner ℝ hx hTy)
  apply hd.congr_deriv
  rw [hUy, map_smul, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_smul_left, hpair, hTz,
    real_inner_comm (y s) Q]
  ring

/-- The derivative-value form of the preceding conditional calculus lemma. -/
theorem deriv_scalar_resolvent_kernel
    {E : Type*} -- [definition]
    [NormedAddCommGroup E] -- [standing]
    [InnerProductSpace ℝ E] -- [standing]
    (k : ℝ → ℝ) -- [definition]
    (x y : ℝ → E) -- [definition]
    (T : ℝ → E →L[ℝ] E) -- [definition]
    (U : E →L[ℝ] E) -- [definition]
    (s a b : ℝ) -- [definition]
    (z Q : E) -- [definition]
    (hk : HasDerivAt k (-(a * b)) s) -- [standing]
    (hx : HasDerivAt x ((-a) • z) s) -- [standing]
    (hy : HasDerivAt y ((-b) • z) s) -- [standing]
    (hT : HasDerivAt T U s) -- [standing]
    (hUy : U (y s) = (-(inner ℝ Q (y s))) • Q) -- [standing]
    (hTz : T s z = Q) -- [standing]
    (hpair : inner ℝ z (T s (y s)) = inner ℝ (T s z) (y s)) -- [standing]
    : deriv (fun t => k t + inner ℝ (x t) (T t (y t))) s =
        -((a + inner ℝ (x s) Q) * (b + inner ℝ (y s) Q)) :=
  (hasDerivAt_scalar_resolvent_kernel k x y T U s a b z Q
    hk hx hy hT hUy hTz hpair).deriv

def scalarResolventProbeK
    (t : ℝ) -- [definition]
    : ℝ := 5 - 2 * t

def scalarResolventProbeX
    (t : ℝ) -- [definition]
    : ℝ := 3 - t

def scalarResolventProbeY
    (t : ℝ) -- [definition]
    : ℝ := 4 - 2 * t

noncomputable def scalarResolventProbeT
    (t : ℝ) -- [definition]
    : ℝ →L[ℝ] ℝ := (2 - 4 * t) • ContinuousLinearMap.id ℝ ℝ

noncomputable def scalarResolventProbeU
    : ℝ →L[ℝ] ℝ := (-4 : ℝ) • ContinuousLinearMap.id ℝ ℝ

/-- Every calculus/algebra binder is jointly satisfied at a nonzero scalar
point jet. The curves are genuine affine/polynomial curves; they do not
describe an Airy kernel or an inverse family on a neighborhood. -/
theorem scalar_resolvent_kernel_all_binders_joint_probe
    : ∃ (k x y : ℝ → ℝ) (T : ℝ → ℝ →L[ℝ] ℝ)
        (U : ℝ →L[ℝ] ℝ) (s a b z Q : ℝ),
        k s ≠ 0 ∧ x s ≠ 0 ∧ y s ≠ 0 ∧ z ≠ 0 ∧ Q ≠ 0 ∧
        a ≠ 0 ∧ b ≠ 0 ∧ U (y s) ≠ 0 ∧
        HasDerivAt k (-(a * b)) s ∧
        HasDerivAt x ((-a) • z) s ∧
        HasDerivAt y ((-b) • z) s ∧
        HasDerivAt T U s ∧
        U (y s) = (-(inner ℝ Q (y s))) • Q ∧
        T s z = Q ∧
        inner ℝ z (T s (y s)) = inner ℝ (T s z) (y s) ∧
        HasDerivAt (fun t => k t + inner ℝ (x t) (T t (y t))) (-70) s := by
  have hk : HasDerivAt scalarResolventProbeK (-(1 * 2)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (5 : ℝ)).fun_sub
      ((hasDerivAt_id (0 : ℝ)).const_mul 2) using 1 <;>
      norm_num [scalarResolventProbeK]
  have hx : HasDerivAt scalarResolventProbeX ((-1 : ℝ) • (1 : ℝ)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (3 : ℝ)).fun_sub
      (hasDerivAt_id (0 : ℝ)) using 1 <;> norm_num [scalarResolventProbeX]
  have hy : HasDerivAt scalarResolventProbeY ((-2 : ℝ) • (1 : ℝ)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (4 : ℝ)).fun_sub
      ((hasDerivAt_id (0 : ℝ)).const_mul 2) using 1 <;>
      norm_num [scalarResolventProbeY]
  have hT : HasDerivAt scalarResolventProbeT scalarResolventProbeU 0 := by
    convert! ((hasDerivAt_const (0 : ℝ) (2 : ℝ)).fun_sub
      ((hasDerivAt_id (0 : ℝ)).const_mul 4)).smul_const
      (ContinuousLinearMap.id ℝ ℝ) using 1 <;>
      norm_num [scalarResolventProbeT, scalarResolventProbeU, neg_smul]
    ext q
    norm_num [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hUy : scalarResolventProbeU (scalarResolventProbeY 0) =
      (-(inner ℝ (2 : ℝ) (scalarResolventProbeY 0))) • (2 : ℝ) := by
    norm_num [scalarResolventProbeU, scalarResolventProbeY,
      ContinuousLinearMap.smul_apply, Real.inner_apply, smul_eq_mul]
  have hTz : scalarResolventProbeT 0 (1 : ℝ) = (2 : ℝ) := by
    norm_num [scalarResolventProbeT, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hpair : inner ℝ (1 : ℝ) (scalarResolventProbeT 0 (scalarResolventProbeY 0)) =
      inner ℝ (scalarResolventProbeT 0 (1 : ℝ)) (scalarResolventProbeY 0) := by
    norm_num [scalarResolventProbeT, scalarResolventProbeY,
      ContinuousLinearMap.smul_apply, Real.inner_apply, smul_eq_mul]
  have hd := hasDerivAt_scalar_resolvent_kernel scalarResolventProbeK
    scalarResolventProbeX scalarResolventProbeY scalarResolventProbeT
    scalarResolventProbeU 0 1 2 1 2 hk hx hy hT hUy hTz hpair
  refine ⟨scalarResolventProbeK, scalarResolventProbeX, scalarResolventProbeY,
    scalarResolventProbeT, scalarResolventProbeU, 0, 1, 2, 1, 2,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hk, hx, hy, hT, hUy, hTz, hpair, ?_⟩
  all_goals norm_num [scalarResolventProbeK, scalarResolventProbeX,
    scalarResolventProbeY, scalarResolventProbeU, ContinuousLinearMap.smul_apply,
    Real.inner_apply, smul_eq_mul] at *
  exact hd

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.hasDerivAt_scalar_resolvent_kernel
#print axioms RMTFoundations.TracyWidom.deriv_scalar_resolvent_kernel
#print axioms RMTFoundations.TracyWidom.scalarResolventProbeK
#print axioms RMTFoundations.TracyWidom.scalarResolventProbeX
#print axioms RMTFoundations.TracyWidom.scalarResolventProbeY
#print axioms RMTFoundations.TracyWidom.scalarResolventProbeT
#print axioms RMTFoundations.TracyWidom.scalarResolventProbeU
#print axioms RMTFoundations.TracyWidom.scalar_resolvent_kernel_all_binders_joint_probe
