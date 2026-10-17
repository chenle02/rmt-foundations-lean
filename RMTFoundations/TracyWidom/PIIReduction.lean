import Mathlib



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace RMTFoundations.TracyWidom

open Filter
open scoped Topology

/-- Differential algebra only: the TW first-order equations make the
quantity `u² - 2v - q²` stationary. No Airy-resolvent identification is assumed. -/
theorem hasDerivAt_tw_firstIntegral_zero
    (q p u v : ℝ → ℝ) -- [definition]
    (s : ℝ) -- [definition]
    (hq : HasDerivAt q (p s - u s * q s) s) -- [standing]
    (hu : HasDerivAt u (-(q s) ^ 2) s) -- [standing]
    (hv : HasDerivAt v (-(p s * q s)) s) -- [standing]
    : HasDerivAt (fun t => (u t) ^ 2 - 2 * v t - (q t) ^ 2) 0 s := by
  convert! ((hu.pow 2).fun_sub (hv.const_mul 2)).fun_sub (hq.pow 2) using 1 <;> ring

/-- At a single point, the first integral removes the two auxiliary functions
from the derivative of the first-order right-hand side. -/
theorem hasDerivAt_tw_painleve_rhs
    (q p u v : ℝ → ℝ) -- [definition]
    (s : ℝ) -- [definition]
    (hq : HasDerivAt q (p s - u s * q s) s) -- [standing]
    (hp : HasDerivAt p (s * q s + u s * p s - 2 * v s * q s) s) -- [standing]
    (hu : HasDerivAt u (-(q s) ^ 2) s) -- [standing]
    (hI : (u s) ^ 2 - 2 * v s = (q s) ^ 2) -- [standing]
    : HasDerivAt (fun t => p t - u t * q t)
        (s * q s + 2 * (q s) ^ 3) s := by
  have he : s * q s + u s * p s - 2 * v s * q s -
      (-(q s) ^ 2 * q s + u s * (p s - u s * q s)) =
      s * q s + 2 * (q s) ^ 3 := by
    linear_combination (q s) * hI
  simpa only [he] using hp.fun_sub (hu.fun_mul hq)

/-- A genuinely local first-order derivative identity yields the second
derivative required by Painleve II. The auxiliary equations are needed at `s`. -/
theorem hasDerivAt_deriv_tw_painleveII
    (q p u v : ℝ → ℝ) -- [definition]
    (s : ℝ) -- [definition]
    (hq : ∀ᶠ t in 𝓝 s, HasDerivAt q (p t - u t * q t) t) -- [standing]
    (hp : HasDerivAt p (s * q s + u s * p s - 2 * v s * q s) s) -- [standing]
    (hu : HasDerivAt u (-(q s) ^ 2) s) -- [standing]
    (hI : (u s) ^ 2 - 2 * v s = (q s) ^ 2) -- [standing]
    : HasDerivAt (deriv q) (s * q s + 2 * (q s) ^ 3) s := by
  have he : deriv q =ᶠ[𝓝 s] (fun t => p t - u t * q t) := by
    filter_upwards [hq] with t ht
    exact ht.deriv
  exact (hasDerivAt_tw_painleve_rhs q p u v s hq.self_of_nhds hp hu hI).congr_of_eventuallyEq he

/-- Pointwise Painleve II, conditional on the local TW system and first integral.
This does not assert existence, Hastings--McLeod asymptotics, or Fredholm equality. -/
theorem deriv_deriv_tw_painleveII
    (q p u v : ℝ → ℝ) -- [definition]
    (s : ℝ) -- [definition]
    (hq : ∀ᶠ t in 𝓝 s, HasDerivAt q (p t - u t * q t) t) -- [standing]
    (hp : HasDerivAt p (s * q s + u s * p s - 2 * v s * q s) s) -- [standing]
    (hu : HasDerivAt u (-(q s) ^ 2) s) -- [standing]
    (hI : (u s) ^ 2 - 2 * v s = (q s) ^ 2) -- [standing]
    : deriv (deriv q) s = s * q s + 2 * (q s) ^ 3 :=
  (hasDerivAt_deriv_tw_painleveII q p u v s hq hp hu hI).deriv

/-- Polynomial point jets for the joint probe; they are not global PII solutions. -/
def twPIIProbeQ
    (t : ℝ) -- [definition]
    : ℝ := 1 + t + t ^ 2

def twPIIProbeU
    (t : ℝ) -- [definition]
    : ℝ := -t

def twPIIProbeP
    (t : ℝ) -- [definition]
    : ℝ := 1 + 2 * t + twPIIProbeU t * twPIIProbeQ t

noncomputable def twPIIProbeV
    (t : ℝ) -- [definition]
    : ℝ := -(1 / 2 : ℝ) - t

theorem hasDerivAt_twPIIProbeQ
    (t : ℝ) -- [definition]
    : HasDerivAt twPIIProbeQ (1 + 2 * t) t := by
  convert! ((hasDerivAt_const t (1 : ℝ)).fun_add (hasDerivAt_id t)).fun_add
    ((hasDerivAt_id t).pow 2) using 1 <;> norm_num [twPIIProbeQ] <;> ring

/-- All binders of the conditional PII and stationary-invariant theorems are
simultaneously satisfied at one nondegenerate point: `q(0)=q'(0)=1`. The first
equation holds on a neighborhood; the remaining equations hold at the point.
The probe asserts no global solution of the full TW system. -/
theorem tw_painleveII_all_binders_joint_probe
    : ∃ (q p u v : ℝ → ℝ) (s : ℝ),
        q s ≠ 0 ∧ deriv q s ≠ 0 ∧
        (∀ᶠ t in 𝓝 s, HasDerivAt q (p t - u t * q t) t) ∧
        HasDerivAt q (p s - u s * q s) s ∧
        HasDerivAt p (s * q s + u s * p s - 2 * v s * q s) s ∧
        HasDerivAt u (-(q s) ^ 2) s ∧
        HasDerivAt v (-(p s * q s)) s ∧
        (u s) ^ 2 - 2 * v s = (q s) ^ 2 := by
  have hq (t : ℝ) : HasDerivAt twPIIProbeQ
      (twPIIProbeP t - twPIIProbeU t * twPIIProbeQ t) t := by
    simpa only [twPIIProbeP, add_sub_cancel_right] using hasDerivAt_twPIIProbeQ t
  have hu : HasDerivAt twPIIProbeU (-(twPIIProbeQ 0) ^ 2) 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).fun_neg using 1 <;>
      norm_num [twPIIProbeU, twPIIProbeQ]
  have hp : HasDerivAt twPIIProbeP
      (0 * twPIIProbeQ 0 + twPIIProbeU 0 * twPIIProbeP 0 -
        2 * twPIIProbeV 0 * twPIIProbeQ 0) 0 := by
    convert! ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_add
      ((hasDerivAt_id (0 : ℝ)).const_mul 2)).fun_add
      (((hasDerivAt_id (0 : ℝ)).fun_neg).fun_mul (hasDerivAt_twPIIProbeQ 0)) using 1 <;>
      norm_num [twPIIProbeP, twPIIProbeU, twPIIProbeQ, twPIIProbeV]
  have hv : HasDerivAt twPIIProbeV
      (-(twPIIProbeP 0 * twPIIProbeQ 0)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) (-(1 / 2 : ℝ))).fun_sub
      (hasDerivAt_id (0 : ℝ)) using 1 <;>
      norm_num [twPIIProbeV, twPIIProbeP, twPIIProbeU, twPIIProbeQ]
  refine ⟨twPIIProbeQ, twPIIProbeP, twPIIProbeU, twPIIProbeV, 0,
    ?_, ?_, Filter.Eventually.of_forall hq, hq 0, hp, hu, hv, ?_⟩
  · norm_num [twPIIProbeQ]
  · rw [(hasDerivAt_twPIIProbeQ 0).deriv]
    norm_num
  · norm_num [twPIIProbeU, twPIIProbeV, twPIIProbeQ]

end RMTFoundations.TracyWidom

#print axioms RMTFoundations.TracyWidom.hasDerivAt_tw_firstIntegral_zero
#print axioms RMTFoundations.TracyWidom.hasDerivAt_tw_painleve_rhs
#print axioms RMTFoundations.TracyWidom.hasDerivAt_deriv_tw_painleveII
#print axioms RMTFoundations.TracyWidom.deriv_deriv_tw_painleveII
#print axioms RMTFoundations.TracyWidom.twPIIProbeQ
#print axioms RMTFoundations.TracyWidom.twPIIProbeU
#print axioms RMTFoundations.TracyWidom.twPIIProbeP
#print axioms RMTFoundations.TracyWidom.twPIIProbeV
#print axioms RMTFoundations.TracyWidom.hasDerivAt_twPIIProbeQ
#print axioms RMTFoundations.TracyWidom.tw_painleveII_all_binders_joint_probe
