import RMTFoundations.TracyWidom.Airy2LimitLaws
import RMTFoundations.TracyWidom.Airy2LimitMarginals
import RMTFoundations.TracyWidom.Airy2Continuity
import RMTFoundations.TracyWidom.Airy2Removal
set_option autoImplicit false
namespace RMTFoundations.TracyWidom.Airy2LimitPhysical
open MeasureTheory Set Filter
open scoped Topology ENNReal
open RMTFoundations.TracyWidom.Airy2Probability
open RMTFoundations.TracyWidom.Airy2LimitLaws
open RMTFoundations.TracyWidom.Airy2LimitMarginals
open RMTFoundations.TracyWidom.Airy2RectangleLimits

/-- The actual determinant, with its real-valued CDF candidate. -/
noncomputable def physicalJointCandidate (m : ℕ /- [definition] -/)
    (times : Fin m → ℝ /- [definition] -/) (s : Fin m → ℝ /- [definition] -/) : ℝ :=
  (RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate m times s).re

theorem physicalJointCandidate_continuous (m : ℕ /- [definition] -/)
    (times : Fin m → ℝ /- [definition] -/) : Continuous (physicalJointCandidate m times) := by
  exact Complex.continuous_re.comp (RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_continuous_cuts m times)

/-- The full complex Fredholm candidate is real at its physical coupling;
its real CDF realization also realizes the literal determinant. -/
theorem physicalJointCandidate_coe (m : ℕ /- [definition] -/)
    (times s : Fin m → ℝ /- [definition] -/) :
    (physicalJointCandidate m times s : ℂ) = RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate m times s := by
  unfold physicalJointCandidate RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate
  rw [show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by norm_num,
    RMTFoundations.AiryKernel.kernelFredholm_real_coupling]
  simp

/-- CONDITIONAL physical limit theorem. The finite-N joint convergence binder
is explicit: the physical Dyson producer is not constructed in this module.
Marginal TW2 convergence gives genuine tightness internally. -/
theorem physical_joint_law_from_finite_limits (m : ℕ /- [definition] -/)
    (times : Fin m → ℝ /- [definition] -/)
    (htimes : StrictMono times /- [standing] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (hjoint : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop
      (𝓝 (physicalJointCandidate m times s)) /- [standing] -/)
    (hcoord : ∀ i s, Tendsto (fun n => (μ n : Measure (Fin m → ℝ)).real
      {x | x i ≤ s}) atTop (𝓝 (RMTFoundations.TracyWidom.TW2R s))
      /- [standing] -/) :
    ∃! ν : ProbabilityMeasure (Fin m → ℝ), ∀ s,
      jointCDF m ν s = physicalJointCandidate m times s := by
  exact finite_law_limit m μ (physicalJointCandidate m times)
    (fun _ => RMTFoundations.TracyWidom.TW2R) (physicalJointCandidate_continuous m times)
    hjoint hcoord (fun _ => RMTFoundations.TracyWidom.tendsto_TW2R_atBot)
    (fun _ => RMTFoundations.TracyWidom.tendsto_TW2R_atTop)

/-- The conditional construction gives a full weak limit and actual TW2 scalar
marginal measures. The finite joint-limit producer remains an explicit input. -/
theorem physical_joint_law_with_marginals (m : ℕ /- [definition] -/)
    (times : Fin m → ℝ /- [definition] -/)
    (htimes : StrictMono times /- [standing] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (hjoint : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop
      (𝓝 (physicalJointCandidate m times s)) /- [standing] -/)
    (hcoord : ∀ i s, Tendsto (fun n => (μ n : Measure (Fin m → ℝ)).real
      {x | x i ≤ s}) atTop (𝓝 (RMTFoundations.TracyWidom.TW2R s))
      /- [standing] -/) :
    ∃ ν : ProbabilityMeasure (Fin m → ℝ),
      (∀ s, jointCDF m ν s = physicalJointCandidate m times s) ∧
      Tendsto μ atTop (𝓝 ν) ∧
      (∀ i, (ν : Measure (Fin m → ℝ)).map (fun x => x i) = RMTFoundations.TracyWidom.TW2Measure) := by
  obtain ⟨ν,hν,hw,_⟩ := finite_law_limit_with_weak m μ (physicalJointCandidate m times)
    (fun _ => RMTFoundations.TracyWidom.TW2R) (physicalJointCandidate_continuous m times)
    hjoint hcoord (fun _ => RMTFoundations.TracyWidom.tendsto_TW2R_atBot)
    (fun _ => RMTFoundations.TracyWidom.tendsto_TW2R_atTop)
  exact ⟨ν,hν,hw,fun i => TW2_marginal_of_weak_limit m μ ν i hw (hcoord i)⟩

/-- The constructed law realizes the full complex determinant, not merely its
real part. Joint finite-ensemble convergence remains explicit. -/
theorem physical_fredholm_law_from_finite_limits (m : ℕ /- [definition] -/)
    (times : Fin m → ℝ /- [definition] -/)
    (htimes : StrictMono times /- [standing] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (hjoint : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop
      (𝓝 (physicalJointCandidate m times s)) /- [standing] -/)
    (hcoord : ∀ i s, Tendsto (fun n => (μ n : Measure (Fin m → ℝ)).real
      {x | x i ≤ s}) atTop (𝓝 (RMTFoundations.TracyWidom.TW2R s))
      /- [standing] -/) :
    ∃ ν : ProbabilityMeasure (Fin m → ℝ),
      (∀ s, (jointCDF m ν s : ℂ) = RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate m times s) ∧
      Tendsto μ atTop (𝓝 ν) ∧
      (∀ i, (ν : Measure (Fin m → ℝ)).map (fun x => x i) = RMTFoundations.TracyWidom.TW2Measure) := by
  obtain ⟨ν,hν,hw,hm⟩ := physical_joint_law_with_marginals m times htimes μ hjoint hcoord
  exact ⟨ν,fun s => by rw [hν s,physicalJointCandidate_coe],hw,hm⟩

/-- Literal finite-N coordinate consistency is inherited by the physical laws
constructed from both Fredholm limits. The physical producers are explicit inputs. -/
theorem physical_finite_limits_consistent (m n : ℕ /- [definition] -/)
    (times : Fin m → ℝ /- [definition] -/)
    (selectedTimes : Fin n → ℝ /- [definition] -/)
    (htimes : StrictMono times /- [standing] -/)
    (hselected : StrictMono selectedTimes /- [standing] -/)
    (f : Fin n → Fin m /- [definition] -/)
    (hsub : ∀ i, selectedTimes i = times (f i) /- [standing] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (η : ℕ → ProbabilityMeasure (Fin n → ℝ) /- [definition] -/)
    (hjoint : ∀ s, Tendsto (fun k => jointCDF m (μ k) s) atTop
      (𝓝 (physicalJointCandidate m times s)) /- [standing] -/)
    (hselectedJoint : ∀ s, Tendsto (fun k => jointCDF n (η k) s) atTop
      (𝓝 (physicalJointCandidate n selectedTimes s)) /- [standing] -/)
    (hcoord : ∀ i s, Tendsto (fun k => (μ k : Measure (Fin m → ℝ)).real
      {x | x i ≤ s}) atTop (𝓝 (RMTFoundations.TracyWidom.TW2R s)) /- [standing] -/)
    (hselectedCoord : ∀ i s, Tendsto (fun k => (η k : Measure (Fin n → ℝ)).real
      {x | x i ≤ s}) atTop (𝓝 (RMTFoundations.TracyWidom.TW2R s)) /- [standing] -/)
    (hfinite : ∀ k, (μ k : Measure (Fin m → ℝ)).map (fun x i => x (f i)) = η k
      /- [standing] -/) :
    ∃ ν : ProbabilityMeasure (Fin m → ℝ), ∃ ρ : ProbabilityMeasure (Fin n → ℝ),
      (∀ s, jointCDF m ν s = physicalJointCandidate m times s) ∧
      (∀ s, jointCDF n ρ s = physicalJointCandidate n selectedTimes s) ∧
      (ν : Measure (Fin m → ℝ)).map (fun x i => x (f i)) = ρ := by
  exact finite_law_limits_consistent m n μ η (physicalJointCandidate m times)
    (physicalJointCandidate n selectedTimes) (fun _ => RMTFoundations.TracyWidom.TW2R)
    (fun _ => RMTFoundations.TracyWidom.TW2R) f (physicalJointCandidate_continuous m times)
    (physicalJointCandidate_continuous n selectedTimes) hjoint hselectedJoint hcoord hselectedCoord
    (fun _ => RMTFoundations.TracyWidom.tendsto_TW2R_atBot)
    (fun _ => RMTFoundations.TracyWidom.tendsto_TW2R_atTop)
    (fun _ => RMTFoundations.TracyWidom.tendsto_TW2R_atBot)
    (fun _ => RMTFoundations.TracyWidom.tendsto_TW2R_atTop) hfinite

/-- Genuine CDF fields of the literal physical determinant follow from the
constructed limiting law, with the finite-ensemble dependency explicit. -/
theorem physical_cdf_fields_from_finite_limits (m : ℕ /- [definition] -/)
    (hm : 0 < m /- [standing] -/)
    (times : Fin m → ℝ /- [definition] -/)
    (htimes : StrictMono times /- [standing] -/)
    (μ : ℕ → ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (hjoint : ∀ s, Tendsto (fun n => jointCDF m (μ n) s) atTop
      (𝓝 (physicalJointCandidate m times s)) /- [standing] -/)
    (hcoord : ∀ i s, Tendsto (fun n => (μ n : Measure (Fin m → ℝ)).real
      {x | x i ≤ s}) atTop (𝓝 (RMTFoundations.TracyWidom.TW2R s))
      /- [standing] -/) :
    Monotone (physicalJointCandidate m times) ∧
    (∀ s, 0 ≤ physicalJointCandidate m times s ∧ physicalJointCandidate m times s ≤ 1) ∧
    Tendsto (fun a : ℝ => physicalJointCandidate m times (fun _ => a)) atTop (𝓝 1) ∧
    Tendsto (fun a : ℝ => physicalJointCandidate m times (fun _ => a)) atBot (𝓝 0) ∧
    (∀ l, l.Nodup → ∀ a b : Fin m → ℝ, (∀ i ∈ l, a i ≤ b i) →
      0 ≤ rectangleDifference m l (physicalJointCandidate m times) a b) := by
  obtain ⟨ν,hν,_⟩ := physical_joint_law_from_finite_limits m times htimes μ hjoint hcoord
  exact limit_cdf_fields m hm ν (physicalJointCandidate m times) hν

/-- Every individual coordinate is grounded for a genuine joint law. -/
theorem jointCDF_coordinate_atBot (m : ℕ /- [definition] -/)
    (ν : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (i : Fin m /- [definition] -/) (s : Fin m → ℝ /- [definition] -/) :
    Tendsto (fun a : ℝ => jointCDF m ν (Function.update s i a)) atBot (𝓝 0) := by
  classical
  have hm : Monotone (fun a : ℝ => lowerBox m (Function.update s i a)) := by
    intro a b hab
    apply lowerBox_mono
    intro j
    by_cases hj : j=i
    · subst j; simpa using hab
    · simp [Function.update_of_ne hj]
  have he : (⋂ a : ℝ, lowerBox m (Function.update s i a)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hh := (mem_iInter.mp hx (x i-1)) i
    simp only [Function.update_self] at hh
    linarith
  have ht := tendsto_measure_iInter_atBot (μ := (ν : Measure (Fin m → ℝ)))
    (fun a => (lowerBox_measurable m _).nullMeasurableSet) hm ⟨0,by finiteness⟩
  rw [he,measure_empty] at ht
  have hr := ENNReal.tendsto_toReal (by norm_num : (0 : ℝ≥0∞) ≠ ∞) |>.comp ht
  simpa [jointCDF,Measure.real,Function.comp_def] using hr

/-- Time translation identifies the actual laws through CDF uniqueness. -/
theorem physical_law_stationary (m : ℕ /- [definition] -/)
    (times : Fin m → ℝ /- [definition] -/) (c : ℝ /- [definition] -/)
    (ν ρ : ProbabilityMeasure (Fin m → ℝ) /- [definition] -/)
    (hν : ∀ s, jointCDF m ν s = physicalJointCandidate m times s /- [standing] -/)
    (hρ : ∀ s, jointCDF m ρ s = physicalJointCandidate m (fun i => times i+c) s
      /- [standing] -/) : ν = ρ := by
  apply Subtype.ext
  apply measure_eq_of_jointCDF m ν ρ ν.prop ρ.prop
  intro s
  rw [hν s,hρ s,physicalJointCandidate,physicalJointCandidate,
    RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate_time_translate]

/-- Full physical singleton example. This instantiates every convergence and tail
binder using the actual nonzero Airy kernel and its nondegenerate TW2 law.
It makes no claim about constructing finite-Dyson laws at distinct times. -/
theorem physical_limit_singleton_all_binder_joint_probe :
    RMTFoundations.Airy.airyAiReal 0 ≠ 0 ∧
    let μ : ℕ → ProbabilityMeasure (Fin 1 → ℝ) := fun _ =>
      ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩
    let times : Fin 1 → ℝ := fun _ => 0
    StrictMono times ∧
    (∀ s, Tendsto (fun n => jointCDF 1 (μ n) s) atTop
      (𝓝 (physicalJointCandidate 1 times s))) ∧
    (∀ i s, Tendsto (fun n => (μ n : Measure (Fin 1 → ℝ)).real {x | x i ≤ s}) atTop
      (𝓝 (RMTFoundations.TracyWidom.TW2R s))) ∧
    (∃! ν : ProbabilityMeasure (Fin 1 → ℝ), ∀ s, jointCDF 1 ν s =
      physicalJointCandidate 1 times s) ∧
    Continuous (physicalJointCandidate 1 times) ∧
    0 < physicalJointCandidate 1 times (fun _ => 0) ∧
    physicalJointCandidate 1 times (fun _ => 0) < 1 ∧
    Tendsto (fun a : ℝ => physicalJointCandidate 1 times (fun _ => a)) atTop (𝓝 1) ∧
    Tendsto (fun a : ℝ => physicalJointCandidate 1 times (fun _ => a)) atBot (𝓝 0) := by
  refine ⟨RMTFoundations.Airy.airyAiReal_zero_pos.ne',?_⟩
  dsimp only
  letI := TW2ProductLaw_probability 1
  let μ : ℕ → ProbabilityMeasure (Fin 1 → ℝ) := fun _ =>
    ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩
  let times : Fin 1 → ℝ := fun _ => 0
  have htimes : StrictMono times := by
    intro i j hij
    have heq : i=j := Subsingleton.elim _ _
    subst j
    exact False.elim ((lt_irrefl i) hij)
  have he : ∀ s, jointCDF 1 (TW2ProductLaw 1) s = physicalJointCandidate 1 times s := by
    intro s
    exact one_time_physical_law times s
  have hl : ∀ s, Tendsto (fun n => jointCDF 1 (μ n) s) atTop
      (𝓝 (physicalJointCandidate 1 times s)) := by
    intro s
    simpa only [μ,ProbabilityMeasure.coe_mk,he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => physicalJointCandidate 1 times s)
        atTop (𝓝 (physicalJointCandidate 1 times s)))
  have hc : ∀ i s, Tendsto (fun n => (μ n : Measure (Fin 1 → ℝ)).real {x | x i ≤ s}) atTop
      (𝓝 (RMTFoundations.TracyWidom.TW2R s)) := by
    intro i s
    have he' : (TW2ProductLaw 1).real {x | x i ≤ s} = RMTFoundations.TracyWidom.TW2R s :=
      TW2ProductLaw_coordinate_cdf 1 i s
    simpa only [μ,ProbabilityMeasure.coe_mk,he'] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => RMTFoundations.TracyWidom.TW2R s) atTop
        (𝓝 (RMTFoundations.TracyWidom.TW2R s)))
  have hp : ∀ s, physicalJointCandidate 1 times s = RMTFoundations.TracyWidom.TW2R (s 0) := by
    intro s
    rw [← he s,TW2ProductLaw_jointCDF]
    simp
  refine ⟨htimes,hl,hc,physical_joint_law_from_finite_limits 1 times htimes μ hl hc,
    physicalJointCandidate_continuous 1 times,?_,?_,?_,?_⟩
  · rw [hp]; exact RMTFoundations.TracyWidom.OrderTwoPositive.TW2R_positive 0
  · rw [hp]
    exact (RMTFoundations.TracyWidom.TW2R_strictMono (by norm_num : (0 : ℝ) < 1)).trans_le
      (RMTFoundations.TracyWidom.TW2R_bounds 1).2
  · change Tendsto (fun a : ℝ => physicalJointCandidate 1 times (fun _ => a)) atTop (𝓝 1)
    have hh : (fun a : ℝ => physicalJointCandidate 1 times (fun _ => a)) =
        RMTFoundations.TracyWidom.TW2R := funext (fun a => hp (fun _ => a))
    rw [hh]
    exact RMTFoundations.TracyWidom.tendsto_TW2R_atTop
  · change Tendsto (fun a : ℝ => physicalJointCandidate 1 times (fun _ => a)) atBot (𝓝 0)
    have hh : (fun a : ℝ => physicalJointCandidate 1 times (fun _ => a)) =
        RMTFoundations.TracyWidom.TW2R := funext (fun a => hp (fun _ => a))
    rw [hh]
    exact RMTFoundations.TracyWidom.tendsto_TW2R_atBot
/-- Full physical singleton fields apply the finite-limit CDF root with every
model, convergence and asymptotic premise supplied by compiled terms. -/
theorem physical_cdf_fields_singleton_all_binder_joint_probe :
    Monotone (physicalJointCandidate 1 (fun _ => 0)) ∧
    (∀ s, 0 ≤ physicalJointCandidate 1 (fun _ => 0) s ∧ physicalJointCandidate 1 (fun _ => 0) s ≤ 1) ∧
    Tendsto (fun a : ℝ => physicalJointCandidate 1 (fun _ => 0) (fun _ => a)) atTop (𝓝 1) ∧
    Tendsto (fun a : ℝ => physicalJointCandidate 1 (fun _ => 0) (fun _ => a)) atBot (𝓝 0) ∧
    (∀ l, l.Nodup → ∀ a b : Fin 1 → ℝ, (∀ i ∈ l, a i ≤ b i) →
      0 ≤ rectangleDifference 1 l (physicalJointCandidate 1 (fun _ => 0)) a b) := by
  have hp := physical_limit_singleton_all_binder_joint_probe
  dsimp only at hp
  exact physical_cdf_fields_from_finite_limits 1 (by norm_num) (fun _ => 0) hp.2.1
    (fun _ => ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩) hp.2.2.1 hp.2.2.2.1

/-- All weak-limit/marginal binders of the limit theorem are jointly
satisfied on actual one-time Airy/TW2 data, with all asymptotic inputs by terms. -/
theorem physical_marginals_singleton_all_binder_joint_probe :
    let μ : ℕ → ProbabilityMeasure (Fin 1 → ℝ) := fun _ =>
      ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩
    ∃ ν : ProbabilityMeasure (Fin 1 → ℝ),
      (∀ s, jointCDF 1 ν s = physicalJointCandidate 1 (fun _ => 0) s) ∧
      Tendsto μ atTop (𝓝 ν) ∧
      (∀ i, (ν : Measure (Fin 1 → ℝ)).map (fun x => x i) = RMTFoundations.TracyWidom.TW2Measure) := by
  dsimp only
  have hp := physical_limit_singleton_all_binder_joint_probe
  dsimp only at hp
  exact physical_joint_law_with_marginals 1 (fun _ => 0) hp.2.1
    (fun _ => ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩) hp.2.2.1 hp.2.2.2.1

/-- The literal determinant theorem has every finite-limit binder instantiated
by the complete physical singleton example. -/
theorem physical_fredholm_singleton_all_binder_joint_probe :
    let μ : ℕ → ProbabilityMeasure (Fin 1 → ℝ) := fun _ =>
      ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩
    ∃ ν : ProbabilityMeasure (Fin 1 → ℝ),
      (∀ s, (jointCDF 1 ν s : ℂ) = RMTFoundations.TracyWidom.Airy2.airy2FredholmCandidate 1 (fun _ => 0) s) ∧
      Tendsto μ atTop (𝓝 ν) ∧
      (∀ i, (ν : Measure (Fin 1 → ℝ)).map (fun x => x i) = RMTFoundations.TracyWidom.TW2Measure) := by
  dsimp only
  have hp := physical_limit_singleton_all_binder_joint_probe
  dsimp only at hp
  exact physical_fredholm_law_from_finite_limits 1 (fun _ => 0) hp.2.1
    (fun _ => ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩) hp.2.2.1 hp.2.2.2.1

/-- Both physical singleton producers and the exact coordinate map jointly
satisfy every consistency binder, including both complete marginal tails. -/
theorem physical_consistency_singleton_all_binder_joint_probe :
    ∃ ν : ProbabilityMeasure (Fin 1 → ℝ), ∃ ρ : ProbabilityMeasure (Fin 1 → ℝ),
      (∀ s, jointCDF 1 ν s = physicalJointCandidate 1 (fun _ => 0) s) ∧
      (∀ s, jointCDF 1 ρ s = physicalJointCandidate 1 (fun _ => 0) s) ∧
      (ν : Measure (Fin 1 → ℝ)).map (fun x => fun i : Fin 1 => x i) = ρ := by
  have hp := physical_limit_singleton_all_binder_joint_probe
  dsimp only at hp
  have hm : ∀ k : ℕ, (TW2ProductLaw 1).map (fun x => fun i : Fin 1 => x i) = TW2ProductLaw 1 := by
    intro k
    exact Measure.map_id
  exact physical_finite_limits_consistent 1 1 (fun _ => 0) (fun _ => 0) hp.2.1 hp.2.1
    (fun i => i) (fun _ => rfl)
    (fun _ => ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩)
    (fun _ => ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩)
    hp.2.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.1 hm

/-- Coordinate grounding and stationarity helper binders are jointly instantiated
on the physical singleton law, with a nonzero time shift. -/
theorem physical_transport_all_binder_joint_probe :
    let ν : ProbabilityMeasure (Fin 1 → ℝ) :=
      ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩
    (3 : ℝ) ≠ 0 ∧
    (∀ s, jointCDF 1 ν s = physicalJointCandidate 1 (fun _ => 0) s) ∧
    (∀ s, jointCDF 1 ν s = physicalJointCandidate 1 (fun _ => 0+3) s) ∧
    ν = ν ∧
    Tendsto (fun a : ℝ => jointCDF 1 ν
      (Function.update (fun _ : Fin 1 => -1) 0 a)) atBot (𝓝 0) := by
  dsimp only
  let ν : ProbabilityMeasure (Fin 1 → ℝ) :=
    ⟨TW2ProductLaw 1,TW2ProductLaw_probability 1⟩
  have hν : ∀ s, jointCDF 1 ν s = physicalJointCandidate 1 (fun _ => 0) s :=
    one_time_physical_law (fun _ => 0)
  have hρ : ∀ s, jointCDF 1 ν s = physicalJointCandidate 1 (fun _ => 0+3) s :=
    one_time_physical_law (fun _ => 0+3)
  exact ⟨by norm_num,hν,hρ,physical_law_stationary 1 (fun _ => 0) 3 ν ν hν hρ,
    jointCDF_coordinate_atBot 1 ν 0 (fun _ => -1)⟩
end RMTFoundations.TracyWidom.Airy2LimitPhysical

#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physicalJointCandidate
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physicalJointCandidate_continuous
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_joint_law_from_finite_limits
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.jointCDF_coordinate_atBot
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_law_stationary
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_limit_singleton_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_transport_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_cdf_fields_from_finite_limits
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_cdf_fields_singleton_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_joint_law_with_marginals
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_marginals_singleton_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physicalJointCandidate_coe
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_fredholm_law_from_finite_limits
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_finite_limits_consistent
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_fredholm_singleton_all_binder_joint_probe
#print axioms RMTFoundations.TracyWidom.Airy2LimitPhysical.physical_consistency_singleton_all_binder_joint_probe
