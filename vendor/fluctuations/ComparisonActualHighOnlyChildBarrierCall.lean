module

public import ComparisonActualHighOnlyMacroscopicEndpointCost
public import OmittedPathMovementGain
public import ComparisonNativeChildOptimizerMovement

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

structure ActualHighOnlyChildBarrierCall (n : ℕ) (delta : ℝ) where
  context : ActualHighOnlyComparisonData n delta
  lam : ℝ
  hlam : 0<lam
  hld : lam ≤ context.d^2
  optimizer : ActualHighOnlyComparisonMinimum context lam
  childData : ActualHighOnlyComparisonData n delta
  childLam : ℝ
  hchildLam : 0<childLam
  hchildLd : childLam ≤ childData.d^2
  childOptimizer : ActualHighOnlyComparisonMinimum childData childLam
  sameInitialMass : childData.s=context.s
  childBareMatrix : childData.b=fun u=>context.b u-context.coefficient optimizer.alpha lam u
  childBareField : childData.h=fun u=>context.h u+context.coefficient optimizer.alpha lam u*context.R optimizer.alpha u
  err : ℝ
  childSuccess : childData.objective childLam childOptimizer.alpha ≤
    realOrderedSKPathPressure n
      (fun u=>context.b u-context.coefficient optimizer.alpha lam u)
      (fun u=>context.h u+context.coefficient optimizer.alpha lam u*context.R optimizer.alpha u) 0+err

namespace ActualHighOnlyChildBarrierCall
variable {n : ℕ} {delta : ℝ} (a : ActualHighOnlyChildBarrierCall n delta)
abbrev alpha:=a.optimizer.alpha
abbrev R:=a.context.R a.alpha
abbrev Z:=a.childData.R a.childOptimizer.alpha
abbrev childRadius:=a.childData.d
abbrev e:=laplaceComparisonStrength a.context.d a.lam
abbrev D:=laplaceComparisonStrength a.childRadius a.childLam
abbrev coefficient:=a.context.coefficient a.alpha a.lam
abbrev childCoefficient:=a.childData.coefficient a.childOptimizer.alpha a.childLam

theorem high_coefficient {u : ℝ} (hu : a.context.s≤u) : a.coefficient u=a.e (a.R u) := by
  change omittedStrengthCoefficient a.context.d a.context.s a.R a.lam u=_
  rw [omittedStrengthCoefficient,ite_eq_left hu]

theorem high_child_coefficient {u : ℝ} (hu : a.context.s≤u) : a.childCoefficient u=a.D (a.Z u) := by
  change omittedStrengthCoefficient a.childData.d a.childData.s a.Z a.childLam u=_
  rw [a.sameInitialMass,omittedStrengthCoefficient,ite_eq_left hu]

theorem low_coefficients {u : ℝ} (hu : u<a.context.s) : a.coefficient u=0 ∧ a.childCoefficient u=0 := by
  change omittedStrengthCoefficient a.context.d a.context.s a.R a.lam u=0 ∧
    omittedStrengthCoefficient a.childData.d a.childData.s a.Z a.childLam u=0
  rw [a.sameInitialMass]
  simp only [omittedStrengthCoefficient,ite_eq_right (not_le.mpr hu)]
  trivial

theorem radius_continuous : Continuous a.R :=
  omittedSweepQuantile_continuous zero_le_one ⟨a.context.hs.1,a.context.hs1⟩
    a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha

theorem child_radius_continuous : Continuous a.Z :=
  omittedSweepQuantile_continuous zero_le_one ⟨a.childData.hs.1,a.childData.hs1⟩
    a.childData.hc a.childData.hk a.childData.hkc a.childData.hm a.childData.hM a.childOptimizer.alpha

theorem radius_bounds (u : ℝ) : a.R u∈Icc (0:ℝ) 1 :=
  omittedSweepQuantile_bounds zero_le_one ⟨a.context.hs.1,a.context.hs1⟩
    a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha u

theorem child_radius_bounds (u : ℝ) : a.Z u∈Icc (0:ℝ) 1 :=
  omittedSweepQuantile_bounds zero_le_one ⟨a.childData.hs.1,a.childData.hs1⟩
    a.childData.hc a.childData.hk a.childData.hkc a.childData.hm a.childData.hM a.childOptimizer.alpha u

theorem child_radius_monotone : Monotone a.Z :=
  omittedSweepQuantile_monotone zero_le_one ⟨a.childData.hs.1,a.childData.hs1⟩
    a.childData.hc a.childData.hk a.childData.hkc a.childData.hm a.childData.hM a.childOptimizer.alpha

theorem optimizer_movement_gain (gamma : a.context.Profile)
    (hgap : ∀u∈Icc a.context.s 1,a.context.R gamma u≠a.R u → a.Z u≠a.R u)
    (hfraction : ∀u∈Icc a.context.s 1,
      (a.context.R gamma u-a.R u)/(a.Z u-a.R u)∈Ico (0:ℝ)
        (a.D (a.Z u)/(a.e (a.R u)+a.D (a.Z u)))) :
    (∫u in (0:ℝ)..1,a.coefficient u*(a.context.R gamma u-a.R u)*(a.Z u-a.R u)) ≤ 4*a.err := by
  let Rhat:=a.context.R gamma
  let eh:=a.context.coefficient gamma a.lam
  let omega:=fun u=>(Rhat u-a.R u)/(a.Z u-a.R u)
  have Hhat:∀u∈Icc a.context.s 1,eh u=a.e (Rhat u):=by
    intro u hu
    change omittedStrengthCoefficient a.context.d a.context.s Rhat a.lam u=_
    rw [omittedStrengthCoefficient,ite_eq_left hu.1]
  have HRhat:Continuous Rhat:=omittedSweepQuantile_continuous zero_le_one
    ⟨a.context.hs.1,a.context.hs1⟩ a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM gamma
  have Hbefore:∀u∈Ico (0:ℝ) a.context.s,a.coefficient u=0 ∧ a.childCoefficient u=0 ∧ eh u=0:=by
    intro u hu
    refine ⟨(a.low_coefficients hu.2).1,(a.low_coefficients hu.2).2,?_⟩
    change omittedStrengthCoefficient a.context.d a.context.s Rhat a.lam u=0
    simp only [omittedStrengthCoefficient,ite_eq_right (not_le.mpr hu.2)]
  have He:∀u∈Icc a.context.s 1,0≤a.coefficient u:=fun u hu=>by
    rw [a.high_coefficient hu.1]
    exact (laplaceComparisonStrength_pos a.context.d a.hlam _).le
  have HD:∀u∈Icc a.context.s 1,0<a.childCoefficient u:=fun u hu=>by
    rw [a.high_child_coefficient hu.1]
    exact laplaceComparisonStrength_pos a.childRadius a.hchildLam _
  have Hfrac:∀u∈Icc a.context.s 1,omega u∈Ico (0:ℝ)
      (a.childCoefficient u/(a.coefficient u+a.childCoefficient u)):=by
    intro u hu
    rw [a.high_coefficient hu.1,a.high_child_coefficient hu.1]
    exact hfraction u hu
  have Hmove:∀u∈Icc a.context.s 1,Rhat u=a.R u+omega u*(a.Z u-a.R u):=by
    intro u hu
    by_cases he:Rhat u=a.R u
    · simp only [omega,he,sub_self,zero_div,zero_mul,add_zero]
    · have HZ:a.Z u-a.R u≠0:=sub_ne_zero.mpr (hgap u hu he)
      dsimp only [omega]
      rw [div_mul_cancel₀ _ HZ]
      ring
  have Hupper:∀u∈Icc a.context.s 1,eh u≤a.coefficient u/(1-omega u):=by
    intro u hu
    rw [Hhat u hu,a.high_coefficient hu.1]
    have Hratio:a.D (a.Z u)/(a.e (a.R u)+a.D (a.Z u))≤1:=
      (div_le_one₀ (add_pos (laplaceComparisonStrength_pos a.context.d a.hlam _)
        (laplaceComparisonStrength_pos a.childRadius a.hchildLam _))).mpr (by
          have HE:=laplaceComparisonStrength_pos a.context.d a.hlam (a.R u)
          linarith)
    exact comparison_movement_strength_upper a.e
      (fun q _=>(laplaceComparisonStrength_pos a.context.d a.hlam q).le)
      (laplaceComparisonStrength_monotonicities a.context.hd.ne' a.hlam (r₀:=0) le_rfl).1
      (by simpa only [mul_comm] using
        (laplaceComparisonStrength_monotonicities a.context.hd.ne' a.hlam (r₀:=0) le_rfl).2)
      (a.radius_bounds u) (a.child_radius_bounds u)
      ((a.context.radiusProfile gamma).property.1 u)
      ⟨(hfraction u hu).1,(hfraction u hu).2.trans_le Hratio⟩ (Hmove u hu)
  have Hec:ContinuousOn a.coefficient (Icc a.context.s 1):=by
    apply ((laplaceComparisonStrength_contDiff a.context.d a.lam).continuous.comp a.radius_continuous).continuousOn.congr
    intro u hu
    exact a.high_coefficient hu.1
  have HDc:ContinuousOn a.childCoefficient (Icc a.context.s 1):=by
    apply ((laplaceComparisonStrength_contDiff a.childRadius a.childLam).continuous.comp a.child_radius_continuous).continuousOn.congr
    intro u hu
    exact a.high_child_coefficient hu.1
  have Hhc:ContinuousOn eh (Icc a.context.s 1):=by
    apply ((laplaceComparisonStrength_contDiff a.context.d a.lam).continuous.comp HRhat).continuousOn.congr
    intro u hu
    exact Hhat u hu
  have HC:=a.childData.clocks_admissible a.childOptimizer.alpha ⟨a.hchildLam.le,a.hchildLd⟩
  rw [a.childBareMatrix,a.childBareField] at HC
  have HT:=a.context.clocks_admissible gamma ⟨a.hlam.le,a.hld⟩
  have HG:=actual_omitted_path_movement_gain n a.context.hn ⟨a.context.hs.1,a.context.hs1⟩
    a.context.b a.context.h a.coefficient a.R a.childCoefficient a.Z eh Rhat omega
    He HD (fun u hu=>(Hfrac u hu).1) (fun u hu=>(Hfrac u hu).2) Hupper Hmove
    Hec HDc Hhc a.radius_continuous.continuousOn a.child_radius_continuous.continuousOn
    HRhat.continuousOn Hbefore HC.1 HC.2.1 HT.1 HT.2.1
    (HC.2.2.1 0 ⟨le_rfl,zero_le_one⟩) (HC.2.2.2 0 ⟨le_rfl,zero_le_one⟩)
    (HT.2.2.1 0 ⟨le_rfl,zero_le_one⟩) (HT.2.2.2 0 ⟨le_rfl,zero_le_one⟩) 0
  have HM:=a.optimizer.minimum gamma
  have HS:=a.childSuccess
  change pathCompensatedPressure n a.childData.b a.childData.h a.childCoefficient a.Z 0≤_ at HS
  rw [a.childBareMatrix,a.childBareField] at HS
  change pathCompensatedPressure n a.context.b a.context.h a.coefficient a.R 0≤
    pathCompensatedPressure n a.context.b a.context.h eh Rhat 0 at HM
  change pathCompensatedPressure n (fun u=>a.context.b u-a.coefficient u)
    (fun u=>a.context.h u+a.coefficient u*a.R u) a.childCoefficient a.Z 0≤
    realOrderedSKPathPressure n (fun u=>a.context.b u-a.coefficient u)
      (fun u=>a.context.h u+a.coefficient u*a.R u) 0+a.err at HS
  linarith only [HG,HM,HS]

end ActualHighOnlyChildBarrierCall
end OAI.SKFluctuations.LaplaceWindowFormalization
