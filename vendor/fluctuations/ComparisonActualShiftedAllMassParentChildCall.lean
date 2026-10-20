module

public import ComparisonActualShiftedParentAllMassMovement

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 14000000

structure ActualShiftedAllMassParentChildCall (n : ℕ) (delta : ℝ) where
  context : ActualShiftedParentData n delta
  optimizer : ActualShiftedParentMinimum context
  childData : NativeChildBarrierParameters n delta
  childLam : ℝ
  hchildLam : 0 < childLam
  hchildLd : childLam ≤ childData.d^2
  childAlpha : childData.Profile
  matrixRoom : childLam ≤ context.b 0-context.coefficient optimizer.alpha 0
  attained : variableEndpointComparisonSweepObjective childData.hc childData.hk childData.hkc childData.hm childData.hM n
      (fun u=>context.b u-context.coefficient optimizer.alpha u)
      (fun u=>context.h u+context.coefficient optimizer.alpha u*context.R optimizer.alpha u)
      childData.d childLam childAlpha=
    variableEndpointComparisonSweepMinimum childData.hc childData.hk childData.hkc childData.hm childData.hM n
      (fun u=>context.b u-context.coefficient optimizer.alpha u)
      (fun u=>context.h u+context.coefficient optimizer.alpha u*context.R optimizer.alpha u)
      childData.d childLam

namespace ActualShiftedAllMassParentChildCall
variable {n : ℕ} {delta : ℝ} (a : ActualShiftedAllMassParentChildCall n delta)
abbrev lam:=a.context.lam
abbrev hlam:=a.context.hlam
abbrev hld:=a.context.hld
abbrev alpha:=a.optimizer.alpha
abbrev R:=a.context.R a.alpha
abbrev Z:=a.childData.R a.childAlpha
abbrev childRadius:=a.childData.d
abbrev e:=laplaceComparisonStrength a.context.d a.lam
abbrev D:=laplaceComparisonStrength a.childRadius a.childLam
abbrev coefficient:=a.context.coefficient a.alpha
abbrev err:=variableEndpointComparisonSweepCost a.childData.hc a.childData.hk a.childData.hkc a.childData.hm a.childData.hM n
  (fun u=>a.context.b u-a.coefficient u)
  (fun u=>a.context.h u+a.coefficient u*a.R u) a.childRadius a.childLam

theorem high_coefficient {u : ℝ} (hu : a.context.s≤u) : a.coefficient u=a.e (a.R u) := by
  change omittedStrengthCoefficient a.context.d a.context.s a.R a.lam u=_
  rw [omittedStrengthCoefficient,ite_eq_left hu]

theorem low_coefficient {u : ℝ} (hu : u<a.context.s) : a.coefficient u=0 := by
  change omittedStrengthCoefficient a.context.d a.context.s a.R a.lam u=0
  simp only [omittedStrengthCoefficient,ite_eq_right (not_le.mpr hu)]

theorem radius_continuous : Continuous a.R :=
  omittedSweepQuantile_continuous a.context.hr1 a.context.hs
    a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha

theorem child_radius_continuous : Continuous a.Z :=
  comparisonSweepQuantile_continuous a.childData.hc a.childData.hk a.childData.hkc a.childData.hm a.childData.hM a.childAlpha

theorem radius_bounds (u : ℝ) : a.R u∈Icc (0:ℝ) 1 :=
  (Icc_subset_Icc a.context.hr0 le_rfl)
    (omittedSweepQuantile_bounds a.context.hr1 a.context.hs a.context.hc a.context.hk a.context.hkc a.context.hm a.context.hM a.alpha u)

theorem child_radius_bounds (u : ℝ) : a.Z u∈Icc (0:ℝ) 1 :=
  comparisonSweepQuantile_bounds a.childData.hc a.childData.hk a.childData.hkc a.childData.hm a.childData.hM a.childAlpha u

theorem child_radius_monotone : Monotone a.Z :=
  comparisonSweepQuantile_monotone a.childData.hc a.childData.hk a.childData.hkc a.childData.hm a.childData.hM a.childAlpha

theorem optimizer_movement_gain (gamma : a.context.Profile)
    (hgap : ∀u∈Icc a.context.s 1,a.context.R gamma u≠a.R u → a.Z u≠a.R u)
    (hfraction : ∀u∈Icc a.context.s 1,
      (a.context.R gamma u-a.R u)/(a.Z u-a.R u)∈Ico (0:ℝ)
        (a.D (a.Z u)/(a.e (a.R u)+a.D (a.Z u)))) :
    (∫u in (0:ℝ)..1,a.coefficient u*(a.context.R gamma u-a.R u)*(a.Z u-a.R u)) ≤ 4*a.err :=
  a.context.optimizer_all_mass_child_movement_gain a.optimizer a.childData a.childAlpha
    a.hchildLam a.matrixRoom a.attained gamma hgap hfraction

end ActualShiftedAllMassParentChildCall
end OAI.SKFluctuations.LaplaceWindowFormalization
