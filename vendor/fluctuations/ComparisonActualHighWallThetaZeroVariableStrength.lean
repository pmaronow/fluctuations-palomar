module

public import ComparisonActualHighWallThetaZeroCapLiftTrial
public import ComparisonActualHighWallShiftedParentData

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighWallData
variable {n:ℕ} {delta:ℝ} (a:ActualHighWallData n delta)

def thetaZeroHighOnlyData : ActualHighOnlyComparisonData n delta where
  E:=a.E
  d:=a.d
  s:=a.s
  b:=wallBareMatrix a.T a.epsilon 0 a.s
  h:=fun _=>0
  hn:=a.hn
  hE:=a.hE
  hd:=a.hd
  hs:=⟨a.hs.1.le,a.hs.2.trans (by norm_num)⟩
  hq:=a.hq
  hb:=by
    intro u hu v hv huv
    simp only [wallBareMatrix,zero_mul,sub_zero]
    by_cases hsU:u<a.s <;> by_cases hsV:v<a.s <;> simp only [hsU,hsV,ite_true,ite_false]
    · exact le_rfl
    · linarith [a.hepsilon.1]
    · exact False.elim (hsU (huv.trans_lt hsV))
    · exact le_rfl
  hh:=by intro u hu v hv huv;exact le_rfl
  hb0:=by
    simp only [wallBareMatrix,ite_eq_left a.hs.1,zero_mul,sub_zero]
    linarith [a.hepsilon.2]
  hh0:=le_rfl
  hcut:=by
    simp only [wallBareMatrix,ite_eq_right (lt_irrefl a.s),zero_mul,sub_zero]
    exact a.hdepsilon.trans a.hepsilon.2.le
  hcross:=by
    intro u hu
    simp only [wallBareMatrix,ite_eq_left hu.2,ite_eq_right (lt_irrefl a.s),zero_mul,sub_zero]
    linarith [a.hdepsilon]

def thetaZeroShiftedParentData (lam:ℝ) (hlam:0 < lam) (hld:lam ≤ a.d^2) : ActualShiftedParentData n delta where
  numerics:={E:=a.E,d:=a.d,hn:=a.hn,hE:=a.hE,hd:=a.hd}
  r0:=a.rmin
  s:=a.s
  hr0:=a.hrbounds.1.le
  hr1:=a.hr
  hs:=⟨a.hs.1.le,a.hs1⟩
  lam:=lam
  hlam:=hlam
  hld:=hld
  b:=a.thetaZeroHighOnlyData.b
  h:=a.thetaZeroHighOnlyData.h
  clockAdmissible:=by
    intro alpha
    let R:=omittedSweepQuantile a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha
    have H:=omittedStrengthSweep_clocks_admissible a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h R
      ⟨a.hs.1.le,a.hs1⟩ a.hd.ne' hlam.le (hld.trans a.thetaZeroHighOnlyData.hcut)
      (fun u hu=>by
        have Hcross:=a.thetaZeroHighOnlyData.hcross u hu
        change a.thetaZeroHighOnlyData.b u+a.d^2 ≤ a.thetaZeroHighOnlyData.b a.s at Hcross
        linarith only [Hcross,hld])
      a.thetaZeroHighOnlyData.hb a.thetaZeroHighOnlyData.hb0 a.thetaZeroHighOnlyData.hh a.thetaZeroHighOnlyData.hh0
      ((omittedSweepQuantile_monotone a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha).monotoneOn _)
      (fun u _=>⟨a.hrbounds.1.le.trans (omittedSweepQuantile_bounds a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha u).1,
        (omittedSweepQuantile_bounds a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM alpha u).2⟩)
    exact H

theorem theta_zero_shifted_minimum_attained (lam:ℝ) (hlam:0 < lam) (hld:lam ≤ a.d^2) :
    Nonempty (ActualShiftedParentMinimum (a.thetaZeroShiftedParentData lam hlam hld)) := by
  obtain ⟨alpha,hatt,Hmin⟩:=omittedComparisonSweepMinimum_attained a.hrbounds.1.le a.hr ⟨a.hs.1.le,a.hs1⟩
    a.hc a.hk a.hkc a.hm a.hM n a.hn a.thetaZeroHighOnlyData.b a.thetaZeroHighOnlyData.h a.hd.ne' hlam.le
    (hld.trans a.thetaZeroHighOnlyData.hcut)
    (fun u hu=>by
        have Hcross:=a.thetaZeroHighOnlyData.hcross u hu
        change a.thetaZeroHighOnlyData.b u+a.d^2 ≤ a.thetaZeroHighOnlyData.b a.s at Hcross
        linarith only [Hcross,hld])
    a.thetaZeroHighOnlyData.hb a.thetaZeroHighOnlyData.hb0 a.thetaZeroHighOnlyData.hh a.thetaZeroHighOnlyData.hh0
    (concreteWallCap_continuous _ _ _ _)
    (concreteWallConstraints_nonempty a.hN a.hE a.hd a.hd1
      ⟨a.hs.1.le,a.hs.2.trans (by norm_num)⟩ a.hq a.hsmall)
  refine ⟨⟨alpha,?_⟩⟩
  intro gamma
  have H:=Hmin gamma
  rw [←hatt] at H
  exact H

def thetaZeroCapLiftPressurePad (lam:ℝ) (hlam:0 < lam) (hld:lam ≤ a.d^2)
    (alpha:a.zeroOriginProfile) (gamma:a.Profile) : ℝ :=
  (a.thetaZeroShiftedParentData lam hlam hld).objective gamma-
    a.thetaZeroHighOnlyData.objective lam alpha

theorem theta_zero_actual_minimum_le_cap_lift_with_literal_pad
    (lam:ℝ) (hlam:0 < lam) (hld:lam ≤ a.d^2)
    (P:ActualShiftedParentMinimum (a.thetaZeroShiftedParentData lam hlam hld))
    (Q:ActualHighOnlyComparisonMinimum a.thetaZeroHighOnlyData lam) :
    ∃gamma:a.Profile,(∀u∈Icc a.s 1,
      gamma.val.val (a.capLiftRadius Q.alpha u)=u ∧
      0 ≤ a.capLiftRadius Q.alpha u-a.zeroOriginRadius Q.alpha u ∧
      a.capLiftRadius Q.alpha u-a.zeroOriginRadius Q.alpha u ≤ a.rmin) ∧
      (a.thetaZeroShiftedParentData lam hlam hld).objective P.alpha ≤
        a.thetaZeroHighOnlyData.minimum lam+a.thetaZeroCapLiftPressurePad lam hlam hld Q.alpha gamma := by
  obtain ⟨gamma,Hgamma⟩:=a.cap_lift_feasible_original_profile Q.alpha
  refine ⟨gamma,Hgamma,?_⟩
  have H:=P.minimum gamma
  dsimp only [thetaZeroCapLiftPressurePad]
  rw [←Q.attained]
  linarith only [H]

end ActualHighWallData
end OAI.SKFluctuations.LaplaceWindowFormalization
