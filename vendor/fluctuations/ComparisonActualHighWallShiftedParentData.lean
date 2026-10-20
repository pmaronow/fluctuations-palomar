module

public import ComparisonActualShiftedParentChildCall
public import ComparisonActualHighWallDescendantSource
public import ComparisonActualHighWallInnovation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 14000000
namespace ActualHighWallData
variable {n:ℕ} {delta:ℝ} (a:ActualHighWallData n delta)

theorem masked_coefficient_eq (alpha:a.Profile):
    omittedStrengthCoefficient a.d a.s (a.wallRadius alpha) (a.d^2)=
      wallHighCoefficient a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM a.g a.hg.continuous alpha :=
  omittedStrengthCoefficient_eq_original a.hr ⟨a.hs.1.le,a.hs1⟩ a.hc a.hk a.hkc a.hm a.hM a.d (a.d^2) alpha

theorem masked_field_coefficient_eq (alpha:a.Profile):
    (fun u=>omittedStrengthCoefficient a.d a.s (a.wallRadius alpha) (a.d^2) u*a.wallRadius alpha u)=
      wallHighCoefficient a.hr a.hs1 a.hc a.hk a.hkc a.hm a.hM
        (fun r=>a.g r*r) (a.hg.continuous.mul continuous_id) alpha := by
  ext u
  by_cases hu:a.s ≤ u <;>
    simp [wallHighCoefficient,wallRadius,comparisonCalibrationConstrainedRadius,
      omittedStrengthCoefficient,omittedExtension,IccExtend,constrainedCoefficient,
      constrainedQuantileMap,hu,Function.comp_def]

def shiftedParentData : ActualShiftedParentData n delta where
  numerics:={E:=a.E,d:=a.d,hn:=a.hn,hE:=a.hE,hd:=a.hd}
  r0:=a.rmin
  s:=a.s
  hr0:=a.hrbounds.1.le
  hr1:=a.hr
  hs:=⟨a.hs.1.le,a.hs1⟩
  lam:=a.d^2
  hlam:=sq_pos_of_pos a.hd
  hld:=le_rfl
  b:=wallBareMatrix a.T a.epsilon a.theta a.s
  h:=wallBareField a.T a.epsilon a.theta a.s a.tau a.d a.rmin
  clockAdmissible:=by
    intro alpha
    change a.Profile at alpha
    have HC:=a.admissible alpha
    have HB:(fun u=>wallBareMatrix a.T a.epsilon a.theta a.s u-
        omittedStrengthCoefficient a.d a.s (a.wallRadius alpha) (a.d^2) u)=a.b alpha:=by
      rw [a.masked_coefficient_eq alpha]
      rfl
    have HH:(fun u=>wallBareField a.T a.epsilon a.theta a.s a.tau a.d a.rmin u+
        omittedStrengthCoefficient a.d a.s (a.wallRadius alpha) (a.d^2) u*a.wallRadius alpha u)=a.h alpha:=by
      ext u
      change wallBareField a.T a.epsilon a.theta a.s a.tau a.d a.rmin u+_=
        wallBareField a.T a.epsilon a.theta a.s a.tau a.d a.rmin u+_
      rw [congrFun (a.masked_field_coefficient_eq alpha) u]
    change MonotoneOn (fun u=>wallBareMatrix a.T a.epsilon a.theta a.s u-
        omittedStrengthCoefficient a.d a.s (a.wallRadius alpha) (a.d^2) u) (Icc (0:ℝ) 1) ∧
      MonotoneOn (fun u=>wallBareField a.T a.epsilon a.theta a.s a.tau a.d a.rmin u+
        omittedStrengthCoefficient a.d a.s (a.wallRadius alpha) (a.d^2) u*a.wallRadius alpha u) (Icc (0:ℝ) 1) ∧
      (∀u∈Icc (0:ℝ) 1,0 ≤ wallBareMatrix a.T a.epsilon a.theta a.s u-
        omittedStrengthCoefficient a.d a.s (a.wallRadius alpha) (a.d^2) u) ∧
      (∀u∈Icc (0:ℝ) 1,0 ≤ wallBareField a.T a.epsilon a.theta a.s a.tau a.d a.rmin u+
        omittedStrengthCoefficient a.d a.s (a.wallRadius alpha) (a.d^2) u*a.wallRadius alpha u)
    rw [HB,HH]
    refine ⟨HC.1,HC.2.1,fun u hu=>HC.2.2.1.trans (HC.1 ⟨le_rfl,zero_le_one⟩ hu hu.1),?_⟩
    intro u hu
    have H:=HC.2.2.2.trans (HC.2.1 ⟨le_rfl,zero_le_one⟩ hu hu.1)
    simpa only [←congrFun HH u] using H

end ActualHighWallData
namespace ActualHighWallOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}

def shiftedParentMinimum (M:ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock):
    ActualShiftedParentMinimum M.data.shiftedParentData where
  alpha:=M.alpha
  minimum:=by
    intro gamma
    have HM:=M.inverse_minimum gamma
    have Hobj (alpha:M.data.Profile):M.data.shiftedParentData.objective alpha=
        inverseCompensatedPressure M.data.hr M.data.hs1 M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM
          M.data.g M.data.hg.continuous n
          (wallBareMatrix M.data.T M.data.epsilon M.data.theta M.data.s)
          (wallBareField M.data.T M.data.epsilon M.data.theta M.data.s M.data.tau M.data.d M.data.rmin) 0 alpha:=
      omittedComparisonSweepObjective_eq_inverse M.data.hr ⟨M.data.hs.1.le,M.data.hs1⟩ M.data.hc M.data.hk M.data.hkc M.data.hm M.data.hM n
        (wallBareMatrix M.data.T M.data.epsilon M.data.theta M.data.s)
        (wallBareField M.data.T M.data.epsilon M.data.theta M.data.s M.data.tau M.data.d M.data.rmin)
        M.data.d (M.data.d^2) alpha
    rw [Hobj M.alpha,Hobj gamma]
    exact HM

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
