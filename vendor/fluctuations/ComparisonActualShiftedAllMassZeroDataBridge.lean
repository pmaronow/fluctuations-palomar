module

public import ComparisonActualShiftedAllMassParentChildCall

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 14000000
set_option backward.isDefEq.respectTransparency false
namespace ActualShiftedAllMassParentChildCall
variable {n : ℕ} {delta : ℝ} (a : ActualShiftedAllMassParentChildCall n delta)

def zeroMassData (hq : 2≤(n:ℝ)^delta)
    (hroom : a.childRadius^2≤a.context.b 0-a.coefficient 0) : ActualHighOnlyComparisonData n delta where
  E:=a.childData.E
  d:=a.childRadius
  s:=0
  b:=fun u=>a.context.b u-a.coefficient u
  h:=fun u=>a.context.h u+a.coefficient u*a.R u
  hn:=a.childData.hn
  hE:=a.childData.hE
  hd:=a.childData.hd
  hs:=by norm_num
  hq:=hq
  hb:=(a.context.clockAdmissible a.alpha).1
  hh:=(a.context.clockAdmissible a.alpha).2.1
  hb0:=(a.context.clockAdmissible a.alpha).2.2.1 0 ⟨le_rfl,zero_le_one⟩
  hh0:=(a.context.clockAdmissible a.alpha).2.2.2 0 ⟨le_rfl,zero_le_one⟩
  hcut:=hroom
  hcross:=by intro u hu;exact False.elim (not_lt_of_ge hu.1 hu.2)

theorem zeroMassData_radius (hq : 2≤(n:ℝ)^delta)
    (hroom : a.childRadius^2≤a.context.b 0-a.coefficient 0)
    (beta : a.childData.Profile) : (a.zeroMassData hq hroom).R beta=a.childData.R beta := rfl

theorem zeroMassData_objective_eq (hq : 2≤(n:ℝ)^delta)
    (hroom : a.childRadius^2≤a.context.b 0-a.coefficient 0)
    (beta : a.childData.Profile) :
    (a.zeroMassData hq hroom).objective a.childLam beta=
      variableEndpointComparisonSweepObjective a.childData.hc a.childData.hk a.childData.hkc a.childData.hm a.childData.hM n
        (fun u=>a.context.b u-a.coefficient u)
        (fun u=>a.context.h u+a.coefficient u*a.R u) a.childRadius a.childLam beta := by
  let data:=a.zeroMassData hq hroom
  have HP:=a.context.clockAdmissible a.alpha
  change data.objective a.childLam beta=_
  rw [data.objective_eq_inverse]
  rw [variableEndpointComparisonSweepObjective_eq_inverse a.childData.hc a.childData.hk a.childData.hkc a.childData.hm a.childData.hM
    n a.context.hn _ _ a.childData.hd.ne' a.hchildLam.le a.matrixRoom HP.1 HP.2.1
    (HP.2.2.2 0 ⟨le_rfl,zero_le_one⟩)]
  rfl

theorem zeroMassData_minimum_eq (hq : 2≤(n:ℝ)^delta)
    (hroom : a.childRadius^2≤a.context.b 0-a.coefficient 0) :
    (a.zeroMassData hq hroom).minimum a.childLam=
      variableEndpointComparisonSweepMinimum a.childData.hc a.childData.hk a.childData.hkc a.childData.hm a.childData.hM n
        (fun u=>a.context.b u-a.coefficient u)
        (fun u=>a.context.h u+a.coefficient u*a.R u) a.childRadius a.childLam := by
  unfold ActualHighOnlyComparisonData.minimum omittedComparisonSweepMinimum variableEndpointComparisonSweepMinimum
  congr 1
  have H : (fun beta : a.childData.Profile=>(a.zeroMassData hq hroom).objective a.childLam beta)=
      variableEndpointComparisonSweepObjective a.childData.hc a.childData.hk a.childData.hkc a.childData.hm a.childData.hM n
        (fun u=>a.context.b u-a.coefficient u) (fun u=>a.context.h u+a.coefficient u*a.R u) a.childRadius a.childLam:=
    funext (a.zeroMassData_objective_eq hq hroom)
  exact congrArg Set.range H

def zeroMassMinimum (hq : 2≤(n:ℝ)^delta)
    (hroom : a.childRadius^2≤a.context.b 0-a.coefficient 0) :
    ActualHighOnlyComparisonMinimum (a.zeroMassData hq hroom) a.childLam where
  alpha:=a.childAlpha
  attained:=by
    rw [a.zeroMassData_objective_eq hq hroom,a.zeroMassData_minimum_eq hq hroom]
    exact a.attained
  minimum:=by
    intro beta
    obtain ⟨alpha,hattained,Hmin⟩:=(a.zeroMassData hq hroom).exists_minimum ⟨a.hchildLam.le,a.hchildLd⟩
    have HA : (a.zeroMassData hq hroom).objective a.childLam a.childAlpha=
        (a.zeroMassData hq hroom).minimum a.childLam:=by
      rw [a.zeroMassData_objective_eq hq hroom,a.zeroMassData_minimum_eq hq hroom]
      exact a.attained
    exact HA.trans_le (Hmin beta)

end ActualShiftedAllMassParentChildCall
end OAI.SKFluctuations.LaplaceWindowFormalization
