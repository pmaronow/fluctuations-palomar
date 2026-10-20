module

public import ComparisonActualHighWallThetaZeroFixedMargins
public import ComparisonActualShiftedAllMassParentChildCall

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option linter.unusedVariables false

namespace ActualThetaZeroOverlapMinimum
variable {n:ℕ} {m delta cl cu Az C0 Ct D Bclock:ℝ}
variable (M:ActualThetaZeroOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)

def shiftedMinimum : ActualShiftedParentMinimum
    (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld) where
  alpha:=M.alpha
  minimum:=M.minimum

abbrev allMassChildNumerics {c0:ℝ} (hc0:0<c0) : NativeChildBarrierParameters n delta :=
  (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).numerics.actualChild
    M.hlam hc0 M.hxs

def allMassChildSweepCost {c0:ℝ} (hc0:0<c0) : ℝ :=
  let child:=M.allMassChildNumerics hc0
  let P:=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
  variableEndpointComparisonSweepCost child.hc child.hk child.hkc child.hm child.hM n
    (fun u=>P.b u-P.coefficient M.alpha u)
    (fun u=>P.h u+P.coefficient M.alpha u*P.R M.alpha u)
    child.d ((c0*M.xs)^2)

theorem all_mass_child_room_of_small_epsilon {c0:ℝ} (hc0:0<c0)
    (heps:M.data.epsilon≤M.data.T/4)
    (hchild:(c0*M.xs)^2≤M.data.T/8) :
    (c0*M.xs)^2≤
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b 0-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha 0 := by
  have hzero:(0:ℝ)<M.data.s:=M.data.hs.1
  rw [M.data.theta_zero_changed_low_matrix M.lam M.hlam M.hld M.alpha hzero]
  have hT:0<M.data.T:=M.data.hepsilon.1.trans M.data.hepsilon.2
  linarith only [heps,hchild,hT]

theorem exists_all_mass_child {c0:ℝ} (hc0:0<c0)
    (hroom:(c0*M.xs)^2≤
      (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b 0-
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha 0) :
    ∃a:ActualShiftedAllMassParentChildCall n delta,
      a.context=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld ∧
      HEq a.optimizer M.shiftedMinimum ∧
      a.R=(M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).R M.alpha ∧
      a.childRadius=c0*M.xs ∧ a.childLam=(c0*M.xs)^2 ∧
      (∀u,a.context.b u-a.coefficient u=
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).b u-
          (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u) ∧
      (∀u,a.context.h u+a.coefficient u*a.R u=
        (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).h u+
          (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).coefficient M.alpha u*
            (M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld).R M.alpha u) ∧
      a.err=M.allMassChildSweepCost hc0 := by
  let P:=M.data.thetaZeroShiftedParentData M.lam M.hlam M.hld
  let child:=M.allMassChildNumerics hc0
  have had:=P.clockAdmissible M.alpha
  obtain ⟨beta,hbeta,_⟩:=variableEndpointComparisonSweepMinimum_attained
    child.hc child.hk child.hkc child.hm child.hM n M.data.hn
    (fun u=>P.b u-P.coefficient M.alpha u)
    (fun u=>P.h u+P.coefficient M.alpha u*P.R M.alpha u)
    child.hd.ne' (sq_pos_of_pos (mul_pos hc0 M.hxs)).le hroom
    had.1 had.2.1 (had.2.2.2 0 ⟨le_rfl,zero_le_one⟩)
    (comparisonCap_continuous _ _ _ _ _ _) (child.profile_nonempty M.data.hq)
  let a:ActualShiftedAllMassParentChildCall n delta:={
    context:=P
    optimizer:=M.shiftedMinimum
    childData:=child
    childLam:=(c0*M.xs)^2
    hchildLam:=sq_pos_of_pos (mul_pos hc0 M.hxs)
    hchildLd:=le_rfl
    childAlpha:=beta
    matrixRoom:=hroom
    attained:=hbeta}
  exact ⟨a,rfl,HEq.rfl,rfl,rfl,rfl,fun _=>rfl,fun _=>rfl,rfl⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
