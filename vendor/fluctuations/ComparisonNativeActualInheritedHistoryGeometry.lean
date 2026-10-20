module

public import ComparisonNativeActualInheritedClocks
public import ComparisonNativeActualMinimumCapGeometry
public import ComparisonFiniteHistory

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 6000000

theorem actual_history_field_zero (ts : List ComparisonHistoryTerm) :
    historyFieldAddition ts 0=0 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    have hq : t.quantile 0=0 := comparisonSweepQuantile_zero t.hc t.hk t.hkc t.hm t.hM t.α
    simp only [historyFieldAddition,ComparisonHistoryTerm.fieldAddition,hq,mul_zero,ih,add_zero]

theorem actual_history_field_le_reduction (ts : List ComparisonHistoryTerm)
    (hlam : ∀t∈ts,0 ≤ t.lam) (u : ℝ) :
    historyFieldAddition ts u ≤ historyMatrixReduction ts u := by
  induction ts with
  | nil => exact le_rfl
  | cons t ts ih =>
    have he:=laplaceComparisonStrength_nonneg t.d (t.quantile u) (hlam t (by simp))
    have hr:=(comparisonSweepQuantile_bounds t.hc t.hk t.hkc t.hm t.hM t.α u).2
    change t.quantile u ≤ 1 at hr
    have ht : t.fieldAddition u ≤ t.matrixReduction u := by
      simpa only [ComparisonHistoryTerm.fieldAddition,ComparisonHistoryTerm.matrixReduction,mul_one]
        using mul_le_mul_of_nonneg_left hr he
    exact add_le_add ht (ih (fun t ht=>hlam t (by simp [ht])))

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

def toHistoryTerm {n : ℕ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) : ComparisonHistoryTerm where
  c:=M.context.floor
  k:=M.context.k
  M:=M.context.M
  hc:=M.context.hc
  hk:=M.context.hk
  hkc:=M.context.hkc
  hm:=M.context.hm
  hM:=M.context.hM
  α:=M.alpha
  d:=M.context.d
  lam:=M.lam

theorem toHistoryTerm_quantile {n : ℕ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) :
    M.toHistoryTerm.quantile=M.R := rfl

theorem inherited_history_child_endpoint {n : ℕ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (ts : List ComparisonHistoryTerm) (B H : ℝ)
    (hb : ∀u,M.b u=B-historyMatrixReduction ts u)
    (hh : ∀u,M.h u=H+historyFieldAddition ts u) (u : ℝ) :
    M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)=
        B-historyMatrixReduction (M.toHistoryTerm::ts) u ∧
      M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u=
        H+historyFieldAddition (M.toHistoryTerm::ts) u := by
  rw [hb,hh]
  simp only [historyMatrixReduction,historyFieldAddition,ComparisonHistoryTerm.matrixReduction,
    ComparisonHistoryTerm.fieldAddition,M.toHistoryTerm_quantile]
  change (B-historyMatrixReduction ts u)-laplaceComparisonStrength M.context.d M.lam (M.R u)=
      B-(laplaceComparisonStrength M.context.d M.lam (M.R u)+historyMatrixReduction ts u) ∧
    (H+historyFieldAddition ts u)+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u=
      H+(laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u+historyFieldAddition ts u)
  constructor <;> ring

theorem inherited_history_total_root {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ts : List ComparisonHistoryTerm) (T : ℝ)
    (hb : ∀u,M.b u=T-historyMatrixReduction ts u)
    (hh : ∀u,M.h u=historyFieldAddition ts u)
    (hlam : ∀t∈ts,0 ≤ t.lam) :
    (∀u∈Icc (0:ℝ) 1,M.h u+M.b u ≤ T) ∧ M.h 0=0 := by
  constructor
  · intro u _
    rw [hb,hh]
    linarith [actual_history_field_le_reduction ts hlam u]
  · rw [hh,actual_history_field_zero]

theorem inherited_history_clock_lipschitz {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ts : List ComparisonHistoryTerm) (B H : ℝ)
    (hb : ∀u,M.b u=B-historyMatrixReduction ts u)
    (hh : ∀u,M.h u=H+historyFieldAddition ts u) :
    ∃Kb Kh : ℝ≥0,
      LipschitzOnWith Kb (fun r=>M.b (M.alpha.val.val r)) (Icc (0:ℝ) 1) ∧
      LipschitzOnWith Kh (fun r=>M.h (M.alpha.val.val r)) (Icc (0:ℝ) 1) := by
  obtain ⟨Kb,hKb⟩:=historyMatrixReduction_lipschitz ts
  obtain ⟨Kh,hKh⟩:=historyFieldAddition_lipschitz ts
  have hα:=inverseIntegralConstraints_lipschitz M.context.hm M.context.hM M.alpha.property
  refine ⟨Kb*Real.toNNReal (M.context.M 1),Kh*Real.toNNReal (M.context.M 1),?_,?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hd:=hKb.dist_le_mul (M.alpha.val.val x) (M.alpha.val.val y)
    have hαd:=hα.dist_le_mul x hx y hy
    change dist (M.alpha.val.val x) (M.alpha.val.val y) ≤ M.context.M 1*dist x y at hαd
    rw [hb,hb]
    have he : dist (B-historyMatrixReduction ts (M.alpha.val.val x))
        (B-historyMatrixReduction ts (M.alpha.val.val y))=
        dist (historyMatrixReduction ts (M.alpha.val.val x))
          (historyMatrixReduction ts (M.alpha.val.val y)) := by
      simp only [Real.dist_eq]
      have h : B-historyMatrixReduction ts (M.alpha.val.val x)-
          (B-historyMatrixReduction ts (M.alpha.val.val y))=
          -(historyMatrixReduction ts (M.alpha.val.val x)-historyMatrixReduction ts (M.alpha.val.val y)) := by ring
      rw [h,abs_neg]
    rw [he]
    apply hd.trans
    change (Kb:ℝ)*dist _ _ ≤ (Kb:ℝ)*(Real.toNNReal (M.context.M 1):ℝ)*dist x y
    rw [Real.coe_toNNReal _ M.context.hM]
    convert mul_le_mul_of_nonneg_left hαd Kb.coe_nonneg using 1; ring
  · apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hd:=hKh.dist_le_mul (M.alpha.val.val x) (M.alpha.val.val y)
    have hαd:=hα.dist_le_mul x hx y hy
    change dist (M.alpha.val.val x) (M.alpha.val.val y) ≤ M.context.M 1*dist x y at hαd
    rw [hh,hh,dist_add_left]
    apply hd.trans
    change (Kh:ℝ)*dist _ _ ≤ (Kh:ℝ)*(Real.toNNReal (M.context.M 1):ℝ)*dist x y
    rw [Real.coe_toNNReal _ M.context.hM]
    convert mul_le_mul_of_nonneg_left hαd Kh.coe_nonneg using 1; ring

theorem Potential.inherited_history_common_geometry {n : ℕ}
    {M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (ts : List ComparisonHistoryTerm) (B H : ℝ)
    (hb : ∀u,M.b u=B-historyMatrixReduction ts u)
    (hh : ∀u,M.h u=H+historyFieldAddition ts u) : Nonempty (M.CommonBandGeometry p) := by
  obtain ⟨Kb,Kh,hKb,hKh⟩:=M.inherited_history_clock_lipschitz ts B H hb hh
  exact ⟨p.commonGeometry Kb Kh hKb hKh⟩

theorem inherited_child_clock_lipschitz {n : ℕ}
    (P M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ts : List ComparisonHistoryTerm) (B H : ℝ)
    (hb : ∀u,P.b u=B-historyMatrixReduction ts u)
    (hh : ∀u,P.h u=H+historyFieldAddition ts u)
    (hchildb : ∀u,M.b u=P.b u-laplaceComparisonStrength P.context.d P.lam (P.R u))
    (hchildh : ∀u,M.h u=P.h u+laplaceComparisonStrength P.context.d P.lam (P.R u)*P.R u) :
    ∃Kb Kh : ℝ≥0,
      LipschitzOnWith Kb (fun r=>M.b (M.alpha.val.val r)) (Icc (0:ℝ) 1) ∧
      LipschitzOnWith Kh (fun r=>M.h (M.alpha.val.val r)) (Icc (0:ℝ) 1) := by
  exact M.inherited_history_clock_lipschitz (P.toHistoryTerm::ts) B H
    (fun u=>(hchildb u).trans (P.inherited_history_child_endpoint ts B H hb hh u).1)
    (fun u=>(hchildh u).trans (P.inherited_history_child_endpoint ts B H hb hh u).2)

theorem inherited_shell_history_clock_lipschitz {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ts : List ComparisonHistoryTerm) (T epsilon s a z : ℝ)
    (hb : ∀u,M.b u=historyMatrixClock T epsilon s ts u)
    (hh : ∀u,M.h u=historyFieldClock ts u)
    (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1)
    (hbranch : M.alpha.val.val z < s ∨ s ≤ M.alpha.val.val a) :
    ∃Kb Kh : ℝ≥0,
      LipschitzOnWith Kb (fun r=>M.b (M.alpha.val.val r)) (Icc a z) ∧
      LipschitzOnWith Kh (fun r=>M.h (M.alpha.val.val r)) (Icc a z) := by
  obtain ⟨Kb,hKb⟩:=historyMatrixClock_inverse_lipschitz M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.alpha T epsilon s ts ha haz hz hbranch
  obtain ⟨Kh,hKh⟩:=historyFieldClock_inverse_lipschitz M.context.hc M.context.hk
    M.context.hkc M.context.hm M.context.hM M.alpha ts ha haz hz
  refine ⟨Kb,Kh,?_,?_⟩
  · simpa only [hb] using hKb
  · simpa only [hh] using hKh

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
