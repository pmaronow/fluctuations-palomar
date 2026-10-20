module

public import ComparisonNativeOriginalHighTailEdgeBudget
public import PhysicalWindowTraceAggregation
public import CavityRealMomentMonotonicity

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem native_edgeBudget_eq_finite_mass_average {as : List PositiveMass}
    (he : partitionEnd 0 as=1) (f : ℕ→ℝ) :
    ClockTree.edgeBudget 0 as f=
      ∑i : Fin as.length,(partitionPoint 0 as (i.val+1)-partitionPoint 0 as i.val)*f i.val := by
  rw [native_edgeBudget_eq_cells_add_terminal,he,sub_self,zero_mul,add_zero,
    massCellSum_eq_partitionPoint_sum]
  exact (Fin.sum_univ_eq_sum_range (fun j : ℕ=>(partitionPoint 0 as (j+1)-partitionPoint 0 as j)*f j) as.length).symm

theorem native_edgeBudget_real_moment_le {as : List PositiveMass}
    (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (D : ℕ→ℝ) (hD : ∀j,0≤D j) {p B : ℝ} (hp : 0<p) (hp2 : p≤2) (hB : 0≤B)
    (hmoment : ClockTree.edgeBudget 0 as (fun j=>(D j)^2)≤B^2) :
    ClockTree.edgeBudget 0 as (fun j=>(D j)^p)≤B^p := by
  let w:=fun i : Fin as.length=>partitionPoint 0 as (i.val+1)-partitionPoint 0 as i.val
  have hw i : 0≤w i:=sub_nonneg.mpr (partitionPoint_mono as ho (Nat.le_succ i.val))
  have hmass : ∑i,w i=1 := by
    rw [Fin.sum_univ_eq_sum_range (fun j : ℕ=>partitionPoint 0 as (j+1)-partitionPoint 0 as j),
      Finset.sum_range_sub]
    have Hend : partitionPoint 0 as as.length=1 := by simpa only [physicalPartitionPoint_length] using he
    rw [Hend,partitionPoint,partitionValues_zero]
    norm_num
  have Hsecond : (∑i : Fin as.length,w i*|D i.val|^(2:ℝ))≤B^(2:ℝ) := by
    simp_rw [abs_of_nonneg (hD _),Real.rpow_two]
    dsimp only [w]
    rw [←native_edgeBudget_eq_finite_mass_average he (fun j=>D j^2)]
    exact hmoment
  have H:=finite_weighted_rpow_moment_le w (fun i=>D i.val) hw hmass hp hp2 hB Hsecond
  rw [native_edgeBudget_eq_finite_mass_average he]
  simpa only [w,abs_of_nonneg (hD _)] using H

end OAI.SKFluctuations.LaplaceWindowFormalization
