module

public import ComparisonSignedCavityTargetRowInterval
public import ComparisonSignedCavityActualBoundarySchedule
public import ComparisonSignedCavityActualGammaHighBound

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_edgeBudget_supported_mass_le
    {a mesh B : ℝ} (as : List PositiveMass) (ho : MassOrdered a as)
    (he : partitionEnd a as=1) (hm : PartitionMesh mesh a as)
    (f : ℕ → ℝ) (hf : ∀j,0 ≤ f j) (hf1 : ∀j,f j ≤ 1)
    (hsupp : ∀j,B < partitionPoint a as j → f j=0) :
    ClockTree.edgeBudget a as f ≤ max (B+mesh-a) 0 := by
  induction as generalizing a f with
  | nil=>
    change a=1 at he
    simp only [ClockTree.edgeBudget,he,sub_self,zero_mul]
    exact le_max_right _ _
  | cons b bs ih=>
    have hs : ∀j,B < partitionPoint b.val bs j → (fun j=>f (1+j)) j=0 := by
      intro j hj
      simpa only [Nat.add_comm] using hsupp (j+1) (by
        simpa only [partitionPoint,partitionValues] using hj)
    have H:=ih ho.2.2 he hm.2 (fun j=>f (1+j))
      (fun j=>hf _) (fun j=>hf1 _) hs
    by_cases ha : a ≤ B
    · have hb : b.val ≤ B+mesh := by linarith [hm.1]
      have hba : 0 ≤ b.val-a:=sub_nonneg.mpr ho.2.1
      have hterm:=mul_le_mul_of_nonneg_left (hf1 0) hba
      rw [max_eq_left (by linarith)] at H
      rw [max_eq_left (by linarith)]
      change (b.val-a)*f 0+ClockTree.edgeBudget b.val bs (fun j=>f (1+j)) ≤ _
      linarith
    · have hz : f 0=0 := hsupp 0 (by
        simpa only [partitionPoint,partitionValues,id_eq] using lt_of_not_ge ha)
      change (b.val-a)*f 0+ClockTree.edgeBudget b.val bs (fun j=>f (1+j)) ≤ _
      rw [hz,mul_zero,zero_add]
      exact H.trans (max_le_max_right 0 (by linarith [ho.2.1]))

def nativeRadiusRowBand (R : ℝ → ℝ) (as : List PositiveMass) (v : ℝ) (j : ℕ) : ℝ :=
  if v ≤ R (partitionPoint 0 as j) ∧ R (partitionPoint 0 as j) ≤ 2*v then 1 else 0

theorem nativeRadiusRowBand_nonneg (R : ℝ → ℝ) (as : List PositiveMass) (v : ℝ) (j : ℕ) :
    0 ≤ nativeRadiusRowBand R as v j := by unfold nativeRadiusRowBand;split_ifs <;> norm_num

theorem nativeRadiusRowBand_le_one (R : ℝ → ℝ) (as : List PositiveMass) (v : ℝ) (j : ℕ) :
    nativeRadiusRowBand R as v j ≤ 1 := by unfold nativeRadiusRowBand;split_ifs <;> norm_num

theorem actual_minimum_radius_band_edgeBudget_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 ≤ cu) {mesh v : ℝ} (hv : 0 ≤ v) (hz : M.z ≤ v)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1) (hm : PartitionMesh mesh 0 as)
    (hmesh : 0 ≤ mesh) :
    ClockTree.edgeBudget 0 as (nativeRadiusRowBand M.R as v) ≤ 2*cu*v+mesh := by
  have H:=native_edgeBudget_supported_mass_le as ho he hm
    (nativeRadiusRowBand M.R as v) (nativeRadiusRowBand_nonneg _ _ _)
    (nativeRadiusRowBand_le_one _ _ _) (B:=2*cu*v) (by
      intro j hj
      unfold nativeRadiusRowBand
      split_ifs with hband
      · have hR:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
          M.context.hm M.context.hM M.alpha (partitionPoint 0 as j)
        have hreg:=(M.regular (M.R (partitionPoint 0 as j)) ⟨hz.trans hband.1,hR.2⟩).2
        have hspec:=comparisonSweepQuantile_mass_spec M.context.hc M.context.hk M.context.hkc
          M.context.hm M.context.hM M.alpha (partitionPoint_mem as ho j)
        rw [hspec] at hreg
        have H:=mul_le_mul_of_nonneg_left hband.2 hcu
        nlinarith
      · rfl)
  simpa only [sub_zero,max_eq_left (by positivity : 0 ≤ 2*cu*v+mesh)] using H

end OAI.SKFluctuations.Cavity
