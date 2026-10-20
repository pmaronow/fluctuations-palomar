module

public import ComparisonActualHighWallThetaZeroEq7ErrorSignPartition
public import ComparisonActualHighWallThetaZeroEq7InnerNonpositive
public import ComparisonOriginalQEq7FloorRestrictionCoreDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum
  (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.eq7_inner_error_le_thermal_exact_floor_core
    (P : Q.Potential) {lo hi : ℝ}
    (hlo : Q.data.s ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) :
    (∫u in lo..hi,
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      3*Q.lam*(∫u in lo..hi,
        (P.negativeSet ∪ P.contactSet).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u)+
      16*Q.lam*(Q.data.rmin+Q.cavityCapTravel)^2*(hi-lo)+
      (∫u in lo..hi,
        P.positiveSet.indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) := by
  have hSign := P.eq7_error_sign_partition_on_band hlo hlohi hhi
  have hNonpos := P.eq7_inner_cap_contact_error_le_thermal
    hlo hlohi hhi
  dsimp only at hNonpos
  have hNonpos' :
      (∫u in lo..hi,
        (P.negativeSet ∪ P.contactSet).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      3*Q.lam*(∫u in lo..hi,
        (P.negativeSet ∪ P.contactSet).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u)+
      16*Q.lam*(Q.data.rmin+Q.cavityCapTravel)^2*(hi-lo) := by
    simpa only [Q.shiftedNativeModel_radius] using hNonpos
  rw [hSign]
  linarith only [hNonpos']

theorem Potential.eq7_inner_error_le_thermal_full_floor_core
    (P : Q.Potential) {lo hi : ℝ}
    (hlo : Q.data.s ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) :
    (∫u in lo..hi,
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) ≤
      3*Q.lam*(∫u in lo..hi,
        (P.negativeSet ∪ P.contactSet).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*Q.shiftedNativeModel.thermal u)+
      16*Q.lam*(Q.data.rmin+Q.cavityCapTravel)^2*(hi-lo)+
      (∫u in Q.data.s..hi,
        P.positiveSet.indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) := by
  have hExact :=
    P.eq7_inner_error_le_thermal_exact_floor_core hlo hlohi hhi
  have hFloor := P.eq7_positive_full_floor_restrict_core hlo hlohi hhi
  linarith only [hExact,hFloor]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
