module

public import ComparisonActualHighWallThetaZeroPositiveFloorThermal
public import ComparisonActualHighWallThetaZeroErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem Potential.eq7_error_sign_partition_on_band
    (P : Q.Potential) {lo hi : ℝ}
    (hlo : Q.data.s ≤ lo) (hlohi : lo ≤ hi) (hhi : hi ≤ 1) :
    (∫u in lo..hi,Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) =
      (∫u in lo..hi,
        (P.negativeSet ∪ P.contactSet).indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u)+
      (∫u in lo..hi,
        P.positiveSet.indicator (fun _ => (1:ℝ))
          (Q.shiftedNativeModel.R u)*
          Q.data.thetaZeroErrorDensity Q.lam Q.alpha u) := by
  let model := Q.shiftedNativeModel
  have hmi : MeasurableSet (P.negativeSet ∪ P.contactSet) :=
    P.negativeSet_open.measurableSet.union P.contactSet_measurable
  have hn := (Q.error_mask_intervalIntegrable _ hmi).mono_set (by
    rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (Q.data.hs.1.le.trans hlo) hhi)
  have hp := (Q.error_mask_intervalIntegrable _ P.positiveSet_measurable).mono_set (by
    rw [uIcc_of_le hlohi,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (Q.data.hs.1.le.trans hlo) hhi)
  simp only [← Q.shiftedNativeModel_radius] at hn hp
  rw [←intervalIntegral.integral_add hn hp]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [volume.ae_ne hi] with u hune hu
  have hu0 : u ∈ Ioc lo hi := by simpa only [uIoc_of_le hlohi] using hu
  have huOpen : u ∈ Ioo lo hi :=
    ⟨hu0.1,lt_of_le_of_ne hu0.2 hune⟩
  have hum : u ∈ Icc Q.data.s 1 :=
    ⟨hlo.trans huOpen.1.le,huOpen.2.le.trans hhi⟩
  have hR : model.R u ∈ Ioo Q.data.rmin 1 := by
    have hleft : model.R Q.data.s < model.R u :=
      model.R_strictMonoOn ⟨le_rfl,Q.data.hs1⟩ hum
        (hlo.trans_lt huOpen.1)
    have hright : model.R u < model.R 1 :=
      model.R_strictMonoOn hum ⟨Q.data.hs1,le_rfl⟩
        (huOpen.2.trans_le hhi)
    rw [show model.R Q.data.s = Q.data.rmin from model.R_left] at hleft
    rw [model.R_one] at hright
    exact ⟨hleft,hright⟩
  have hnon : (model.R u∈P.negativeSet ∪ P.contactSet) ↔
      P.H (model.R u) ≤ 0 := by
    constructor
    · rintro (h|h)
      · exact h.2.le
      · exact h.2.le
    · intro h
      rcases lt_or_eq_of_le h with hneg|hz
      · exact Or.inl ⟨hR,hneg⟩
      · exact Or.inr ⟨Ioo_subset_Icc_self hR,hz⟩
  have hpos : (model.R u∈P.positiveSet) ↔
      0 < P.H (model.R u) :=
    ⟨fun h=>h.2,fun h=>⟨Ioo_subset_Icc_self hR,h⟩⟩
  change Q.data.thetaZeroErrorDensity Q.lam Q.alpha u =
    (P.negativeSet ∪ P.contactSet).indicator (fun _ => (1:ℝ)) (model.R u)*
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u+
    P.positiveSet.indicator (fun _ => (1:ℝ)) (model.R u)*
      Q.data.thetaZeroErrorDensity Q.lam Q.alpha u
  by_cases hH : 0 < P.H (model.R u)
  · have hP : model.R u∈P.positiveSet := hpos.mpr hH
    have hN : model.R u∉P.negativeSet∪P.contactSet :=
      fun h => not_le_of_gt hH (hnon.mp h)
    simp only [indicator_of_mem hP,indicator_of_notMem hN,
      zero_mul,one_mul,zero_add] <;> rfl
  · have hN : model.R u∈P.negativeSet∪P.contactSet :=
      hnon.mpr (le_of_not_gt hH)
    have hP : model.R u∉P.positiveSet := fun h => hH (hpos.mp h)
    simp only [indicator_of_mem hN,indicator_of_notMem hP,
      one_mul,zero_mul,add_zero] <;> rfl

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
