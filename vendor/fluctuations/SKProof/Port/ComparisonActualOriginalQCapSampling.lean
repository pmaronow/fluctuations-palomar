module

public import ComparisonActualHighWallThetaZeroCapLocalPhysical
public import SKProof.Port.ComparisonActualOriginalQCanonicalMassBudgets

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (c : ShiftedCapInterval a P)
private theorem rmin_le_cap_travel
    (M : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock) :
    M.data.rmin ≤ M.cavityCapTravel := by
  have hU : 0 < M.data.U := M.data.hU
  have hL : 0 < M.data.L := M.data.hL
  have hpow : 0 < M.data.N^delta := Real.rpow_pos_of_pos M.data.hN _
  have hs0 : 0 ≤ M.data.s := M.data.hs.1.le
  have hrecip := (comparisonCap_first_term (δ:=delta) M.data.hN M.data.hU
    M.data.hL M.data.hE M.data.hd.le M.data.hs.1.le).2
  change 1/M.data.M M.data.s ≤
    (M.data.L/M.data.N^delta)*(1/(M.data.s+M.data.U)) at hrecip
  have hratio : M.data.U/(M.data.s+M.data.U) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by linarith [M.data.hs.1])
  have hhalf : M.data.rmin ≤ (M.data.L/M.data.N^delta)/2 := by
    calc
      M.data.rmin = (M.data.U/2)*(1/M.data.M M.data.s) := by
        change M.data.U/(2*M.data.M M.data.s) = _
        ring
      _ ≤ (M.data.U/2)*((M.data.L/M.data.N^delta)*(1/(M.data.s+M.data.U))) :=
        mul_le_mul_of_nonneg_left hrecip (by positivity)
      _ = ((M.data.L/M.data.N^delta)/2)*(M.data.U/(M.data.s+M.data.U)) := by ring
      _ ≤ ((M.data.L/M.data.N^delta)/2)*1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (M.data.L/M.data.N^delta)/2 := mul_one _
  have hU1 : M.data.U ≤ 1 := M.data.hsmall.trans M.data.hd1
  have hlog : (1:ℝ)/2 ≤ Real.log ((1+M.data.U)/M.data.U) := by
    have htwo : (2:ℝ) ≤ (1+M.data.U)/M.data.U :=
      (le_div_iff₀ M.data.hU).mpr (by linarith only [hU1])
    have H := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at H
    exact H.trans (Real.log_le_log (by norm_num) htwo)
  exact hhalf.trans (by
    change (M.data.L/M.data.N^delta)/2 ≤
      (M.data.L/M.data.N^delta)*Real.log ((1+M.data.U)/M.data.U)
    simpa only [div_eq_mul_inv,one_mul] using
      mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ M.data.L/M.data.N^delta))

theorem sampled_increment_canonical
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (hleftContact : P.H c.left=0 ∨ c.left=a.data.rmin) (hrightContact : P.H c.right=0 ∨ c.right=1)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) {i j : ℕ} (hij : i≤ j) (hj : j≤ as.length)
    (hiCap : a.shiftedNativeModel.R (partitionPoint 0 as i)∈Ioo c.left c.right)
    (hjCap : a.shiftedNativeModel.R (partitionPoint 0 as j)∈Ioo c.left c.right) :
    let m:=a.shiftedNativeModel
    let steps:=sampleClockSteps m.q 0 as
    let Cnode:=2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) m.q
    physicalPathSecondMoment (n+1) steps (m.q 0) j-
      physicalPathSecondMoment (n+1) steps (m.q 0) i≤ a.canonicalMassDiameter+2*(mesh*Cnode) := by
  dsimp only
  let m:=a.shiftedNativeModel
  have hmass:=partitionPoint_mono as ho hij
  have hrad:=m.R_monotone hmass
  have hiHigh : m.u0≤ partitionPoint 0 as i:=by
    by_contra HH
    have H:=m.R_monotone (le_of_not_ge HH)
    rw [m.R_left] at H
    exact (not_lt_of_ge H) (c.hleft.trans_lt hiCap.1)
  have hjHigh : m.u0≤ partitionPoint 0 as j:=hiHigh.trans hmass
  have hi0 : 0< partitionPoint 0 as i := a.data.hs.1.trans
    (a.radius_high_mass (c.hleft.trans_lt hiCap.1))
  have hj0 : 0< partitionPoint 0 as j := hi0.trans_le hmass
  have hinc : a.radiusS (m.R (partitionPoint 0 as j))-
      a.radiusS (m.R (partitionPoint 0 as i)) ≤ a.canonicalMassDiameter := by
    have hlog0 : 0 ≤ 9*Real.log a.data.N := by linarith
    rcases hleftContact with hcontact | hwall
    · exact (c.interior_radiusS_increment hN hlog hnd hcontact hrightContact
        hiCap hjCap hrad).trans
        (mul_le_mul_of_nonneg_left c.travel hlog0)
    · have hS0 : 0 ≤ a.radiusS (m.R (partitionPoint 0 as i)) :=
        (a.radius_moments.2.2 _ (m.R_bounds _)).1.1
      have hSj : a.radiusS (m.R (partitionPoint 0 as j)) ≤ c.right := by
        rcases hrightContact with hcontact | hterminal
        · exact P.cap_point_mean_le_right c.hleft c.hright hjCap hcontact
            (c.negative _ hjCap)
        · rw [hterminal]
          exact (a.radius_moments.2.2 _ (m.R_bounds _)).1.2
      have htravel := c.travel
      have hwallTravel := rmin_le_cap_travel a
      have htravel0 := a.cavityCapTravel_nonneg
      have hprice := mul_le_mul_of_nonneg_right
        (show (2:ℝ) ≤ 9*Real.log a.data.N by linarith) htravel0
      change _ ≤ 9*Real.log a.data.N*a.cavityCapTravel
      rw [hwall] at htravel
      linarith only [hS0,hSj,htravel,hwallTravel,hprice]
  have herr:=physicalSampledNodeSecondMoment_increment_le n a.sweepBf a.sweepHf m.hbf m.hhf
    as ho he hmesh (hij.trans hj) hj hi0 hj0
  have hiSpec:=m.R_spec ⟨hiHigh,(partitionPoint_mem as ho i).2⟩
  have hjSpec:=m.R_spec ⟨hjHigh,(partitionPoint_mem as ho j).2⟩
  rw [←hiSpec,←hjSpec] at herr
  change physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) j-
    physicalPathSecondMoment (n+1) (sampleClockSteps m.q 0 as) (m.q 0) i≤
      a.radiusS (m.R (partitionPoint 0 as j))-a.radiusS (m.R (partitionPoint 0 as i))+
        2*(mesh*(2*ClockTree.errorJetVariation 2 0 0*
          clockVariationBound (physicalFeatureCoordinateBound n) m.q)) at herr
  exact herr.trans (add_le_add hinc le_rfl)

end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
