module

public import RadiusIntervalExhaustion
public import PhysicalComparisonTraceFixedStrength
public import VariableEndpointComparisonCaps

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonPhysicalWholeCapTrace_eventually
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {a z : ℝ} (ha : 0 ≤ a) (haz : a < z) (hz : z ≤ 1)
    (haH : H a=0) (hzH : H z=0) (hneg : ∀r∈Ioo a z,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α
        (as j) (ho j) (Ioo a z) ≤ ENNReal.ofReal ((9*Real.log N)*(z-a)/F+ε) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let clock := completedPathClock (n+1) bf hf
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) clock
  let bound := (9*Real.log N)*(z-a)/F
  let η := min ((z-a)/4) (ε/8)
  let p := a+η
  let q := z-η
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  have hηLen : η ≤ (z-a)/4 := min_le_left _ _
  have hηε : η ≤ ε/8 := min_le_right _ _
  have hp : p∈Ioo a z := by dsimp only [p];constructor <;> linarith
  have hq : q∈Ioo a z := by dsimp only [q];constructor <;> linarith
  have hpq : p ≤ q := by dsimp only [p,q];linarith
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hbound : 0 ≤ bound := div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hlog0)
    (sub_nonneg.mpr haz.le)) hF.le
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h
    hd.ne' hlam.le hlb hb hh hh0 α
  have hCn : 0 ≤ Cnode := mul_nonneg
    (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg (physicalFeatureCoordinateBound n) clock
      (completedPathClock_monotone (n+1) (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)))
  have hinc : S q-S p ≤ (9*Real.log N)*(z-a) :=
    (actual_variableEndpoint_comparison_cap_interior_geometry hc hk hkc hm hM
      hN hlog hd hnd hlam hld (n+1) (by omega) b h hb hlb hh hh0 α H J hH hJ hD
      ha hz hp hq hpq haH hzH (hneg p hp) (hneg q hq)).1
  have herror : Tendsto (fun j=>2*(mesh j*Cnode)/F+2*(mesh j/c)) atTop (𝓝 0) := by
    convert (((hlim.mul_const Cnode).const_mul 2).div_const F).add
      ((hlim.div_const c).const_mul 2) using 1 <;> simp
  have herr := herror.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2))
  filter_upwards [herr] with j hj
  let μ := comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j)
  let error := 2*(mesh j*Cnode)/F+2*(mesh j/c)
  have hmeshj : 0 ≤ mesh j := hmesh0 j
  have herror0 : 0 ≤ error := by dsimp only [error];positivity
  have hinterval := comparisonPhysicalRadiusMeasure_interval_le_fixedStrength hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α (as j) (ho j) (hend j)
    (hmesh j) (hmesh0 j) (ha.trans_lt hp.1) hpq hq.2.le hz
  have hinner : μ (Ioo p q) ≤ ENNReal.ofReal bound+ENNReal.ofReal error := by
    apply hinterval.trans
    apply add_le_add
    · exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hinc hF.le)
    · exact le_rfl
  have hinnerReal : μ.real (Ioo p q) ≤ bound+error := by
    have ht := ENNReal.toReal_mono (by finiteness) hinner
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_ofReal hbound,ENNReal.toReal_ofReal herror0] at ht
    exact ht
  have hdom : μ ≤ volume :=
    (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM n dphys e d lam b h α
      (as j) (ho j)).trans Measure.restrict_le_self
  have hwhole := radius_measure_open_le_inner hdom hp.1.le hpq hq.2.le
  have hreal : μ.real (Ioo a z) ≤ bound+ε := by
    dsimp only [error] at hinnerReal
    dsimp only [p,q] at hwhole
    linarith
  exact (ENNReal.le_ofReal_iff_toReal_le (by finiteness) (by positivity : 0 ≤ bound+ε)).mpr hreal
end
end OAI.SKFluctuations.LaplaceWindowFormalization
