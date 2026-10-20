module

public import ComparisonActualHighWallThetaZeroTraceMeasure
public import ComparisonActualHighWallThetaZeroCapOscillation
public import ComparisonActualHighWallCriticalBroadTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
namespace ActualThetaZeroOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : Q.Potential} (cap : ShiftedCapInterval Q P)

theorem localized_measure_eventually_positive_origin
    (hN : 1≤Q.data.N) (hlog : 1≤Real.log Q.data.N) (hnd : 1/Q.data.N≤Q.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ag zg : ℝ} (hag : Q.data.rmin≤ag) (hzg : zg≤1)
    (hoverlap : max cap.left ag < min cap.right zg)
    (hboundary : (P.H cap.left=0 ∨ cap.left=Q.data.rmin) ∧ (P.H cap.right=0 ∨ cap.right=1))
    (A : Set ℝ) (hAcap : A⊆Ioo cap.left cap.right) (hAgroup : A⊆Ioo ag zg)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ε : ℝ} (hε : 0<ε) :
    let F:=(n+1:ℝ)*(((1/3)/Real.log Q.data.N)*laplaceComparisonStrength Q.data.d Q.lam zg)
    ∀ᶠj in atTop,(Q.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j)).real A≤
      (9*Real.log Q.data.N)*(cap.right-cap.left+Q.data.rmin)/F+ε := by
  dsimp only
  let N:=Q.data.N
  let d:=Q.data.d
  let lam:=Q.lam
  let left:=cap.left
  let z:=cap.right
  have ha : Q.data.rmin≤left:=cap.hleft
  have haz : left<z:=cap.hlt
  have hz : z≤1:=cap.hright
  let m:=Q.shiftedNativeModel
  let clock:=m.q
  let S:=Q.radiusS
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam zg)
  let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) clock
  let bound := (9*Real.log N)*(z-left+Q.data.rmin)/F
  let lo := max left ag
  let hi := min z zg
  let η := min ((hi-lo)/4) (ε/8)
  let p := lo+η
  let q := hi-η
  have hη : 0<η := lt_min (by dsimp [hi,lo]; linarith) (by positivity)
  have hηLen : η≤(hi-lo)/4 := min_le_left _ _
  have hηε : η≤ε/8 := min_le_right _ _
  have hloA : left≤lo := le_max_left _ _
  have hloG : ag≤lo := le_max_right _ _
  have hhiZ : hi≤z := min_le_left _ _
  have hhiG : hi≤zg := min_le_right _ _
  have hp : p∈Ioo left z := by dsimp only [p]; constructor <;> linarith
  have hq : q∈Ioo left z := by dsimp only [q]; constructor <;> linarith
  have hpq : p≤q := by dsimp only [p,q]; linarith
  have hF : 0<F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d Q.hlam zg))
  have hbound : 0≤bound := by
    dsimp [bound]
    exact div_nonneg (mul_nonneg (by linarith : 0≤9*Real.log N) (by linarith [Q.data.hrbounds.1] : 0≤z-left+Q.data.rmin)) hF.le
  have hinc : S q-S p≤(9*Real.log N)*(z-left+Q.data.rmin) := by
    have H:=cap.radiusS_increment_with_origin hN hlog hnd hboundary.1 hboundary.2 hp hq hpq
    have hw:(if cap.left=Q.data.rmin then Q.data.rmin else 0)≤Q.data.rmin:=by
      split_ifs <;> linarith [Q.data.hrbounds.1]
    have hwlog:Q.data.rmin≤9*Real.log N*Q.data.rmin:=by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (by linarith : (1:ℝ)≤9*Real.log N) Q.data.hrbounds.1.le
    dsimp only [S,left,z] at H ⊢
    nlinarith only [H,hw,hwlog]
  have herror : Tendsto (fun j=>2*(mesh j*Cnode)/F+2*(mesh j/m.c)) atTop (𝓝 0) := by
    convert (((hlim.mul_const Cnode).const_mul 2).div_const F).add
      ((hlim.div_const m.c).const_mul 2) using 1 <;> simp
  have herr := herror.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2))
  have hCn : 0≤Cnode := mul_nonneg
    (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg (physicalFeatureCoordinateBound n) clock
      (completedPathClock_monotone (n+1) m.hbf m.hhf))
  filter_upwards [herr] with j hj
  let μ:=m.radiusMeasure dphys e (as j) (ho j)
  let error := 2*(mesh j*Cnode)/F+2*(mesh j/m.c)
  have hmeshj := hmesh0 j
  have hc:=m.hc
  have herror0 : 0≤error := by dsimp [error]; positivity
  have hinterval := Q.radiusMeasure_interval_le_fixedStrength hN hlog hnd dphys e
    (as j) (ho j) (hend j) (hmesh j) (hmesh0 j) (by dsimp [p]; linarith) hpq
    (by dsimp [q]; linarith) hzg
  have hinner : μ (Ioo p q)≤ENNReal.ofReal bound+ENNReal.ofReal error := by
    exact hinterval.trans (add_le_add (ENNReal.ofReal_le_ofReal
      (div_le_div_of_nonneg_right hinc hF.le)) le_rfl)
  have hinnerReal : μ.real (Ioo p q)≤bound+error := by
    have ht := ENNReal.toReal_mono (by finiteness) hinner
    rw [ENNReal.toReal_add (by finiteness) (by finiteness),
      ENNReal.toReal_ofReal hbound,ENNReal.toReal_ofReal herror0] at ht
    exact ht
  have hdom : μ≤volume:=m.radiusMeasure_le_volume dphys e (as j) (ho j)
  have hwhole := radius_measure_open_le_inner hdom
    (by dsimp [p]; linarith : lo≤p) hpq (by dsimp [q]; linarith : q≤hi)
  have hAsub : A⊆Ioo lo hi := by
    intro r hr
    exact ⟨max_lt ((hAcap hr).1) ((hAgroup hr).1),lt_min ((hAcap hr).2) ((hAgroup hr).2)⟩
  have hreal : μ.real (Ioo lo hi)≤bound+ε := by
    dsimp only [p,q] at hwhole
    dsimp only [error] at hinnerReal
    linarith
  exact (measureReal_mono hAsub).trans hreal

end ActualThetaZeroOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
