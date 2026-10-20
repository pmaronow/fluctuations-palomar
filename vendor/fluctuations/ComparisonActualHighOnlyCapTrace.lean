module

public import ComparisonActualHighOnlyCapOscillation
public import ComparisonActualHighOnlyTraceMeasure
public import ComparisonShiftedNativeTraceLimit
public import ComparisonCapSideTraceLocalizedBroad

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000
set_option linter.unnecessarySeqFocus false
namespace ActualHighOnlyOverlapMinimum.ShiftedCapInterval
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    {P : a.Potential} (cap : ShiftedCapInterval a P)

theorem localized_measure_eventually
    (hN : 1≤a.data.N) (hlog : 1≤Real.log a.data.N) (hnd : 1/a.data.N≤a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ag zg : ℝ} (hag : 0<ag) (hzg : zg≤1)
    (hoverlap : max cap.left ag < min cap.right zg)
    (hboundary : (P.H cap.left=0 ∨ cap.left=0) ∧ (P.H cap.right=0 ∨ cap.right=1))
    (A : Set ℝ) (hAcap : A⊆Ioo cap.left cap.right) (hAgroup : A⊆Ioo ag zg)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ε : ℝ} (hε : 0<ε) :
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam zg)
    ∀ᶠj in atTop,(a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j)).real A≤
      (9*Real.log a.data.N)*(cap.right-cap.left)/F+ε := by
  dsimp only
  let N:=a.data.N
  let d:=a.data.d
  let lam:=a.lam
  let left:=cap.left
  let z:=cap.right
  have ha : 0≤left:=cap.hleft
  have haz : left<z:=cap.hlt
  have hz : z≤1:=cap.hright
  let m:=a.shiftedNativeModel
  let clock:=m.q
  let S:=a.radiusS
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam zg)
  let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) clock
  let bound := (9*Real.log N)*(z-left)/F
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
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d a.hlam zg))
  have hbound : 0≤bound := by dsimp [bound]; positivity
  have hinc : S q-S p≤(9*Real.log N)*(z-left) :=
    cap.radiusS_increment_all hN hlog hnd hboundary.1 hboundary.2 hp hq hpq
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
  have hinterval := a.radiusMeasure_interval_le_fixedStrength hN hlog hnd dphys e
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

end ActualHighOnlyOverlapMinimum.ShiftedCapInterval
end OAI.SKFluctuations.LaplaceWindowFormalization
