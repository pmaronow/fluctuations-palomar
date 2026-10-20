module

public import ComparisonActualHighWallSlowWindowProducerAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 10000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

def weakenRadiusUpper
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (Az' : ℝ) (hAz : Az ≤ Az') :
    ActualHighWallOverlapMinimum n m delta cl cu Az' C0 Ct D Bclock where
  data:=M.data
  alpha:=M.alpha
  minimum:=M.minimum
  xs:=M.xs
  z:=M.z
  hxs:=M.hxs
  hscale:=M.hscale
  hsxs:=M.hsxs
  hz:=M.hz
  hzxs:=M.hzxs.trans (mul_le_mul_of_nonneg_right hAz M.hxs.le)
  hdD:=M.hdD
  hupper:=M.hupper
  hlower:=M.hlower
  htest:=M.htest
  regular:=M.regular
  hT:=M.hT

@[simp] theorem weakenRadiusUpper_data
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (Az' : ℝ) (hAz : Az ≤ Az') : (M.weakenRadiusUpper Az' hAz).data=M.data:=rfl
@[simp] theorem weakenRadiusUpper_alpha
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (Az' : ℝ) (hAz : Az ≤ Az') : (M.weakenRadiusUpper Az' hAz).alpha=M.alpha:=rfl
@[simp] theorem weakenRadiusUpper_xs
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (Az' : ℝ) (hAz : Az ≤ Az') : (M.weakenRadiusUpper Az' hAz).xs=M.xs:=rfl
@[simp] theorem weakenRadiusUpper_z
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (Az' : ℝ) (hAz : Az ≤ Az') : (M.weakenRadiusUpper Az' hAz).z=M.z:=rfl
@[simp] theorem weakenRadiusUpper_bf
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (Az' : ℝ) (hAz : Az ≤ Az') : (M.weakenRadiusUpper Az' hAz).bf=M.bf:=rfl
@[simp] theorem weakenRadiusUpper_hf
    (M : ActualHighWallOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (Az' : ℝ) (hAz : Az ≤ Az') : (M.weakenRadiusUpper Az' hAz).hf=M.hf:=rfl

theorem exists_star_mass_constant_for_clock_room
    {T0 C : ℝ} (hT0 : 0 < T0) (hcu : 0 < cu) :
    ∃Az' : ℝ,Az ≤ Az' ∧ 0 ≤ Az' ∧
      2*C ≤ 3*T0*(starMassBandConstant cu Az'/cu)/8 := by
  let Az':=max (max Az 0) (16*C/(3*T0))
  have hAA : Az ≤ Az':=(le_max_left _ _).trans (le_max_left _ _)
  have hAp : 0 ≤ Az':=(le_max_right _ _).trans (le_max_left _ _)
  have hAroom : 16*C ≤ Az'*(3*T0):=
    (div_le_iff₀ (by positivity : 0 < 3*T0)).mp (le_max_right _ _)
  have Hc : starMassBandConstant cu Az'/cu=1/cu+Az':=by
    unfold starMassBandConstant
    field_simp
  refine ⟨Az',hAA,hAp,?_⟩
  rw [Hc]
  nlinarith only [hAroom,mul_pos hT0 (one_div_pos.mpr hcu)]

theorem calibrated_slow_window_clock_lower
    {n : ℕ} (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {W L Cs : ℝ} {w : ActualSlowWindowChoice}
    (Hw : M.IsActualHighWallCalibratedSlowWindow W L Cs w) :
    3*M.data.T*(starMassBandConstant cu Az/cu)/8*W ≤
      actualMixedClock (n+1) M.bf M.hf w.star.val := by
  obtain ⟨P,hi,hblocks,hq,hqlow,htotal,hNodes,hstar,hH,hThermal,hSlo,hShi,
    hRlo,hRhi,hxs,hz,hK,hGap,hosc⟩:=Hw
  exact hK

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
