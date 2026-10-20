module

public import ComparisonActualHighWallSlowWindowData
public import ComparisonSignedCavitySharpOriginalLowRadiusAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

 theorem eventually_actual_high_wall_star_original_second_moment_along
    {m delta cl cu Az C0 Ct D Bclock L Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow
      (M n) (M n).data.d L Cs (w n)) :
    ∀ᶠn in atTop,∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
      ∀ᶠj in atTop,
        nativeRetainedCenteredMoment (dim n) 1 (M n).bf (M n).hf (finiteCutMasses us j)
          (w n).star.val (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val) ≤
          (M n).data.N^(-(actualMassSavingExponent m delta/8))*(M n).data.d^2 := by
  let eta:=actualMassSavingExponent m delta
  have heta : 0 < eta:=actualMassSavingExponent_pos hm hdelta
  have Hcoef:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=2) (d:=1) (q:=-eta/4) (r:=-eta/8)
      zero_lt_one (by linarith))
  filter_upwards [hw,Hcoef] with n hn hnCoef
  intro us hus hstar
  have Hlimit:=nativeRetainedCenteredMoment_one_tendsto (dim n) (M n).bf (M n).hf
    ((M n).data.bf_monotone (M n).alpha) ((M n).data.hf_monotone (M n).alpha)
    us hus (w n).star hstar
  obtain ⟨P,hi,hblocks,hq,hqlow,htotal,hNodes,hstarBand,hH,hThermal,hSlo,hShi,
    hRlo,hRhi,hxs,hz,hK,hGap,hosc⟩:=hn
  let target:=(M n).data.N^(-eta/4)*(M n).data.d^2
  have hd:=(M n).data.hd
  have htarget : 0 < target:=by dsimp only [target];positivity [(M n).data.hN]
  have hThermalTarget : orderedPathB (dim n+1) (M n).bf (M n).hf (w n).star.val-
      (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val)^2 ≤ target:=by
    simpa only [target,eta,neg_div] using hThermal
  have hgap : orderedPathB (dim n+1) (M n).bf (M n).hf (w n).star.val-
      (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val)^2 < 2*target:=
    hThermalTarget.trans_lt (by linarith only [htarget])
  have Hfine:=Hlimit.eventually (eventually_le_nhds hgap)
  filter_upwards [Hfine] with j hj
  apply hj.trans
  have Hmul:=mul_le_mul_of_nonneg_right hnCoef (sq_nonneg (M n).data.d)
  simpa only [target,ActualHighWallData.N,one_mul,mul_assoc,Function.comp_apply,eta,neg_div] using Hmul

end OAI.SKFluctuations.Cavity
