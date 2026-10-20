module

public import ComparisonSignedCavityActualSharpStarFinalNet

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy NativeStarBuffer NativeOverlapMinimum
set_option maxHeartbeats 6000000

theorem eventually_actual_sharp_star_second_moment_final_net_along
    {m delta cl cu Az C0 Ct D Bclock T L Cs : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW : ∀n,0 < W n) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) :
    ∀ᶠn : ℕ in atTop,
      ∀us : List PositiveMass,(∀u∈us,u.val≤1) → (w n).star∈us →
      ∀ᶠj : ℕ in atTop,
        nativeRetainedCenteredMoment (dim n) 1 (M n).bf (M n).hf (finiteCutMasses us j)
          (w n).star.val (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val) ≤
          (M n).context.N^(-(actualMassSavingExponent m delta/8))*((M n).xs^4/(W n)^2) := by
  let eta := actualMassSavingExponent m delta
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have Hcoef := ((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=2) (d:=1) (q:=-(eta/4)) (r:=-(eta/8))
      zero_lt_one (by linarith))
  filter_upwards [hw,Hcoef] with n hn hncoef
  intro us hus hstar
  have had := comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have Hlimit := nativeRetainedCenteredMoment_one_tendsto (dim n) (M n).bf (M n).hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) us hus (w n).star hstar
  let target := (M n).context.N^(-(eta/4))*((M n).xs^4/(W n)^2)
  have hxs := (M n).hxs
  have hWn := hW n
  have htarget : 0 < target := by dsimp only [target];positivity
  have hgap : orderedPathB (dim n+1) (M n).bf (M n).hf (w n).star.val-
      (orderedPathS (dim n+1) (M n).bf (M n).hf (w n).star.val)^2 < 2*target := by
    exact hn.2.trans_lt (by linarith only [htarget])
  have Hfine := Hlimit.eventually (eventually_le_nhds hgap)
  filter_upwards [Hfine] with j hj
  apply hj.trans
  have Hmul := mul_le_mul_of_nonneg_right hncoef
    (show 0 ≤ (M n).xs^4/(W n)^2 by positivity)
  simpa only [target,NativeOverlapContext.N,one_mul,mul_assoc,Function.comp_apply] using Hmul

end OAI.SKFluctuations.LaplaceWindowFormalization
