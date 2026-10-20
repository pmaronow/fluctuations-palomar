module

public import ComparisonSignedCavityActualInitialFullResidualPrefixSource
public import ComparisonSignedCavityActualOriginalTargetGapFromFullResidual

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem ActualInitialResidualFullModulusOnStrongCutsAlong.to_retained_targets
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}
    {depth : ℕ} {A Atarget Ci : ℝ} {err : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice} {high outer : ℕ→PositiveMass}
    (H : ActualInitialResidualFullModulusOnStrongCutsAlong depth A Ci err M W w high outer)
    (hA : Atarget ≤ A) :
    ActualInitialFullResidualOnRetainedTargetsAlong depth Atarget Ci err M W w high outer := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar hhigh houter hnodes
  filter_upwards [hn L us hus hret hmesh hstar hhigh houter hnodes] with jGrid hj
  dsimp only at hj ⊢
  intro i hi hs hU hmass
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have hilen:i ≤ as.length:=hi.le.trans (hs.le.trans hU)
  obtain ⟨pre,mid,tail,hparts,hpre,hindex,hmid⟩:=
    native_actual_initial_retained_target_prefix_split as i star hi (hs.le.trans hU)
  have hmass':partitionPoint 0 as pre.length ≤ A*(M n).xs := by
    rw [hpre]
    exact hmass.trans (mul_le_mul_of_nonneg_right hA (M n).hxs.le)
  obtain ⟨hs',hU',Hbound⟩:=hj pre mid tail hparts hindex hmid hmass'
  have Hsource:=native_actual_initial_full_residual_reindex (M n) (W:=W n) (depth:=depth)
    hparts hpre hindex hs' hs hU' hU (by omega) hilen
  rw [Hsource] at Hbound
  simpa only [hpre] using Hbound

end OAI.SKFluctuations.Cavity
