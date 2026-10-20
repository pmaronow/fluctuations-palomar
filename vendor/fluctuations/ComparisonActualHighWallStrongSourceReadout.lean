module

public import ComparisonActualHighWallStrongSourceMassesAlong
public import ComparisonSignedCavityActualSharpSourceCutReadout
public import ComparisonActualHighWallSlowWindowData

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000

 theorem actual_high_wall_calibrated_star_mass_mem_band
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock W L Cs : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {w : ActualSlowWindowChoice}
    (H : ActualHighWallOverlapMinimum.IsActualHighWallCalibratedSlowWindow M W L Cs w) :
    w.star.val ∈ Icc (calibratedBandStart cu Az*W) ((calibratedBandStart cu Az+4*L)*W) := by
  obtain ⟨P,hi,hblocks,hq,hqlow,htotal,hNodes,hstar,hH,hThermal,hSlo,hShi,
    hRlo,hRhi,hxs,hz,hK,hGap,hosc⟩:=H
  have hblock:=calibrated_mass_central_subset hq.le (calibrated_mass_middle_subset hq.le hstar)
  exact calibrated_mass_block_subset hq.le hi htotal hblock

 theorem ActualHighWallStrongSourceMasses.retained_source_geometry
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock Cmass Ccut Cx c Rmacro : ℝ}
    {M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {source outer : PositiveMass}
    (H : ActualHighWallStrongSourceMasses M Cmass Ccut Cx c Rmacro source outer)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (star : PositiveMass)
    (hs : star∈as) (hsource : source∈as) (houter : outer∈as)
    (hmass : star.val ≤ Cmass*M.data.d) :
    let i:=retainedMassPrefixIndex star.val as
    let U:=retainedMassPrefixIndex source.val as
    let V:=retainedMassPrefixIndex outer.val as
    0 < i ∧ i < U ∧ U < V ∧ V ≤ as.length ∧
      partitionPoint 0 as i=star.val ∧ partitionPoint 0 as U=source.val ∧
      partitionPoint 0 as V=outer.val ∧
      partitionPoint 0 as U ≤ Ccut*M.data.d ∧
      partitionPoint 0 as V ≤ (Ccut+1)*M.data.d ∧
      M.data.s ≤ partitionPoint 0 as U ∧
      4*M.data.d ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U) ∧
      M.z ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) ∧
      M.data.wallRadius M.alpha (partitionPoint 0 as 0) ≤
        min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) ∧
      M.data.wallRadius M.alpha (partitionPoint 0 as i) ≤
        min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4) := by
  dsimp only
  have Hi:=nativeRetainedCut_partitionPoint as ho star hs
  have HU:=nativeRetainedCut_partitionPoint as ho source hsource
  have HV:=nativeRetainedCut_partitionPoint as ho outer houter
  have hi0 : 0 < retainedMassPrefixIndex star.val as:=by
    by_contra hn
    have hz : retainedMassPrefixIndex star.val as=0:=by omega
    rw [hz] at Hi
    simp only [partitionPoint,partitionValues_zero,id_eq] at Hi
    exact (ne_of_gt star.property) Hi.symm
  have Hsi:=actual_retained_mass_strict_index as ho star source hs hsource
    (hmass.trans_lt H.low_lt_source)
  have HUV:=actual_retained_mass_strict_index as ho source outer hsource houter H.source_lt_outer
  refine ⟨hi0,Hsi,HUV,retainedMassPrefixIndex_le_length outer.val as,Hi,HU,HV,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [HU];exact H.source_upper
  · rw [HV];exact H.outer_upper
  · rw [HU];exact H.above_wall
  · rw [HU];exact H.high_radius
  · rw [HU];exact H.seed_radius
  · rw [HU]
    exact H.low_radius _ (partitionPoint_mem as ho 0) (by
      simp only [partitionPoint,partitionValues_zero,id_eq]
      exact star.property.le.trans hmass)
  · rw [HU]
    exact H.low_radius _ (partitionPoint_mem as ho _) (by simpa only [Hi] using hmass)

end OAI.SKFluctuations.Cavity
