module

public import ComparisonSignedCavityScalarRadiusRowAllocation
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyRetainedGammaPhysicalSources

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_actual_generated_scalar_radius_row_bound_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcu : 0 ≤ cu) {S : Type} {as : List PositiveMass}
    (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) (hmesh : 0 ≤ mesh) (hmeshxs : mesh ≤ M.xs)
    {i star U k : ℕ} {seed : List NativeResourceMark} {T : ClockTree S as}
    {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P) (hi : i ≤ star)
    {v : ℝ} (hxv : M.xs ≤ v) (hzv : M.z ≤ v)
    (hstar : M.R (partitionPoint 0 as star) ≤ v/2) :
    ((T.markedAttach 0).map (fun p=>|p.coeff| *
      M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))*
      nativeTargetOffDiagonalProfile T P.live.test.target (nativeRadiusRowBand M.R as v) p)).sum ≤
      2*(2*cu+1)*v^2 := by
  let f:=nativeRadiusRowBand M.R as v
  let s:=P.live.test.target
  have hv : 0 < v:=M.hxs.trans_le hxv
  have hzero : ∀c:T.Slot,c≠s → f (T.splitIndex s c)=0:=by
    intro c hc
    have hsplit : T.splitIndex s c ≤ star:=
      le_of_not_gt (fun H=>hc ((hP.targetStarSingleton hi) c H))
    have HR:=M.R_monotone (partitionPoint_mono as ho hsplit)
    unfold f nativeRadiusRowBand
    split_ifs with hband
    · linarith [hband.1]
    · rfl
  have Habs (p : MarkedPlacement T) :
      |M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark))|=
        M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark)):=
    abs_of_nonneg (M.R_bounds _).1
  have Hrow:=native_target_weighted_profile_le T s ho f (nativeRadiusRowBand_nonneg _ _ _) hzero
    (fun p=>M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark))) (C:=2*v) (by
      intro p hp hne hf
      have hband : v ≤ M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark)) ∧
          M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark)) ≤ 2*v:=by
        unfold f nativeRadiusRowBand at hf
        split_ifs at hf with hband
        · exact hband
        · exact (hf rfl).elim
      rw [Habs]
      exact hband.2)
  simp only [Habs] at Hrow
  have HB:=actual_minimum_radius_band_edgeBudget_le_high_only M hcu hv.le hzv as ho he hm hmesh
  have Hb : edgeBudget 0 as f ≤ (2*cu+1)*v:=HB.trans (by linarith [hmeshxs,hxv])
  exact Hrow.trans (by nlinarith [mul_le_mul_of_nonneg_left Hb (show 0 ≤ 2*v by positivity)])

theorem actual_minimum_scalar_radius_row_on_every_final_net_high_only
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hcu : 0 ≤ cu)
    (us : List PositiveMass) (hus : ∀u∈us,u.val ≤ 1) :
    ∀ᶠjGrid : ℕ in atTop,
      let as:=finiteCutMasses us jGrid
      ∀{S : Type} (i star U : ℕ) (T : ClockTree S as) (seed : List NativeResourceMark)
        (depth : ℕ) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed depth T P → i ≤ star →
      ∀v : ℝ,M.xs ≤ v → M.z ≤ v → M.R (partitionPoint 0 as star) ≤ v/2 →
        ((T.markedAttach 0).map (fun p=>|p.coeff| *
          M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))*
          nativeTargetOffDiagonalProfile T P.live.test.target (nativeRadiusRowBand M.R as v) p)).sum ≤
          2*(2*cu+1)*v^2 := by
  filter_upwards [uniformMasses_mesh_tendsto.eventually (gt_mem_nhds M.hxs)] with jGrid hj
  dsimp only
  intro S i star U T seed depth P hP hi v hxv hzv hstar
  exact native_actual_generated_scalar_radius_row_bound_high_only M hcu
    (finiteCutMasses_ordered us hus jGrid) (finiteCutMasses_end us hus jGrid)
    (finiteCutMasses_mesh us hus jGrid) (by positivity) hj.le hP hi hxv hzv hstar

end OAI.SKFluctuations.Cavity
