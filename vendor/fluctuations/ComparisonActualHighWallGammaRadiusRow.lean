module

public import ComparisonActualHighWallContinuumGammaRadius
public import ComparisonSignedCavityRadiusRowInterval
public import ComparisonSignedCavityInheritedGammaRowInterval

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity ClockTree
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable

theorem actual_high_wall_radius_band_edgeBudget_le
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hwork : M.xs=M.data.d) (hcu : 0 ≤ cu) {mesh v : ℝ} (hxv : M.xs ≤ v) (hzv : M.z ≤ v)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1) (hm : PartitionMesh mesh 0 as) (hmesh : 0 ≤ mesh) :
    edgeBudget 0 as (nativeRadiusRowBand (M.data.wallRadius M.alpha) as v) ≤ 2*cu*v+mesh := by
  have hv : 0<v:=M.hxs.trans_le hxv
  have H:=native_edgeBudget_supported_mass_le as ho he hm
    (nativeRadiusRowBand (M.data.wallRadius M.alpha) as v) (nativeRadiusRowBand_nonneg _ _ _)
    (nativeRadiusRowBand_le_one _ _ _) (B:=2*cu*v) (by
      intro j hj
      unfold nativeRadiusRowBand
      split_ifs with hband
      · let u:=partitionPoint 0 as j
        let r:=M.data.wallRadius M.alpha u
        have hr:=M.data.wallRadius_bounds M.alpha u
        have hmin : M.data.rmin<r:=by
          have H:=M.data.hrbounds.2.1
          have Hd : M.data.d ≤ v:=by rwa [hwork] at hxv
          nlinarith only [H,Hd,hband.1,M.data.hd]
        have hhigh : M.data.s ≤ u:=(M.data.wallRadius_high_mass M.alpha hmin).le
        have Hreg:=(M.regular r ⟨hzv.trans hband.1,hr.2⟩).2
        rw [M.data.wallRadius_spec M.alpha ⟨hhigh,(partitionPoint_mem as ho j).2⟩] at Hreg
        have Hcap:=mul_le_mul_of_nonneg_left hband.2 hcu
        nlinarith only [Hreg,Hcap,hj]
      · rfl)
  simpa only [sub_zero,max_eq_left (by positivity : 0 ≤ 2*cu*v+mesh)] using H

theorem eventually_actual_high_wall_gamma_radius_row_bound
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct) :
    ∃Cg : ℝ,0<Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as)
          (seed : List NativeResourceMark) (depth : ℕ) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed depth T P → i  ≤  star → 0<U →
        ∀v : ℝ,M.xs ≤ v → M.z ≤ v → M.data.wallRadius M.alpha (partitionPoint 0 as star) ≤ v/2 →
        ((T.markedAttach 0).map (fun p=>|p.coeff| *
          |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as)
            (p.embed P.live.test.target) p.mark| *
          nativeTargetOffDiagonalProfile T P.live.test.target
            (nativeRadiusRowBand (M.data.wallRadius M.alpha) as v) p)).sum ≤ Cg*v^2 := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_high_wall_continuum_scalar_gamma_radius_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*Cg*(2*cu+1),by positivity,?_⟩
  filter_upwards [HG] with n hn
  intro M hwork us hus
  have Hmesh:=uniformMasses_mesh_tendsto.eventually (gt_mem_nhds M.hxs)
  filter_upwards [Hmesh] with jGrid hmesh
  dsimp only
  intro i star U T seed depth P hP hi hU v hxv hzv hstar
  let as:=finiteCutMasses us jGrid
  let f:=nativeRadiusRowBand (M.data.wallRadius M.alpha) as v
  let s:=P.live.test.target
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hv : 0<v:=M.hxs.trans_le hxv
  have hzero : ∀c:T.Slot,c≠s → f (T.splitIndex s c)=0:=by
    intro c hc
    have hsplit : T.splitIndex s c ≤ star:=le_of_not_gt (fun H=>hc ((hP.targetStarSingleton hi) c H))
    have HR:=M.data.wallRadius_monotone M.alpha (partitionPoint_mono as ho hsplit)
    unfold f nativeRadiusRowBand
    split_ifs with hband
    · linarith only [HR,hstar,hband.1,hv]
    · rfl
  have Hrow:=native_target_weighted_profile_le T s ho f (nativeRadiusRowBand_nonneg _ _ _) hzero
    (fun p=>fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as) (p.embed s) p.mark)
    (C:=2*Cg*v) (by
      intro p hp hne hf
      have hband : v ≤ M.data.wallRadius M.alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark)) ∧
          M.data.wallRadius M.alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark)) ≤ 2*v:=by
        unfold f nativeRadiusRowBand at hf
        split_ifs at hf with hband
        · exact hband
        · exact (hf rfl).elim
      have H:=hn M hwork as ho p.tree U hU (p.embed s) p.mark hne
        (hxv.trans hband.1) (hzv.trans hband.1)
      exact H.trans (by nlinarith only [mul_le_mul_of_nonneg_left hband.2 hCg.le]))
  have Hbudget:=actual_high_wall_radius_band_edgeBudget_le M hwork hcu.le hxv hzv as ho
    (finiteCutMasses_end us hus jGrid) (finiteCutMasses_mesh us hus jGrid) (by positivity)
  have Hb : edgeBudget 0 as f ≤ (2*cu+1)*v:=Hbudget.trans (by linarith only [hmesh,hxv])
  exact Hrow.trans (by nlinarith only [mul_le_mul_of_nonneg_left Hb (show 0 ≤ 2*Cg*v by positivity)])

end OAI.SKFluctuations.LaplaceWindowFormalization
