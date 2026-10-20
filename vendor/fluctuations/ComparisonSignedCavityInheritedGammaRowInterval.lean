module

public import ComparisonSignedCavityInheritedContinuumGammaRadius
public import ComparisonSignedCavityRadiusRowInterval

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity ClockTree

theorem eventually_actual_minimum_inherited_gamma_radius_row_bound
    (Bclock Temp Cf : ℝ) (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cg : ℝ,0 < Cg ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        ∀(i star U : ℕ) (T : ClockTree (Spin n×Bool) as)
          (seed : List NativeResourceMark) (depth : ℕ) (P : NativeResourceTerm i star T),
          NativeActualResourceGenerated i star U seed depth T P → i ≤ star → 0 < U →
        ∀v : ℝ,M.xs ≤ v → M.z ≤ v → M.R (partitionPoint 0 as star) ≤ v/2 →
          ((T.markedAttach 0).map (fun p=>|p.coeff| *
            |fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as)
              (p.embed P.live.test.target) p.mark| *
            nativeTargetOffDiagonalProfile T P.live.test.target (nativeRadiusRowBand M.R as v) p)).sum ≤
            Cg*v^2 := by
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_inherited_continuum_scalar_gamma_radius_bound
    (D:=D) Bclock Temp Cf hT hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨2*Cg*(2*cu+1),by positivity,?_⟩
  filter_upwards [HG] with n hn
  intro M hsource _hxs L us hus _hret _hmesh
  have Hmesh:=uniformMasses_mesh_tendsto.eventually (gt_mem_nhds M.hxs)
  filter_upwards [Hmesh] with k hkmesh
  dsimp only
  intro i star U T seed depth P hP hi hU v hxv hzv hstar
  let as:=finiteCutMasses us k
  let f:=nativeRadiusRowBand M.R as v
  let s:=P.live.test.target
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hv : 0 < v:=M.hxs.trans_le hxv
  have hzero : ∀c:T.Slot,c≠s → f (T.splitIndex s c)=0 := by
    intro c hc
    have hsplit : T.splitIndex s c ≤ star:=
      le_of_not_gt (fun H=>hc ((hP.targetStarSingleton hi) c H))
    have HR:=comparisonSweepQuantile_monotone M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha (partitionPoint_mono as ho hsplit)
    unfold f nativeRadiusRowBand
    split_ifs with hband
    · linarith [hband.1]
    · rfl
  have Hrow:=native_target_weighted_profile_le T s ho f
    (nativeRadiusRowBand_nonneg _ _ _) hzero
    (fun p=>fullScalarCutGamma p.tree U (nativeContinuumMixedClock n M.bf M.hf as) (p.embed s) p.mark)
    (C:=2*Cg*v) (by
      intro p hp hne hf
      have hband : v ≤ M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark)) ∧
          M.R (partitionPoint 0 as (p.tree.splitIndex (p.embed s) p.mark)) ≤ 2*v := by
        unfold f nativeRadiusRowBand at hf
        split_ifs at hf with hband
        · exact hband
        · exact (hf rfl).elim
      have H:=hn M hsource as ho p.tree U hU (p.embed s) p.mark hne (hxv.trans hband.1) (hzv.trans hband.1)
      exact H.trans (by nlinarith [mul_le_mul_of_nonneg_left hband.2 hCg.le]))
  have Hbudget:=actual_minimum_radius_band_edgeBudget_le M hcu.le hv.le hzv as ho
    (finiteCutMasses_end us hus k) (finiteCutMasses_mesh us hus k) (by positivity)
  have Hb : edgeBudget 0 as f ≤ (2*cu+1)*v := by
    exact Hbudget.trans (by linarith [hkmesh,hxv])
  exact Hrow.trans (by nlinarith [mul_le_mul_of_nonneg_left Hb (show 0 ≤ 2*Cg*v by positivity)])

end OAI.SKFluctuations.LaplaceWindowFormalization
