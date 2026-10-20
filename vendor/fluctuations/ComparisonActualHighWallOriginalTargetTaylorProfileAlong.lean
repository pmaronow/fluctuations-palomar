module

public import ComparisonActualHighWallOriginalTargetRestorationProfileAlong
public import ComparisonActualHighWallOriginalConstantTaylorProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_original_target_Taylor_profile_along
    (dOrder : ℕ) (hd : 0< dOrder) (p : ℝ) (hp : 2< p) (hOrder : p/(p-2)≤ (dOrder:ℝ))
    (Bclock Cmass Ccut Rmacro F Cx : ℝ) {eta : ℝ}
    (hCm : 0≤ Cmass) (hCcut : 0≤ Ccut) (hCx : 0< Cx) (heta : 0< eta)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta< 3*m) (hgap : 2*eta< 6*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hmacro : 0< Rmacro) (hRhalf : Rmacro≤ 1/2)
    (hFmass : 1+2*cu≤ F) (hFradius : 1+1/Rmacro≤ F)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop) :
    ∃C : ℝ,0< C ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d→∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤ M.xs→∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      ∀(mid tail : List PositiveMass),as=mid++tail→0< mid.length→
      ∀(U : ℕ),mid.length< U→U≤ as.length→
      partitionPoint 0 as mid.length≤ Cmass*M.data.d→partitionPoint 0 as U≤ Ccut*M.data.d→
      M.data.d≤ Rmacro/2→4*M.data.d≤ M.data.wallRadius M.alpha (partitionPoint 0 as U)→
      M.z≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
      M.data.wallRadius M.alpha (partitionPoint 0 as 0)≤
        min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
      M.data.wallRadius M.alpha (partitionPoint 0 as mid.length)≤
        min (M.data.wallRadius M.alpha (partitionPoint 0 as U)/8) (Rmacro/4)→
      ∀sourceMass : ℝ,∀hsourceMass : 0< sourceMass,
      Cx*M.xs≤ sourceMass→partitionPoint 0 as U=sourceMass→
      (∀j≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us)→
      let g:=nativeFreshAtSlot (single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) mid.length
      let R:=M.data.highErrorEnvelope M.alpha as U
      |actualGeneralTargetOriginalTaylorPart (n:=dim n) M.bf M.hf as mid.length U|≤
        C*(M.data.d^3+M.data.d*(g.tree.forkCost (fun l=> (R l)^(4/p))+edgeBudget 0 as (fun l=> (R l)^(4/p))+
          M.data.d*(g.tree.forkCost R+edgeBudget 0 as R))) := by
  obtain ⟨Cr,hCr,HR⟩:=eventually_actual_high_wall_original_target_restoration_profile_along
    (D:=D) dOrder hd p hp hOrder Bclock Cmass Ccut Rmacro F Cx hCm hCcut hCx heta
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius dim hdim
  obtain ⟨CT,hCT,HT⟩:=eventually_actual_high_wall_original_constant_Taylor_remainder_profile
    (D:=D) 2 dOrder hd p hp hOrder Bclock Ccut hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cr+CT,by positivity,?_⟩
  filter_upwards [HR,hdim.eventually HT] with n hnR hnT
  intro M hwork L us hus hret hmesh
  filter_upwards [hnR M hwork L us hus hret hmesh,hnT M hwork L us hus hret hmesh]
    with jGrid hjR hjT
  dsimp only at hjR hjT ⊢
  intro mid tail hparts hmid U hs hU hmass hcut hsmall hhigh hz hri hrs
    sourceMass hsourceMass hsource hsourceeq hnodes
  have HR0:=hjR mid tail hparts hmid U hs hU hmass hcut hsmall hhigh hz hri hrs
    sourceMass hsourceMass hsource hsourceeq hnodes
  let as:=finiteCutMasses us jGrid
  let T:=single (S:=Spin (dim n)×Bool) as
  let s:=singleSlot (S:=Spin (dim n)×Bool) as
  let g:=nativeFreshAtSlot T 0 s mid.length
  have hg : g.tree.leaves≤2:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 s mid.length)
    simpa only [T,single_leaves_exact] using H
  have HT0:=hjT U g.tree hU hg hcut (g.embed s) g.mark
  have HT' : |actualGeneralTargetRawTaylorRemainder (n:=dim n) M.bf M.hf as mid.length U|≤
      CT*(M.data.d*(g.tree.forkCost (fun l=>(M.data.highErrorEnvelope M.alpha as U l)^(4/p))+
        edgeBudget 0 as (fun l=>(M.data.highErrorEnvelope M.alpha as U l)^(4/p))+
          M.data.d*(g.tree.forkCost (M.data.highErrorEnvelope M.alpha as U)+
            edgeBudget 0 as (M.data.highErrorEnvelope M.alpha as U)))+M.data.d^3):=HT0
  have H:=actual_general_target_original_Taylor_abs_le_raw_restoration_and_Taylor
    (n:=dim n) M.bf M.hf as (finiteCutMasses_ordered us hus jGrid) hs hU
  exact H.trans ((add_le_add HR0 HT').trans_eq (by dsimp only [g,T,s,as];ring))

end OAI.SKFluctuations.Cavity
