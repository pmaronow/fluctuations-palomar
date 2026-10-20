module

public import ComparisonSignedCavityActualWorkingScaleCenteredResourceJointHighRestorationFromMinimum
public import ComparisonSignedCavityActualFreshResourceJointHighRestorationReadout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_minimum_inherited_working_scale_fresh_resource_joint_HIGH_restoration_from_minimum
    (kind : NativeJointHighRestorationKind) (degree dOrder rBound : ℕ)
    (hd : 0 < dOrder) (p : ℝ) (hp : 2 < p) (hOrder : p/(p-2) ≤ (dOrder:ℝ)) (Bclock Temp Cf Cmass Ccut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(i star U k : ℕ) (seed : List NativeResourceMark)
          (T : ClockTree (Spin n×Bool) as) (P : NativeResourceTerm i star T),
        NativeActualResourceGenerated i star U seed k T P → i ≤ star → star < U →
        U ≤ as.length → T.leaves ≤ rBound → seed.length+k ≤ degree →
        ∀xScale W : ℝ,M.xs ≤ xScale → xScale ≤ W → W ≤ 1 →
        partitionPoint 0 as i ≤ Cmass*xScale → partitionPoint 0 as star ≤ Cmass*W →
        partitionPoint 0 as U ≤ Ccut*W →
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
        let cost:=T.forkCost (fun j=>(R j)^(4/p))+edgeBudget 0 as (fun j=>(R j)^(4/p))+
          W*(T.forkCost R+edgeBudget 0 as R)
        |(W⁻¹)^k*nativeActualOriginalFreshResourceJointHighRestoration kind M U P| ≤
          |P.coefficient| *nativeResourceScale xScale W 1 seed*(C*W*cost) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_working_scale_centered_resource_joint_HIGH_restoration_from_minimum
    (D:=D) kind degree dOrder (rBound+1) hd p hp hOrder Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro i star U k seed T P hP hi hs hU hT hdepth xScale W hxsScale hxW hW1 hmi hms hcut
  let as:=finiteCutMasses us jGrid
  let g:=nativeFreshAtSlot T 0 P.live.test.target star
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  let f:=fun j=>(R j)^(4/p)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hg : g.tree.leaves ≤ rBound+1:=by
    have H:=T.markedAttach_leaves 0 g (nativeFreshAtSlot_mem T 0 P.live.test.target star)
    omega
  have Hsplit : g.tree.splitIndex (g.embed P.live.test.target) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,min_eq_left (hs.le.trans hU)]
  have hRlo j (hj : j<U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hflo j (hj : j<U) : f j=0:=by
    dsimp only [f]
    rw [hRlo j hj,Real.zero_rpow (by positivity : 4/p≠0)]
  have HR:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs R hRlo
  have HF:=nativeFreshAtSlot_high_forkCost T 0 P.live.test.target hs f hflo
  have Hbound:=hj i star U k seed g.tree (P.retarget 0) hP.retarget hi hs hU hg hdepth
    xScale W hxsScale hxW hW1 hmi hms hcut (g.embed P.live.test.target) g.mark (by rw [Hsplit];exact hs)
  rw [native_actual_original_fresh_resource_joint_HIGH_restoration_eq_centered_retarget kind M U P ho]
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceJointHighRestoration kind M U (P.retarget 0)
      (g.embed P.live.test.target) g.mark| ≤ _
  change |(W⁻¹)^k*nativeActualOriginalCenteredResourceJointHighRestoration kind M U (P.retarget 0)
      (g.embed P.live.test.target) g.mark| ≤ |P.coefficient| *nativeResourceScale xScale W 1 seed*
        (C*W*(g.tree.forkCost f+edgeBudget 0 as f+W*(g.tree.forkCost R+edgeBudget 0 as R))) at Hbound
  rw [show g.tree.forkCost f=T.forkCost f from HF,show g.tree.forkCost R=T.forkCost R from HR] at Hbound
  exact Hbound

end OAI.SKFluctuations.Cavity
