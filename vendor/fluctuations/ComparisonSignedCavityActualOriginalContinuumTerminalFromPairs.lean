module

public import ComparisonSignedCavityActualOriginalContinuumTerminal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

theorem exists_actual_bare_original_continuum_G_terminal_decay_of_pair_budgets
    {m delta cl cu Az C0 Ct D Bclock Temp Lwin gamma : ℝ}
    (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hTemp : 0 < Temp) (hgamma : 0 < gamma)
    (Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0)
    (Cs : ℝ) (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,IsActualCalibratedSlowWindow (M n) (W n) Temp Lwin Cs (w n))
    (Hp : ∀degree : ℕ,0 < degree→∃A : ℝ,1 ≤ A ∧
      ActualSquareResourcePairBudgetOnEveryFinalNet degree A gamma Cmass M W w) :
    ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
      ∀depth : ℕ,threshold ≤ depth→ActualOriginalContinuumGTerminalSaving depth saving Cmass M W w := by
  obtain ⟨threshold,hth,saving,hsaving,Hrate⟩:=exists_actual_mixed_terminal_depth
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0 hgamma
  have hlen : ∀b∈nativeActualOriginalGCenteredBranches,b.2.length ≤ 2 := by
    simp [nativeActualOriginalGCenteredBranches_eq]
  have hcount : ∀b∈nativeActualOriginalGCenteredBranches,nativeActualExpansionMarkedCount b.2=1 := by
    simp [nativeActualOriginalGCenteredBranches_eq,nativeActualExpansionMarkedCount,
      NativeActualExpansionOp.markedIncrement]
  let c:=starMassBandConstant cu Az/cu
  let Cweight:=Temp/(Real.exp (-4*Temp)*(3*Temp*c/8))
  have hc : 0 < c:=div_pos (star_mass_band_constant_pos hcu hAz) hcu
  have hCweight : 0 ≤ Cweight:=by dsimp only [Cweight];positivity
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨threshold,hth,saving,hsaving,?_⟩
  intro depth hdepth
  obtain ⟨A,hA,HA⟩:=Hp (1+depth) (by omega)
  let V:=nativeActualWeightedFrontierCost nativeActualOriginalGCenteredBranches Cweight 2 2 depth
  let Cenv:=V*A^(1+depth)*(2*Temp)*nativeActualGInsertionCost (2+4*depth)
  have hV : 0 ≤ V:=nativeActualWeightedFrontierCost_nonneg _ hCweight 2 2 depth
  have hGcost:=nativeActualGInsertionCost_nonneg (2+4*depth)
  have hCenv : 0 ≤ Cenv:=by dsimp only [Cenv];positivity
  let ops:=List.replicate depth NativeActualExpansionOp.highRow
  have hopcount : nativeActualExpansionMarkedCount ops=depth := by
    simp [ops,nativeActualExpansionMarkedCount,NativeActualExpansionOp.markedIncrement]
  filter_upwards [HA,hw,HW,Hrate Cenv hCenv] with n hn hnw hnW hnrate
  intro Lnet us hus hstar hret hmesh
  filter_upwards [hn Lnet us hus hstar hret hmesh] with j hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock n (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let C:=nativePhysicalResourceCenter n (M n).bf (M n).hf as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  intro U i hi hs hU x hxsx hxW hmass
  change i ≤ star at hi
  change star < U at hs
  change U ≤ as.length at hU
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (parent : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K parent
    (nativeOriginalClockGBranchBeta U K b parent tag)
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (by omega : i ≤ as.length)
  have hst : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (by change i ≤ as.length;omega))
  have hr : st.tree.leaves ≤ 2:=nativeActualInitialState_leaves_le as i star 0 (by omega)
  have hΓ (Q : NativeHighSwitchState (Spin n×Bool) as) (p : MarkedPlacement Q.tree)
      (_hp : p∈Q.tree.markedAttach 0) : |Γ Q p| ≤ 1:=nativeOriginalHighRowGamma_abs_le_one ho U K Q p
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  have heps : 0 < ((n+1:ℕ):ℝ)^(-gamma):=by positivity
  have hweight Q z (_hz : z∈nativeActualOriginalGCenteredBranches) : |weight Q z.1| ≤ Cweight:=
    actual_calibrated_continuum_G_weight_bound (M n) hcu hAz hTemp hW (hb n) (hh n)
      (w n) hnw as ho (finiteCutMasses_nodes us j hstar) i U hs hU Q z.1
  let B:=A^(1+depth)*x*(((n+1:ℕ):ℝ)^(-gamma))^depth*(2*Temp)*nativeActualGInsertionCost (2+4*depth)
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have Hterm:=nativeActualWeightedFrontier_terminal_abs_le ho Γ hΓ hs (hs.le.trans hU)
    nativeActualOriginalGCenteredBranches weight hCweight hweight 2 hlen depth st hr
    (nativeOriginalClockStateResponse U K b C 0 q 0 0 q 0 (W n)) hB (by
      intro Q hQ
      have HG:=nativeActualWeightedFrontier_valid Γ hs (hs.le.trans hU)
        nativeActualOriginalGCenteredBranches weight depth st hst Q hQ
      have HD:=nativeActualWeightedFrontier_generation Γ hs (hs.le.trans hU)
        nativeActualOriginalGCenteredBranches weight 1 hcount depth st Q hQ
      change Q.generation=0+depth*1 at HD
      simp only [zero_add,mul_one] at HD
      have HL:=nativeActualWeightedFrontier_leaves_le Γ hs (hs.le.trans hU)
        nativeActualOriginalGCenteredBranches weight 2 hlen depth st Q hr hQ
      have HP:=hj U i Q.generation Q.tree Q.term HG (by omega) (hi.trans (hs.le.trans hU)) x hxsx hxW hmass
        1 1 (by norm_num) (by norm_num)
      have H:=nativeActualClockFrozenResourceResponse_abs_le (M n) K hcl hAz hTemp.le
        (hb n) (hh n) HG ho (2+4*depth) (by omega) 0 q 0 0 q 0
        A x (W n) (((n+1:ℕ):ℝ)^(-gamma)) (zero_lt_one.trans_le hA) hx hW heps hi
        (by omega) HP HP
      simpa only [nativeOriginalClockStateResponse,B,HD,List.length_singleton,nativeResourceScale,
        List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,NativeResourceMark.savedScale,
        mul_one,mul_assoc] using H)
  simp only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul] at Hterm
  change |nativeActualOriginalContinuumGFrontier (M n) as (W n) i star U hi hs hU depth| ≤ V*B at Hterm
  have Henv : V*B ≤ Cenv*(((n+1:ℕ):ℝ)^(-gamma))^depth := by
    have HX:=mul_le_mul_of_nonneg_left (hxW.trans hnW)
      (show 0 ≤ Cenv*(((n+1:ℕ):ℝ)^(-gamma))^depth by positivity)
    dsimp only [Cenv,B] at HX ⊢
    nlinarith only [HX]
  have HR:=hnrate (M n) ops (by rwa [hopcount])
  rw [hopcount] at HR
  exact Hterm.trans (Henv.trans HR)

end OAI.SKFluctuations.Cavity
