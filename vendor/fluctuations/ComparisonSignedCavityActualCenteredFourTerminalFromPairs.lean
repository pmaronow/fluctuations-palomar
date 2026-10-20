module

public import ComparisonSignedCavityActualCenteredFourTerminalLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

def ActualOriginalContinuumFrozenSeedFourGTerminalSaving
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (saving Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→(∀u∈uniformMasses Lnet,u∈us)→
    ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U i : ℕ) (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length),
      ∀x : ℝ,(M n).xs ≤ x→x ≤ W n→partitionPoint 0 as i ≤ Cmass*x→
        |nativeActualOriginalContinuumFrozenSeedFourGFrontier (M n) as (W n) i star U hi hs hU depth| ≤
          ((n+1:ℕ):ℝ)^(-saving)*(M n).xs^2

def ActualOriginalContinuumCenteredFourGTerminalSaving
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (saving Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→(∀u∈uniformMasses Lnet,u∈us)→
    ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U i : ℕ) (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length),
      ∀x : ℝ,(M n).xs ≤ x→x ≤ W n→partitionPoint 0 as i ≤ Cmass*x→
        |nativeActualOriginalContinuumCenteredFourGFrontier (M n) as (W n) i star U hi hs hU depth| ≤
          2*((n+1:ℕ):ℝ)^(-saving)*(M n).xs^2

theorem exists_actual_original_continuum_frozen_seed_four_G_terminal_decay_of_pair_budgets
    {m delta cl cu Az C0 Ct D Bclock Temp gamma cK : ℝ}
    (hm : 0 < m) (hC0 : 0<C0) (hTemp : 0≤Temp) (hgamma : 0<gamma) (hcK : 0<cK)
    (Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤Temp)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,cK*W n≤actualMixedClock (n+1) (M n).bf (M n).hf (w n).star.val)
    (Hp : ∀degree : ℕ,0<degree→∃A : ℝ,1≤A ∧
      ActualSquareResourcePairBudgetOnEveryFinalNet degree A gamma Cmass M W w) :
    ∃threshold : ℕ,0<threshold ∧ ∃saving : ℝ,0<saving ∧
      ∀depth : ℕ,threshold≤depth→ActualOriginalContinuumFrozenSeedFourGTerminalSaving depth saving Cmass M W w := by
  obtain ⟨threshold,hth,saving,hsaving,Hrate⟩:=exists_actual_mixed_terminal_depth
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0 hgamma
  have hlen : ∀b∈nativeActualOriginalFourGCenteredBranches,b.2.length ≤ 3 := by
    simp [nativeActualOriginalFourGCenteredBranches_eq]
  have hcount : ∀b∈nativeActualOriginalFourGCenteredBranches,nativeActualExpansionMarkedCount b.2=1 := by
    simp [nativeActualOriginalFourGCenteredBranches_eq,nativeActualExpansionMarkedCount,
      NativeActualExpansionOp.markedIncrement]
  let Cweight:=Temp/(Real.exp (-4*Temp)*cK)
  have hCweight : 0 ≤ Cweight:=by dsimp only [Cweight];positivity
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨threshold,hth,saving,hsaving,?_⟩
  intro depth hdepth
  obtain ⟨A,hA,HA⟩:=Hp (1+depth) (by omega)
  let V:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cweight 3 2 depth
  let Cenv:=V*A^(1+depth)*(2*Temp)*nativeActualGInsertionCost (2+6*depth)
  have hV : 0 ≤ V:=nativeActualWeightedFrontierCost_nonneg _ hCweight 3 2 depth
  have hGcost:=nativeActualGInsertionCost_nonneg (2+6*depth)
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
    (nativeOriginalClockFourGBranchBeta U K b parent tag)
  let original:=nativeActualInitialState (S:=Spin n×Bool) as i star 0 (by omega : i ≤ as.length)
  let st:=original.freeze
  have hst : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    (show NativeActualResourceGenerated i star U [.initial] original.generation original.tree original.term from
      .physical (.seed as hU 0 .initial (Or.inl rfl) (by change i ≤ as.length;omega))).freeze
  have hr : st.tree.leaves ≤ 2:=nativeActualInitialState_leaves_le as i star 0 (by omega)
  have hΓ (Q : NativeHighSwitchState (Spin n×Bool) as) (p : MarkedPlacement Q.tree)
      (_hp : p∈Q.tree.markedAttach 0) : |Γ Q p| ≤ 1:=nativeOriginalHighRowGamma_abs_le_one ho U K Q p
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  have heps : 0 < ((n+1:ℕ):ℝ)^(-gamma):=by positivity
  have hweight Q z (_hz : z∈nativeActualOriginalFourGCenteredBranches) : |weight Q z.1| ≤ Cweight:=
    actual_retained_continuum_four_G_weight_bound_of_total_clock (M n) (htotal n) hW hcK
      (w n).star hnw as ho (finiteCutMasses_nodes us j hstar) hs hU Q z.1
  let B:=A^(1+depth)*x*(((n+1:ℕ):ℝ)^(-gamma))^depth*(2*Temp)*nativeActualGInsertionCost (2+6*depth)
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have Hterm:=nativeActualWeightedFrontier_terminal_abs_le ho Γ hΓ hs (hs.le.trans hU)
    nativeActualOriginalFourGCenteredBranches weight hCweight hweight 3 hlen depth st hr
    (nativeOriginalClockStateResponse U K b C 0 q 0 0 q 0 (W n)) hB (by
      intro Q hQ
      have HG:=nativeActualWeightedFrontier_valid Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight depth st hst Q hQ
      have HD:=nativeActualWeightedFrontier_generation Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight 1 hcount depth st Q hQ
      change Q.generation=0+depth*1 at HD
      simp only [zero_add,mul_one] at HD
      have HL:=nativeActualWeightedFrontier_leaves_le Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight 3 hlen depth st Q hr hQ
      have HP:=hj U i Q.generation Q.tree Q.term HG (by omega) (hi.trans (hs.le.trans hU)) x hxsx hxW hmass
        1 1 (by norm_num) (by norm_num)
      have H:=nativeActualClockFrozenResourceResponse_abs_le_of_total_clock (M n) K hTemp
        (htotal n) HG ho (2+6*depth) (by omega) 0 q 0 0 q 0
        A x (W n) (((n+1:ℕ):ℝ)^(-gamma)) (zero_lt_one.trans_le hA) hx hW heps hi
        (by omega) HP HP
      simpa only [nativeOriginalClockStateResponse,B,HD,List.length_singleton,nativeResourceScale,
        List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,NativeResourceMark.savedScale,
        mul_one,mul_assoc] using H)
  simp only [st,original,NativeActualResourceState.freeze,NativeResourceTerm.freeze,
    nativeActualInitialState,NativeResourceTerm.ofLive,abs_neg,abs_one,one_mul] at Hterm
  change |nativeActualOriginalContinuumFrozenSeedFourGFrontier (M n) as (W n) i star U hi hs hU depth| ≤ V*B at Hterm
  have Henv : V*B ≤ Cenv*(((n+1:ℕ):ℝ)^(-gamma))^depth := by
    have HX:=mul_le_mul_of_nonneg_left (hxW.trans hnW)
      (show 0 ≤ Cenv*(((n+1:ℕ):ℝ)^(-gamma))^depth by positivity)
    dsimp only [Cenv,B] at HX ⊢
    nlinarith only [HX]
  have HR:=hnrate (M n) ops (by rwa [hopcount])
  rw [hopcount] at HR
  exact Hterm.trans (Henv.trans HR)

theorem exists_actual_original_continuum_centered_four_G_terminal_decay_of_pair_budgets
    {m delta cl cu Az C0 Ct D Bclock Temp gamma cK : ℝ}
    (hm : 0 < m) (hC0 : 0<C0) (hTemp : 0≤Temp) (hgamma : 0<gamma) (hcK : 0<cK)
    (Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤W n) (hWlim : Tendsto W atTop (𝓝 0))
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤Temp)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,cK*W n≤actualMixedClock (n+1) (M n).bf (M n).hf (w n).star.val)
    (Hp : ∀degree : ℕ,0<degree→∃A : ℝ,1≤A ∧
      ActualSquareResourcePairBudgetOnEveryFinalNet degree A gamma Cmass M W w) :
    ∃threshold : ℕ,0<threshold ∧ ∃saving : ℝ,0<saving ∧
      ∀depth : ℕ,threshold≤depth→
        ActualOriginalContinuumCenteredFourGTerminalSaving depth saving Cmass M W w := by
  obtain ⟨tr,htr,sr,hsr,Hr⟩:=
    exists_actual_original_continuum_four_G_terminal_decay_of_pair_budgets
      hm hC0 hTemp hgamma hcK Cmass M W hxs hWlim htotal w hw Hp
  obtain ⟨tf,htf,sf,hsf,Hf⟩:=
    exists_actual_original_continuum_frozen_seed_four_G_terminal_decay_of_pair_budgets
      hm hC0 hTemp hgamma hcK Cmass M W hxs hWlim htotal w hw Hp
  refine ⟨max tr tf,htr.trans_le (le_max_left _ _),min sr sf,lt_min hsr hsf,?_⟩
  intro depth hdepth
  filter_upwards [Hr depth ((le_max_left _ _).trans hdepth),
    Hf depth ((le_max_right _ _).trans hdepth)] with n hnraw hnfrozen
  intro Lnet us hus hstar hret hmesh
  filter_upwards [hnraw Lnet us hus hstar hret hmesh,
    hnfrozen Lnet us hus hstar hret hmesh] with j hjraw hjfrozen
  dsimp only at hjraw hjfrozen ⊢
  intro U i hi hs hU x hxsx hxW hmass
  rw [native_actual_original_centered_four_G_frontier_eq_two_seeds]
  have hraw:=hjraw U i hi hs hU x hxsx hxW hmass
  have hfrozen:=hjfrozen U i hi hs hU x hxsx hxW hmass
  have hN : 1≤((n+1:ℕ):ℝ):=by exact_mod_cast (show 1≤n+1 by omega)
  have HR:=mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (min_le_left sr sf)))
    (sq_nonneg (M n).xs)
  have HF:=mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg (min_le_right sr sf)))
    (sq_nonneg (M n).xs)
  have HC : ((n+1:ℕ):ℝ)^(-min sr sf)*(M n).xs^2+
      ((n+1:ℕ):ℝ)^(-min sr sf)*(M n).xs^2=
      2*((n+1:ℕ):ℝ)^(-min sr sf)*(M n).xs^2:=by ring
  exact (abs_add_le _ _).trans ((add_le_add (hraw.trans HR) (hfrozen.trans HF)).trans_eq HC)

end OAI.SKFluctuations.Cavity
