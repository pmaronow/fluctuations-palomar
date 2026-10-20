module

public import ComparisonSignedCavityActualConstantStarFourTerminalFromPairs

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000

def ActualOriginalConstantGeneratedFourGIndividualTerminalSaving
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (r depth : ℕ) (saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
      let K:=nativeContinuumMixedClock n (M n).bf (M n).hf as
      ∀(U i : ℕ) (_hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
        (st : NativeActualResourceState (Spin n×Bool) as i star),
      NativeActualResourceGenerated i star U [] st.generation st.tree st.term→
      st.generation=1→st.tree.leaves ≤ r→
      |((nativeActualWeightedFrontier (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches
        (fun parent tag=>nativeOriginalClockParentWeight (W n) U K parent
          (nativeOriginalClockFourGBranchBeta U K b parent tag)) depth st).map
        (nativeActualMinimumFourStateResponse (M n) U (W n))).sum| ≤
        |st.term.coefficient| *(((n+1:ℕ):ℝ)^(-saving)*(M n).xs^2)

theorem exists_actual_original_constant_generated_four_G_individual_terminal_decay_of_pair_budgets
    {m delta cl cu Az C0 Ct D Bclock Temp gamma cK : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0 ≤ Temp) (hgamma : 0 < gamma) (hcK : 0 < cK)
    (r : ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (htotal : ∀ᶠn : ℕ in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,cK*W n ≤ actualMixedClock (n+1) (M n).bf (M n).hf (w n).star.val)
    (Hp : ∀degree : ℕ,0 < degree→∃A : ℝ,1 ≤ A ∧
      ActualSquareConstantResourcePairBudgetOnEveryFinalNet degree A gamma M W w) :
    ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
      ∀depth : ℕ,threshold ≤ depth→ActualOriginalConstantGeneratedFourGIndividualTerminalSaving r depth saving M W w := by
  obtain ⟨threshold,hth,saving,hsaving,Hrate⟩:=exists_actual_mixed_terminal_depth
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0 hgamma
  have hlen : ∀b∈nativeActualOriginalFourGCenteredBranches,b.2.length  ≤  3 := by
    simp [nativeActualOriginalFourGCenteredBranches_eq]
  have hcount : ∀b∈nativeActualOriginalFourGCenteredBranches,nativeActualExpansionMarkedCount b.2=1 := by
    simp [nativeActualOriginalFourGCenteredBranches_eq,nativeActualExpansionMarkedCount,
      NativeActualExpansionOp.markedIncrement]
  let Cweight:=Temp/(Real.exp (-4*Temp)*cK)
  have hCweight : 0  ≤  Cweight:=by dsimp only [Cweight];positivity
  refine ⟨threshold,hth,saving,hsaving,?_⟩
  intro depth hdepth
  obtain ⟨A,hA,HA⟩:=Hp (1+depth) (by omega)
  let V:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cweight 3 r depth
  let Cenv:=V*A^(1+depth)*(2*Temp)*nativeActualGInsertionCost (r+6*depth)
  have hV : 0  ≤  V:=nativeActualWeightedFrontierCost_nonneg _ hCweight 3 r depth
  have hGcost:=nativeActualGInsertionCost_nonneg (r+6*depth)
  have hCenv : 0  ≤  Cenv:=by dsimp only [Cenv];positivity
  let ops:=List.replicate depth NativeActualExpansionOp.highRow
  have hopcount : nativeActualExpansionMarkedCount ops=depth := by
    simp [ops,nativeActualExpansionMarkedCount,NativeActualExpansionOp.markedIncrement]
  filter_upwards [HA,hw,Hrate Cenv hCenv,htotal] with n hn hnw hnrate hntotal
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let K:=nativeContinuumMixedClock n (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>((M n).hf (partitionPoint 0 as j):ℝ)
  let C:=nativePhysicalResourceCenter n (M n).bf (M n).hf as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  intro U i hi hs hU st hst hgen hr
  change star  <  U at hs
  change U  ≤  as.length at hU
  let q:=finitePhysicalCavitySquareVariance n U as b h 1 1
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (parent : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K parent
    (nativeOriginalClockFourGBranchBeta U K b parent tag)
  have hΓ (Q : NativeHighSwitchState (Spin n×Bool) as) (p : MarkedPlacement Q.tree)
      (_hp : p∈Q.tree.markedAttach 0) : |Γ Q p|  ≤  1:=nativeOriginalHighRowGamma_abs_le_one ho U K Q p
  have hW : 0  <  W n:=(M n).hxs.trans_le (hxs n)
  have heps : 0  <  ((n+1:ℕ):ℝ)^(-gamma):=by positivity
  have hweight Q z (_hz : z∈nativeActualOriginalFourGCenteredBranches) : |weight Q z.1|  ≤  Cweight:=
    actual_retained_continuum_four_G_weight_bound_of_total_clock (M n) hntotal hW hcK
      (w n).star hnw as ho (finiteCutMasses_nodes us j hstar) hs hU Q z.1
  let B:=A^(1+depth)*(((n+1:ℕ):ℝ)^(-gamma))^(1+depth)*(2*Temp)*nativeActualGInsertionCost (r+6*depth)
  have hB : 0  ≤  B:=by dsimp only [B];positivity
  have Hterm:=nativeActualWeightedFrontier_terminal_abs_le ho Γ hΓ hs (hs.le.trans hU)
    nativeActualOriginalFourGCenteredBranches weight hCweight hweight 3 hlen depth st hr
    (nativeOriginalClockStateResponse U K b C 0 q 0 0 q 0 (W n)) hB (by
      intro Q hQ
      have HG:=nativeActualWeightedFrontier_valid Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight depth st hst Q hQ
      have HD:=nativeActualWeightedFrontier_generation Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight 1 hcount depth st Q hQ
      rw [hgen] at HD
      simp only [mul_one] at HD
      have HL:=nativeActualWeightedFrontier_leaves_le Γ hs (hs.le.trans hU)
        nativeActualOriginalFourGCenteredBranches weight 3 hlen depth st Q hr hQ
      have HP:=hj U i Q.generation Q.tree Q.term HG (by omega)
        (W n) 1 1 (by norm_num) (by norm_num)
      have H:=nativeActualClockFrozenResourceResponse_abs_le_of_total_clock (M n) K hTemp
        hntotal HG ho (r+6*depth) (by omega) 0 q 0 0 q 0
        A (W n) (W n) (((n+1:ℕ):ℝ)^(-gamma)) (zero_lt_one.trans_le hA) hW hW heps hi
        (by omega) HP HP
      simpa only [nativeOriginalClockStateResponse,B,HD,List.length_singleton,List.length_nil,zero_add,nativeResourceScale,
        List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,NativeResourceMark.savedScale,
        mul_one,mul_assoc] using H)
  change |((nativeActualWeightedFrontier Γ hs (hs.le.trans hU) nativeActualOriginalFourGCenteredBranches
    weight depth st).map (nativeActualMinimumFourStateResponse (M n) U (W n))).sum| ≤
      |st.term.coefficient| *V*B at Hterm
  have heps1 : ((n+1:ℕ):ℝ)^(-gamma) ≤ 1:=by
    exact Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (show 1 ≤ n+1 by omega)) (neg_nonpos.mpr hgamma.le)
  have Henv : V*B  ≤  Cenv*(((n+1:ℕ):ℝ)^(-gamma))^depth := by
    have HX:=mul_le_mul_of_nonneg_left heps1
      (show 0 ≤ Cenv*(((n+1:ℕ):ℝ)^(-gamma))^depth by positivity)
    dsimp only [Cenv,B] at HX ⊢
    convert HX using 1 <;> simp only [pow_add,pow_one] <;> ring
  have HR:=hnrate (M n) ops (by rwa [hopcount])
  rw [hopcount] at HR
  exact Hterm.trans (by
    calc
      |st.term.coefficient| *V*B=|st.term.coefficient| *(V*B):=by ring
      _ ≤ |st.term.coefficient| *(Cenv*(((n+1:ℕ):ℝ)^(-gamma))^depth):=
        mul_le_mul_of_nonneg_left Henv (abs_nonneg _)
      _ ≤ |st.term.coefficient| *(((n+1:ℕ):ℝ)^(-saving)*(M n).xs^2):=
        mul_le_mul_of_nonneg_left HR (abs_nonneg _))

def ActualOriginalConstantGeneratedFourGCenteredTerminalSaving
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (r depth : ℕ) (saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U i : ℕ) (_hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
        (st : NativeActualResourceState (Spin n×Bool) as i star),
      NativeActualResourceGenerated i star U [] st.generation st.tree st.term→
      st.generation=1→st.tree.leaves ≤ r→
      |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st]).map
        (nativeActualMinimumFourStateResponse (M n) U (W n))).sum| ≤
        2*|st.term.coefficient| *(((n+1:ℕ):ℝ)^(-saving)*(M n).xs^2)

theorem exists_actual_original_constant_generated_four_G_centered_terminal_decay_of_pair_budgets
    {m delta cl cu Az C0 Ct D Bclock Temp gamma cK : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0 ≤ Temp) (hgamma : 0 < gamma) (hcK : 0 < cK)
    (r : ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (htotal : ∀ᶠn : ℕ in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,cK*W n ≤ actualMixedClock (n+1) (M n).bf (M n).hf (w n).star.val)
    (Hp : ∀degree : ℕ,0 < degree→∃A : ℝ,1 ≤ A ∧
      ActualSquareConstantResourcePairBudgetOnEveryFinalNet degree A gamma M W w) :
    ∃threshold : ℕ,0 < threshold ∧ ∃saving : ℝ,0 < saving ∧
      ∀depth : ℕ,threshold ≤ depth→ActualOriginalConstantGeneratedFourGCenteredTerminalSaving r depth saving M W w := by
  obtain ⟨threshold,hth,saving,hsaving,HR⟩:=
    exists_actual_original_constant_generated_four_G_individual_terminal_decay_of_pair_budgets
      hm hC0 hTemp hgamma hcK r M W hxs htotal w hw Hp
  refine ⟨threshold,hth,saving,hsaving,?_⟩
  intro depth hdepth
  filter_upwards [HR depth hdepth] with n hn
  intro us hus hstar
  filter_upwards [hn us hus hstar] with j hj
  dsimp only at hj ⊢
  intro U i hi hs hU st hst hgen hr
  have HF:=hj U i hi hs hU st hst hgen hr
  have HT:=hj U i hi hs hU st.freeze hst.freeze hgen hr
  simp only [NativeActualResourceState.freeze,NativeResourceTerm.freeze,abs_neg] at HT
  unfold nativeActualMinimumFourCenteredForest
  rw [nativeActualFourCenteredForest_singleton_response]
  exact (abs_add_le _ _).trans ((add_le_add HF HT).trans_eq (by ring))

end OAI.SKFluctuations.Cavity
