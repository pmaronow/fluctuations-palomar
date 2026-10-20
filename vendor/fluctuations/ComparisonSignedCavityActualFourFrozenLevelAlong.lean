module

public import ComparisonSignedCavityActualFourForestNumerics
public import ComparisonSignedCavityActualInheritedFrozenMeanCorrection
public import ComparisonSignedCavityActualInheritedSquareResourceAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 22000000
set_option backward.isDefEq.respectTransparency false

def ActualOriginalFourFrozenChildLevelSavingAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Cmass : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(Lnet : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→(∀u∈uniformMasses Lnet,u∈us)→
    ((Lnet+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U i : ℕ) (hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length),
      ∀x : ℝ,(M n).xs ≤ x→x ≤ W n→partitionPoint 0 as i ≤ Cmass*x→
        |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [nativeActualInitialState as i star 0 (hi.trans (hs.le.trans hU))]).map
          (nativeActualOriginalFourFrozenChildCorrection (M n) hs hU (W n))).sum| ≤
            ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2*x

theorem actual_inherited_four_frozen_child_level_saving_of_pair_budget_along
    {m delta cl cu Az C0 Ct D Bclock Temp gamma cK A : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0 ≤ Temp) (hgamma : 0 < gamma) (hcK : 0 < cK)
    (depth : ℕ) (hA : 1 ≤ A) (Cmass : ℝ)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (htotal : ∀ᶠn : ℕ in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (hroot : ∀ᶠn : ℕ in atTop,(M n).h 0=0)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val)
    (Hpair : ActualSquareResourcePairBudgetOnEveryFinalNetAlong (depth+2) A gamma Cmass M W w) :
    ActualOriginalFourFrozenChildLevelSavingAlong depth Cmass M W w := by
  let Cweight:=Temp/(Real.exp (-4*Temp)*cK)
  have hCweight : 0 ≤ Cweight:=by dsimp only [Cweight];positivity
  let V:=nativeActualFourForestCost Temp cK depth
  let Bcost:=nativeActualWeightedBranchCost nativeActualOriginalFourGBranches Cweight (2+6*depth)
  let Cenv:=V*Bcost*A^(depth+2)
  have hV : 0 ≤ V:=nativeActualFourForestCost_nonneg hTemp hcK depth
  have hBcost : 0 ≤ Bcost:=nativeActualWeightedBranchCost_nonneg _ hCweight _
  have hCenv : 0 ≤ Cenv:=by dsimp only [Cenv];positivity
  have Hrate:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (native_mass_log_power_decay (q:=(1:ℝ)/3) (s:=(1:ℝ)/6) (by norm_num) 0 Cenv)
  have Hmean:=eventually_actual_inherited_clock_frozen_resource_correction
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    (2+6*depth+4) Bclock Temp hTemp hm hC0
  filter_upwards [Hpair,htotal,hroot,hw,hdim.eventually Hmean,Hrate] with n hnPair hnTotal hnRoot hnClock hnMean hnRate
  intro Lnet us hus hstar hret hmesh
  filter_upwards [hnPair Lnet us hus hstar hret hmesh,hnMean (M n) hnTotal hnRoot us hus] with j hjPair hjMean
  dsimp only at hjPair hjMean ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun l=>((M n).bf (partitionPoint 0 as l):ℝ)
  let h:=fun l=>((M n).hf (partitionPoint 0 as l):ℝ)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let C:=nativePhysicalResourceCenter (dim n) (M n).bf (M n).hf as
  let eps:=((dim n+1:ℕ):ℝ)^(-gamma)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have heps : 0 < eps:=by dsimp only [eps];positivity
  have heps1 : eps ≤ 1:=Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (show 1 ≤ dim n+1 by omega)) (by linarith)
  have hKstar : cK*W n ≤ K star := by
    dsimp only [K,star]
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us j hstar)]
    exact hnClock
  intro U i hi hs hU x hxsx hxW hmass
  change i ≤ star at hi
  change star < U at hs
  change U ≤ as.length at hU
  have hx : 0 < x:=(M n).hxs.trans_le hxsx
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let q:=finitePhysicalCavitySquareVariance (dim n) U as b h 1 1
  have hΓ (Q : NativeHighSwitchState (Spin (dim n)×Bool) as) (p : MarkedPlacement Q.tree)
      (_hp : p∈Q.tree.markedAttach 0) : |Γ Q p| ≤ 1:=nativeOriginalHighRowGamma_abs_le_one ho U K Q p
  have hweight Q tag : |weight Q tag| ≤ Cweight:=
    actual_continuum_four_G_weight_bound_of_total_clock (M n) hnTotal hW hcK as ho hs hU hKstar Q tag
  have hst : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  let raw:=A^(depth+2)*x*eps^(depth+1)*(((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)*(M n).xs^2)
  have hraw : 0 ≤ raw:=by dsimp only [raw];positivity
  have Hlevel:=actual_minimum_four_initial_forest_abs_le (M n) hTemp hnTotal hW hcK ho hi hs hU hKstar
    depth (nativeActualOriginalFourFrozenChildCorrection (M n) hs hU (W n))
    (B:=Bcost*raw) (mul_nonneg hBcost hraw) (by
      intro Q hQ
      have HQ:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
        (seed:=[.initial]) (by intro P hP;obtain rfl:=List.mem_singleton.mp hP;exact hst) Q hQ
      have Hsplit:=nativeActualFourCenteredForest_singleton Γ hs (hs.le.trans hU) weight depth st
      change Q∈nativeActualFourCenteredForest Γ hs (hs.le.trans hU) weight depth [st] at hQ
      rw [Hsplit] at hQ
      have HD : Q.generation=depth := by
        rcases List.mem_append.mp hQ with hQ|hQ
        · simpa only [st,nativeActualInitialState,zero_add,mul_one] using
            nativeActualWeightedFrontier_generation Γ hs (hs.le.trans hU)
              nativeActualOriginalFourGCenteredBranches weight 1 nativeActualOriginalFourGCenteredBranches_marked depth st Q hQ
        · simpa only [st,nativeActualInitialState,NativeActualResourceState.freeze,zero_add,mul_one] using
            nativeActualWeightedFrontier_generation Γ hs (hs.le.trans hU)
              nativeActualOriginalFourGCenteredBranches weight 1 nativeActualOriginalFourGCenteredBranches_marked depth st.freeze Q hQ
      have HL : Q.tree.leaves ≤ 2+6*depth := by
        have hr:=nativeActualInitialState_leaves_le (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
        rcases List.mem_append.mp hQ with hQ|hQ
        · convert nativeActualWeightedFrontier_leaves_le Γ hs (hs.le.trans hU)
            nativeActualOriginalFourGCenteredBranches weight 3 nativeActualOriginalFourGCenteredBranches_length
            depth st Q hr hQ using 1; omega
        · convert nativeActualWeightedFrontier_leaves_le Γ hs (hs.le.trans hU)
            nativeActualOriginalFourGCenteredBranches weight 3 nativeActualOriginalFourGCenteredBranches_length
            depth st.freeze Q hr hQ using 1; omega
      let children:=nativeActualWeightedBranchStep Γ hs (hs.le.trans hU) nativeActualOriginalFourGBranches weight Q
      have HE (R : NativeActualResourceState (Spin (dim n)×Bool) as i star) (hR : R∈children) :
          |nativeActualMinimumFourStateResponse (M n) U (W n) R.freeze| ≤ |R.term.coefficient| *raw := by
        have HR:=nativeActualWeightedBranchStep_valid Γ hs (hs.le.trans hU)
          nativeActualOriginalFourGBranches weight Q HQ R hR
        have HRD:=nativeActualWeightedBranchStep_generation Γ hs (hs.le.trans hU)
          nativeActualOriginalFourGBranches weight 1 nativeActualOriginalFourGBranches_marked Q R hR
        rw [HD] at HRD
        have HRL:=nativeActualWeightedBranchStep_leaves_le Γ hs (hs.le.trans hU)
          nativeActualOriginalFourGBranches weight 2 nativeActualOriginalFourGBranches_length Q R HL hR
        have HP:=hjPair U i R.generation R.tree R.term HR (by omega) (hi.trans (hs.le.trans hU))
          x hxsx hxW hmass 1 1 (by norm_num) (by norm_num)
        have H:=hjMean K i star U R.generation [.initial] R.tree R.term HR HRL
          A x (W n) eps (zero_lt_one.trans_le hA) hx hW heps hi (hs.trans_le hU) HP
        change |nativeActualMinimumFourStateResponse (M n) U (W n) R.freeze| ≤ _ at H
        simpa only [HRD,List.length_singleton,nativeResourceScale,List.map_cons,List.map_nil,
          List.prod_cons,List.prod_nil,NativeResourceMark.savedScale,mul_one,raw,
          show 1+(depth+1)=depth+2 by omega,mul_assoc] using H
      change |(children.map (fun R=>nativeActualMinimumFourStateResponse (M n) U (W n) R.freeze)).sum| ≤ _
      apply (native_abs_sum_map_le _ _).trans
      apply (List.sum_le_sum HE).trans
      rw [List.sum_map_mul_right]
      have HC:=nativeActualWeightedBranchStep_coefficient_variation_le ho Γ hΓ hs (hs.le.trans hU)
        nativeActualOriginalFourGBranches weight hCweight (fun P z _=>hweight P z.1) Q HL
      exact (mul_le_mul_of_nonneg_right HC hraw).trans_eq (by dsimp only [Bcost];ring))
  change |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st]).map
    (nativeActualOriginalFourFrozenChildCorrection (M n) hs hU (W n))).sum| ≤ _ at Hlevel ⊢
  apply Hlevel.trans
  have Hab : Cenv*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3) ≤ ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6) := by
    simpa only [pow_zero,mul_one,neg_div,Function.comp_apply] using hnRate
  have Hpow : eps^(depth+1) ≤ 1:=pow_le_one₀ heps.le heps1
  calc
    _=(Cenv*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3))*(M n).xs^2*x*eps^(depth+1) := by
      dsimp only [Cenv,V,raw]
      ring
    _ ≤ (Cenv*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3))*(M n).xs^2*x := by
      exact mul_le_of_le_one_right (by positivity) Hpow
    _ ≤ _:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right Hab (sq_nonneg _)) hx.le

end OAI.SKFluctuations.Cavity
