module

public import ComparisonSignedCavityActualFourConstantFrozenLevelAlong
public import ComparisonActualHighOnlySquareConsumerActualFourFrozenLevelAlong

@[expose] public section
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum (ActualSlowWindowChoice)
set_option linter.unusedVariables false
noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set Filter LaplaceWindowFormalization
open NativeOverlapMinimum ActualHighOnlyOverlapMinimum
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

def ActualOriginalFourConstantFrozenChildLevelSavingAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (k₀ depth r : ℕ) (gamma : ℝ)
    {dim : ℕ→ℕ}
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,
    (∀u∈us,u.val ≤ 1)→(w n).star∈us→∀ᶠj : ℕ in atTop,
      let as:=finiteCutMasses us j
      let star:=retainedMassPrefixIndex (w n).star.val as
      ∀(U i : ℕ) (_hi : i ≤ star) (hs : star < U) (hU : U ≤ as.length)
        (st : NativeActualResourceState (Spin (dim n)×Bool) as i star),
        NativeActualResourceGenerated i star U [] st.generation st.tree st.term→
        st.generation=k₀→st.tree.leaves ≤ r→
        |((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth [st]).map
          (nativeActualOriginalFourFrozenChildCorrection_high_only (M n) hs hU (W n))).sum| ≤
          |st.term.coefficient| * ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2*
            ((((dim n+1:ℕ):ℝ)^(-gamma))^(k₀+depth+1))

theorem actual_inherited_four_constant_frozen_child_level_saving_of_pair_budget_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp gamma cK A : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (hTemp : 0 ≤ Temp) (hcK : 0 < cK)
    (k₀ depth r : ℕ) (hA : 1 ≤ A)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n)
    (htotal : ∀ᶠn : ℕ in atTop,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ Temp)
    (hroot : ∀ᶠn : ℕ in atTop,(M n).h 0=0)
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn : ℕ in atTop,cK*W n ≤ actualMixedClock (dim n+1) (M n).bf (M n).hf (w n).star.val)
    (Hpair : ActualSquareConstantResourcePairBudgetOnEveryFinalNetAlong_high_only (k₀+depth+1) A gamma M W w) :
    ActualOriginalFourConstantFrozenChildLevelSavingAlong_high_only k₀ depth r gamma M W w := by
  let Cweight:=Temp/(Real.exp (-4*Temp)*cK)
  have hCweight : 0 ≤ Cweight:=by dsimp only [Cweight];positivity
  let V:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cweight 3 r depth
  let Bcost:=nativeActualWeightedBranchCost nativeActualOriginalFourGBranches Cweight (r+6*depth)
  let Cenv:=2*V*Bcost*A^(k₀+depth+1)
  have hV : 0 ≤ V:=nativeActualWeightedFrontierCost_nonneg _ hCweight _ _ _
  have hBcost : 0 ≤ Bcost:=nativeActualWeightedBranchCost_nonneg _ hCweight _
  have hCenv : 0 ≤ Cenv:=by dsimp only [Cenv];positivity
  have Hrate:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (native_mass_log_power_decay (q:=(1:ℝ)/3) (s:=(1:ℝ)/6) (by norm_num) 0 Cenv)
  have Hmean:=eventually_actual_inherited_clock_frozen_resource_correction_high_only
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D)
    (r+6*depth+4) Bclock Temp hTemp hm hC0
  filter_upwards [Hpair,htotal,hroot,hw,hdim.eventually Hmean,Hrate] with n hnPair hnTotal hnRoot hnClock hnMean hnRate
  intro us hus hstar
  filter_upwards [hnPair us hus hstar,hnMean (M n) hnTotal hnRoot us hus] with j hjPair hjMean
  dsimp only at hjPair hjMean ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let b:=fun l=>((M n).bf (partitionPoint 0 as l):ℝ)
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let eps:=((dim n+1:ℕ):ℝ)^(-gamma)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  have hW : 0 < W n:=(M n).hxs.trans_le (hxs n)
  have heps : 0 < eps:=by dsimp only [eps];positivity
  have hKstar : cK*W n ≤ K star:=by
    dsimp only [K,star]
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us j hstar)]
    exact hnClock
  intro U i hi hs hU st hst hgen hleaves
  change i ≤ star at hi
  change star < U at hs
  change U ≤ as.length at hU
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as i star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  have hΓ (Q : NativeHighSwitchState (Spin (dim n)×Bool) as) (p : MarkedPlacement Q.tree)
      (_hp : p∈Q.tree.markedAttach 0) : |Γ Q p| ≤ 1:=nativeOriginalHighRowGamma_abs_le_one ho U K Q p
  have hweight Q tag : |weight Q tag| ≤ Cweight:=
    actual_continuum_four_G_weight_bound_of_total_clock_high_only (M n) hnTotal hW hcK as ho hs hU hKstar Q tag
  let raw:=A^(k₀+depth+1)*eps^(k₀+depth+1)*(((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3)*(M n).xs^2)
  have hraw : 0 ≤ raw:=by dsimp only [raw];positivity
  have Hlevel:=actual_minimum_four_state_forest_abs_le_high_only (M n) hTemp hnTotal hW hcK ho hs hU hKstar
    depth st hleaves (nativeActualOriginalFourFrozenChildCorrection_high_only (M n) hs hU (W n))
    (B:=Bcost*raw) (mul_nonneg hBcost hraw) (by
      intro Q hQ
      have HQ:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
        (seed:=[]) (by intro P hP;obtain rfl:=List.mem_singleton.mp hP;exact hst) Q hQ
      have HD:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
        k₀ (by intro P hP;obtain rfl:=List.mem_singleton.mp hP;exact hgen) Q hQ
      have HL:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
        r (by intro P hP;obtain rfl:=List.mem_singleton.mp hP;exact hleaves) Q hQ
      let children:=nativeActualWeightedBranchStep Γ hs (hs.le.trans hU) nativeActualOriginalFourGBranches weight Q
      have HE (R : NativeActualResourceState (Spin (dim n)×Bool) as i star) (hR : R∈children) :
          |nativeActualMinimumFourStateResponse_high_only (M n) U (W n) R.freeze| ≤ |R.term.coefficient| *raw:=by
        have HR:=nativeActualWeightedBranchStep_valid Γ hs (hs.le.trans hU)
          nativeActualOriginalFourGBranches weight Q HQ R hR
        have HRD:=nativeActualWeightedBranchStep_generation Γ hs (hs.le.trans hU)
          nativeActualOriginalFourGBranches weight 1 nativeActualOriginalFourGBranches_marked Q R hR
        rw [HD] at HRD
        have HRL:=nativeActualWeightedBranchStep_leaves_le Γ hs (hs.le.trans hU)
          nativeActualOriginalFourGBranches weight 2 nativeActualOriginalFourGBranches_length Q R HL hR
        have HP:=hjPair U i R.generation R.tree R.term HR (by omega) (M n).xs 1 1 (by norm_num) (by norm_num)
        have H:=hjMean K i star U R.generation [] R.tree R.term HR HRL
          A (M n).xs (W n) eps (zero_lt_one.trans_le hA) (M n).hxs hW heps hi (hs.trans_le hU) HP
        change |nativeActualMinimumFourStateResponse_high_only (M n) U (W n) R.freeze| ≤ _ at H
        simpa only [HRD,List.length_nil,zero_add,nativeResourceScale,List.map_nil,
          List.prod_nil,mul_one,raw,mul_assoc] using H
      change |(children.map (fun R=>nativeActualMinimumFourStateResponse_high_only (M n) U (W n) R.freeze)).sum| ≤ _
      apply (native_abs_sum_map_le _ _).trans
      apply (List.sum_le_sum HE).trans
      rw [List.sum_map_mul_right]
      have HC:=nativeActualWeightedBranchStep_coefficient_variation_le ho Γ hΓ hs (hs.le.trans hU)
        nativeActualOriginalFourGBranches weight hCweight (fun P z _=>hweight P z.1) Q HL
      exact (mul_le_mul_of_nonneg_right HC hraw).trans_eq (by dsimp only [Bcost];ring))
  apply Hlevel.trans
  have Hab : Cenv*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3) ≤ ((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6):=by
    simpa only [pow_zero,mul_one,neg_div,Function.comp_apply] using hnRate
  calc
    _=|st.term.coefficient| *(Cenv*((dim n+1:ℕ):ℝ)^(-(1:ℝ)/3))*(M n).xs^2*eps^(k₀+depth+1):=by
      dsimp only [Cenv,V,raw,Cweight]
      ring
    _ ≤ |st.term.coefficient| *((dim n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(M n).xs^2*eps^(k₀+depth+1):=by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left Hab (abs_nonneg _)) (sq_nonneg _)) (by positivity)
    _=_:=rfl

end OAI.SKFluctuations.Cavity
