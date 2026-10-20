module

public import ComparisonSignedCavitySecondLowActualHistoryFullWeightedForestB0ModulusAlong
public import ComparisonActualHighOnlyLowB0ResourceConsumerInterfacesSourceAlong
public import ComparisonActualHighOnlyFourReadoutPrimitives
public import ComparisonActualHighOnlyPullbackFourInterfaces

@[expose] public section
noncomputable section
set_option maxHeartbeats 600000
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal ENNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization ActualHighOnlyOverlapMinimum
open NativeOverlapMinimum (ActualSlowWindowChoice)
attribute [local instance] Classical.propDecidable
attribute [local instance] nativeSecondLowSlotFintype
def ActualHistorySecondLowFullWeightedForestB0ModulusOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (seedBound k₀ r₀ depth : ℕ) (Cmass Ccut Couter Rmacro Cx Cerr cK Ci : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop:=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
  ∀ᶠjGrid in atTop,
    let as:=finiteCutMasses us jGrid
    ∀(pre mid tail : List PositiveMass),as=pre++(mid++tail) →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
    ∀(V U : ℕ) (hU : U ≤ (pre++(mid++tail)).length)
      (seed : List NativeResourceMark)
      (st : NativeActualResourceState (Spin (dim n)×Bool) (pre++(mid++tail)) pre.length (pre.length+mid.length)),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed st.generation st.tree st.term → seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves ≤ r₀ →
      0 < mid.length → 0 < V → pre.length < V → V ≤ pre.length+mid.length → ∀(hs : pre.length+mid.length < U),
      partitionPoint 0 as V ≤ Ccut*(M n).xs → partitionPoint 0 as U ≤ Couter*W n →
    ∀(x sourceMass : ℝ) (hsourceMass : 0 < sourceMass),(M n).xs ≤ x → x ≤ W n →
      partitionPoint 0 as pre.length ≤ Cmass*x → partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      4*W n ≤ (M n).R (partitionPoint 0 as U) →
      (M n).z ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).R (partitionPoint 0 as pre.length) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
      Cx*(M n).xs ≤ sourceMass → partitionPoint 0 as U=sourceMass →
      (∀j ≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us) →
    cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as (pre.length+mid.length) →
    |nativeActualFourOtherCategorySum_high_only (M n) U (W n)
      (nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth [st]) .secondLow| ≤
      |st.term.coefficient| *nativeResourceScale x (W n) 1 seed*
        (Ci*partitionPoint 0 as U*(M n).xs*Cerr*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ))+
          eps n*W n*(M n).xs^2)

theorem actual_second_low_full_weighted_forest_from_actual_half_rows_along_high_only
    {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (seedBound k₀ r₀ depth : ℕ) (Cmass Ccut Couter Rmacro Cx cK Ci : ℝ) (eps : ℕ→ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hcK : 0<cK) (hCi : 0<Ci)
    (heps : ∀n,0 ≤ eps n) (HL : Tendsto eps atTop (𝓝 0)) (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (HS : ∀ᶠn in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (HX : ∀ᶠn in atTop,(M n).xs ≤ 1)
    (Hrows : ActualHistorySecondLowFullHalfRetargetB0ModulusOnEveryFinalNetAlong_high_only
      (seedBound+k₀+depth) (r₀+6*depth) Cmass Ccut Couter Rmacro Cx
      (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Ci eps dim M W w) :
    ∃CiForest : ℝ,0<CiForest ∧ ∃epsForest : ℕ→ℝ,(∀n,0 ≤ epsForest n) ∧ Tendsto epsForest atTop (𝓝 0) ∧
      ActualHistorySecondLowFullWeightedForestB0ModulusOnEveryFinalNetAlong_high_only seedBound k₀ r₀ depth
        Cmass Ccut Couter Rmacro Cx (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) cK CiForest epsForest dim M W w := by
  let Cw:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  let Vcost:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 r₀ depth
  have hVcost : 0 ≤ Vcost:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  let C:=2*Vcost+1
  have hC : 0<C:=by dsimp only [C];positivity
  refine ⟨C*Ci,by positivity,fun n=>C*eps n,fun n=>mul_nonneg hC.le (heps n),?_,?_⟩
  · simpa only [mul_zero] using HL.const_mul C
  · filter_upwards [Hrows,HS,HX] with n hn hnSource hnXs
    intro L us hus hstar hret hmesh
    filter_upwards [hn L us hus hstar hret hmesh] with jGrid hj
    dsimp only at hj ⊢
    intro pre mid tail hparts hindex V U hU seed st hP hseed hgen hleaf hmid hV hiV hVstar hs hcut houter
      x sourceMass hsourceMass hx hxW hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes HK
    let as:=pre++(mid++tail)
    let star:=pre.length+mid.length
    let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
    let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
    let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
    let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as pre.length star) tag=>
      nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
    let rows:=nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth [st]
    let price:=Ci*partitionPoint 0 (finiteCutMasses us jGrid) U*(M n).xs*
      actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
        (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid) pre.length+
          1/(dim n+1:ℕ))+eps n*W n*(M n).xs^2
    let B:=nativeResourceScale x (W n) 1 seed*price
    have ho : MassOrdered 0 as:=by dsimp only [as];rw [←hparts];exact finiteCutMasses_ordered us hus jGrid
    have hx0 : 0<x:=(M n).hxs.trans_le hx
    have hxs0 : 0<(M n).xs:=(M n).hxs
    have hW : 0<W n:=hx0.trans_le hxW
    have hscale : 0<nativeResourceScale x (W n) 1 seed:=actual_resource_raw_scale_pos seed hx0 hW
    have hmassU : 0 ≤ partitionPoint 0 (finiteCutMasses us jGrid) U:=
      (partitionPoint_mem _ (finiteCutMasses_ordered us hus jGrid) U).1
    have hCerr:=actualLowErrorComparisonConstant_nonneg (4*Cf+2*Temp) hTemp
    have hdi : 0 ≤ nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf (finiteCutMasses us jGrid) pre.length:=Real.sqrt_nonneg _
    have hepsn : 0 ≤ eps n:=heps n
    have hprice : 0 ≤ price:=by dsimp only [price];positivity
    have hB : 0 ≤ B:=mul_nonneg hscale.le hprice
    have Hrow Q (hQ : Q∈rows) :
        |(W n)⁻¹^Q.generation*nativeActualOriginalFourOtherCategoryContrast_high_only (M n) U Q .secondLow| ≤ |Q.term.coefficient| *B:=by
      have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
        (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hP) Q hQ
      have Hdepth:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
        k₀ (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hgen) Q hQ
      have Hleaf:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
        r₀ (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hleaf) Q hQ
      have Hdegree : Q.term.resources.length ≤ seedBound+k₀+depth:=by rw [Hvalid.total_factor_depth];omega
      have H:=hj pre mid tail hparts hindex V U hU seed Q Hvalid Hdegree hmid hV hiV hVstar hs Hleaf
        hcut houter x sourceMass hsourceMass hx hxW hmi hms Hhigh Hz Hri Hrs HCx HsourceMass Hnodes
      exact H.trans_eq (by dsimp only [B,price];ring)
    have Hsum:=nativeActualFourCenteredForest_singleton_abs_le ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
      weight hCw (fun Q tag=>actual_continuum_four_G_weight_bound_of_small_source_clocks_high_only
        (M n) hCf hnSource hnXs hW hcK as ho hs hU (by simpa only [hparts] using HK) Q tag) depth st hleaf
      (fun Q=>(W n)⁻¹^Q.generation*nativeActualOriginalFourOtherCategoryContrast_high_only (M n) U Q .secondLow) hB Hrow
    apply Hsum.trans
    have HH:=mul_le_mul_of_nonneg_left (show 2*Vcost ≤ C by dsimp only [C];linarith)
      (show 0 ≤ |st.term.coefficient| *B by positivity)
    convert HH using 1 <;> dsimp only [B,price] <;> ring

end OAI.SKFluctuations.Cavity
