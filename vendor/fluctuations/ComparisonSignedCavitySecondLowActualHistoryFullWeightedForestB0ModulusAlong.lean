module

public import ComparisonSignedCavitySecondLowActualHistoryFullHalfRetargetB0ModulusAlong
public import ComparisonSignedCavityActualConstantSourceCategoryReduction
public import ComparisonSignedCavityActualSmallSourceFourWeights
public import ComparisonSignedCavityActualFourForestNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 60000000
set_option backward.isDefEq.respectTransparency false

def ActualHistorySecondLowFullWeightedForestB0ModulusOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (seedBound k₀ r₀ depth : ℕ) (Cmass Ccut Couter Rmacro Cx Cerr cK Ci : ℝ) (eps : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
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
    |nativeActualFourOtherCategorySum (M n) U (W n)
      (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st]) .secondLow| ≤
      |st.term.coefficient| *nativeResourceScale x (W n) 1 seed*
        (Ci*partitionPoint 0 as U*(M n).xs*Cerr*
          (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as pre.length+1/(dim n+1:ℕ))+
          eps n*W n*(M n).xs^2)

theorem actual_second_low_full_weighted_forest_from_actual_half_rows_along
    {m delta cl cu Az C0 Ct D Bclock Temp Cf : ℝ}
    (seedBound k₀ r₀ depth : ℕ) (Cmass Ccut Couter Rmacro Cx cK Ci : ℝ) (eps : ℕ→ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hcK : 0<cK) (hCi : 0<Ci)
    (heps : ∀n,0 ≤ eps n) (HL : Tendsto eps atTop (𝓝 0)) (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (HS : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (HX : ∀ᶠn in atTop,(M n).xs ≤ 1)
    (Hrows : ActualHistorySecondLowFullHalfRetargetB0ModulusOnEveryFinalNetAlong
      (seedBound+k₀+depth) (r₀+6*depth) Cmass Ccut Couter Rmacro Cx
      (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) Ci eps dim M W w) :
    ∃CiForest : ℝ,0<CiForest ∧ ∃epsForest : ℕ→ℝ,(∀n,0 ≤ epsForest n) ∧ Tendsto epsForest atTop (𝓝 0) ∧
      ActualHistorySecondLowFullWeightedForestB0ModulusOnEveryFinalNetAlong seedBound k₀ r₀ depth
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
    let rows:=nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth [st]
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
        |(W n)⁻¹^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q .secondLow| ≤ |Q.term.coefficient| *B:=by
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
      weight hCw (fun Q tag=>actual_continuum_four_G_weight_bound_of_small_source_clocks
        (M n) hCf hnSource hnXs hW hcK as ho hs hU (by simpa only [hparts] using HK) Q tag) depth st hleaf
      (fun Q=>(W n)⁻¹^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q .secondLow) hB Hrow
    apply Hsum.trans
    have HH:=mul_le_mul_of_nonneg_left (show 2*Vcost ≤ C by dsimp only [C];linarith)
      (show 0 ≤ |st.term.coefficient| *B by positivity)
    convert HH using 1 <;> dsimp only [B,price] <;> ring

theorem actual_second_low_actual_history_full_weighted_forest_B0_modulus_along
    {m delta eta cl cu Az C0 Ct D Bclock Temp Tstar Lwin Cs c0 : ℝ}
    (seedBound k₀ r₀ depth : ℕ) (Cmass Ccut Couter Ccal Rmacro F Cx cK : ℝ) (hcK : 0<cK)
    (hCx : 0 < Cx) (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hCouter : 0 ≤ Couter) (hCcal : 1 ≤ Ccal)
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2) (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F)
    (hc0 : 0 < c0) (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0) (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale) (hWlim : Tendsto W atTop (𝓝 0))
    (w : ℕ→ActualSlowWindowChoice)
    (Hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cs (w n)) :
    ∃Cf Ci : ℝ,0 ≤ Cf ∧ 0 < Ci ∧ (∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf) ∧
      ∃eps : ℕ→ℝ,(∀n,0 ≤ eps n) ∧ Tendsto eps atTop (𝓝 0) ∧
      ActualHistorySecondLowFullWeightedForestB0ModulusOnEveryFinalNetAlong seedBound k₀ r₀ depth Cmass Ccut Couter Rmacro Cx
        (actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp) cK Ci eps dim M W w := by
  obtain ⟨Cf,Ci,hCf,hCi,HS,eps,heps,HL,H⟩:=actual_second_low_actual_history_full_half_retarget_B0_modulus_along
    (seedBound+k₀+depth) (r₀+6*depth) Cmass Ccut Couter Ccal Rmacro F Cx hCx hTemp hCm hCcut hCouter hCcal
    heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius hc0 hmargin hcapmargin
    dim hdim root M epsilon shell hepsilon hb hh Hhistory W hcanonical hWlim w Hcompare hw
  have HX : ∀ᶠn in atTop,(M n).xs ≤ 1:=by
    filter_upwards [hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with n hn
    rw [hcanonical n] at hn
    exact (M n).canonical_direct_test_band_ge_scale.trans hn
  obtain ⟨CiForest,hCiForest,epsForest,hepsForest,HLForest,HForest⟩:=
    actual_second_low_full_weighted_forest_from_actual_half_rows_along seedBound k₀ r₀ depth
      Cmass Ccut Couter Rmacro Cx cK Ci eps hTemp hCf hcK hCi heps HL dim M W w HS HX H
  exact ⟨Cf,CiForest,hCf,hCiForest,HS,epsForest,hepsForest,HLForest,HForest⟩

end OAI.SKFluctuations.Cavity
