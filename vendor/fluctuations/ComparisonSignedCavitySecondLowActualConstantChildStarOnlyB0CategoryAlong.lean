module

public import ComparisonSignedCavitySecondLowActualConstantResourceStarOnlyHalfB0SavingAlong
public import ComparisonSignedCavityActualSmallSourceTaylorDenominator
public import ComparisonSignedCavityActualFourForestTaylorVariation
public import ComparisonSignedCavityActualConstantJointFourReadout
public import ComparisonSignedCavityActualConstantChildHighProfile
public import ComparisonSignedCavitySecondLowActualRetainedStarSplit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

def ActualConstantChildStarOnlyFullB0CategoryOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (depth : ℕ) (Cmass Couter Rmacro Cx cK : ℝ) (err : ℕ→ℝ) (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop:=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (w n).star∈us → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
  ∀ᶠjGrid in atTop,
    let as:=finiteCutMasses us jGrid
    ∀(mid tail : List PositiveMass),as=mid++tail → mid.length=retainedMassPrefixIndex (w n).star.val as →
    ∀(U : ℕ) (hs : mid.length<U) (hU : U ≤ (mid++tail).length),
      partitionPoint 0 as U ≤ Couter*W n → partitionPoint 0 as mid.length ≤ Cmass*W n →
      4*W n ≤ (M n).R (partitionPoint 0 as U) →
      (M n).z ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
      (M n).R (partitionPoint 0 as mid.length) ≤ min ((M n).R (partitionPoint 0 as U)/8) (Rmacro/4) →
    ∀(sourceMass : ℝ) (hsourceMass : 0 < sourceMass),Cx*(M n).xs ≤ sourceMass → partitionPoint 0 as U=sourceMass →
      (∀j ≤ nativeDyadicCutDepth sourceMass,nativeDyadicMassCut sourceMass hsourceMass j∈us) →
      cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as mid.length →
    let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (mid++tail)
    let chi:=(scalarTerminal.schedule (scalarBoundaryClocks (mid++tail) (relocatedClock U 0 K))).H 0 0
    |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
      (nativeActualConstantSourceChildren (M n) (mid++tail) mid.length U hs hU)).map
      (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q .secondLow)).sum|/
      (chi*K mid.length) ≤ err n*(M n).xs^2

theorem actual_constant_child_star_only_full_B0_from_actual_half_rows_along
    (depth : ℕ) (Bclock Temp Cf Cmass Couter Rmacro Cx cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D : ℝ}
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (w : ℕ→ActualSlowWindowChoice) (eps : ℕ→ℝ)
    (heps : ∀n,0 ≤ eps n) (HL : Tendsto eps atTop (𝓝 0))
    (Hrows : ActualConstantResourceStarOnlyFullHalfB0SavingOnEveryFinalNetAlong
      (1+depth) (3+6*depth) Cmass Couter Rmacro Cx eps dim M W w) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧
      ActualConstantChildStarOnlyFullB0CategoryOnEveryFinalNetAlong depth Cmass Couter Rmacro Cx cK err dim M W w := by
  let degree:=1+depth
  let rBound:=3+6*depth
  let Cd:=Real.exp (-4*(Temp+2*Cf))*cK
  let Cw:=(Temp+2*Cf)/Cd
  let Vv:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 3 depth
  have hCd : 0 < Cd:=by dsimp only [Cd];positivity
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  have hVv : 0 ≤ Vv:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  let err:=fun n=>(12*Vv/Cd)*eps n
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,mul_zero] using HL.const_mul (12*Vv/Cd)
  refine ⟨err,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [Hrows,Hsource,HW1] with n hnL hsource hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hepsn:=heps n
  have hxs1:=hxW.trans hW1
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hstar hret hmesh
  filter_upwards [hnL L us hus hstar hret hmesh] with jGrid hgridL
  dsimp only at hgridL ⊢
  intro mid tail hparts hindex U hs hU hcut hmassstar Hhigh Hz Hrs sourceMass hsourceMass HCx HsourceMass Hnodes hstarK
  rw [hparts] at hgridL hindex hcut hmassstar Hhigh Hz Hrs HsourceMass hstarK
  let as:=mid++tail
  let star:=mid.length
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let b:=fun j=>((M n).bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=dim n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin (dim n)×Bool) as 0 star) tag=>
    nativeOriginalClockParentWeight (W n) U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let children:=nativeActualConstantSourceChildren (M n) as star U hs hU
  let rows:=nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth children
  have ho : MassOrdered 0 as:=by dsimp only [as];rw [←hparts];exact finiteCutMasses_ordered us hus jGrid
  have HW Q tag : |weight Q tag| ≤ Cw:=
    actual_continuum_four_G_weight_bound_of_small_source_clocks (M n) hCf hsource hxs1 hW hcK as ho hs hU hstarK Q tag
  have Hleaves Q (hQ : Q∈children) : Q.tree.leaves ≤ 3:=nativeActualConstantSourceChildren_leaves (M n) hs hU Q hQ
  have Hvalid Q (hQ : Q∈rows) := nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
    (fun P hP=>nativeActualConstantSourceChildren_valid (M n) hs hU P hP) Q hQ
  have Hgen Q (hQ : Q∈rows) := nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
    1 (fun P hP=>nativeActualConstantSourceChildren_generation (M n) hs hU P hP) Q hQ
  have Hleaf Q (hQ : Q∈rows) :=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
    3 Hleaves Q hQ
  have hmid : 0 < mid.length:=by
    have H:=native_retained_positive_star_split (finiteCutMasses us jGrid)
      (finiteCutMasses_ordered us hus jGrid) (w n).star
      (finiteCutMasses_nodes us jGrid hstar)
    dsimp only at H
    have HI:=(H.2.1.symm ▸ H.2.2)
    simpa only [hparts,hindex] using HI
  have Hrow Q (hQ : Q∈rows) :
      |((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q .secondLow| ≤
        |Q.term.coefficient| *eps n*W n*(M n).xs^2:=by
    have HV:=Hvalid Q hQ
    have HG:=Hgen Q hQ
    have HT:=Hleaf Q hQ
    exact hgridL mid tail rfl hindex U hU Q HV
      (by omega) hmid hs (by omega)
      hcut hmassstar Hhigh Hz Hrs sourceMass hsourceMass HCx HsourceMass Hnodes
  have Hvariation:=nativeActualFourCenteredForest_coefficient_variation_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU) weight
    hCw HW depth children 3 Hleaves
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi1,hdenLower⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks (M n)
    hCf hsource hxs1 hW hcK ho hs hU hstarK
  have hKpos : 0 < K star:=(mul_pos hcK hW).trans_le hstarK
  have hchi0 : 0 ≤ chi:=by nlinarith
  have hchi : |chi| ≤ 1:=by rw [abs_of_nonneg hchi0];exact hchi1
  have Hcoeff : (children.map (fun Q=>|Q.term.coefficient|)).sum ≤ 6:=by
    have H:=native_actual_constant_child_family_coefficient_variation_le (i:=0) ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi
    norm_num only [NativeActualExpansionOp.coefficientCost,Nat.cast_one] at H
    exact H
  have Htotal : (rows.map (fun Q=>|Q.term.coefficient|)).sum ≤ 12*Vv:=by
    apply Hvariation.trans
    have H:=mul_le_mul_of_nonneg_left Hcoeff (show 0 ≤ 2*Vv by positivity)
    convert H using 1
    ring
  have Habs:=native_abs_sum_map_le rows
    (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q .secondLow)
  have Hsum:=List.sum_le_sum Hrow
  rw [List.sum_map_mul_right,List.sum_map_mul_right,List.sum_map_mul_right] at Hsum
  have Hnum : |(rows.map (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q .secondLow)).sum| ≤
      12*Vv*eps n*W n*(M n).xs^2:=by
    apply Habs.trans (Hsum.trans ?_)
    have H:=mul_le_mul_of_nonneg_right Htotal
      (show 0 ≤ eps n*W n*(M n).xs^2 by positivity)
    convert H using 1 <;> ring
  apply (div_le_iff₀ hden).2
  apply Hnum.trans
  have H:=mul_le_mul_of_nonneg_left
    (show Cd*W n ≤ chi*K star from hdenLower)
    (show 0 ≤ err n*(M n).xs^2 by dsimp only [err];positivity)
  convert H using 1
  dsimp only [err]
  field_simp

end OAI.SKFluctuations.Cavity
