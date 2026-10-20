module

public import ComparisonSignedCavityActualInitialHigherTaylorForestModulusAlong
public import ComparisonSignedCavityActualHigherTaylorCategorySum
public import ComparisonSignedCavityInitialInheritedFreshResourceThirdLowSavingAlong
public import ComparisonSignedCavityActualFreshResourceHighTaylorFromMinimum
public import ComparisonSignedCavityActualOriginalHighProfileHistory
public import ComparisonSignedCavityActualExpansionInitialTerminal
public import ComparisonSignedCavityActualFourForestTaylorProfile
public import ComparisonSignedCavityActualConstantChildHighProfile
public import ComparisonSignedCavityActualConstantJointFourReadout
public import ComparisonNativeActualInheritedHighTailPowers

@[expose] public section

noncomputable section
set_option autoImplicit false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem actual_inherited_initial_higher_Taylor_category_modulus_along
    (depth : ℕ) (Bclock Temp Cf Cmass Cinitial Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCinitial : 0 ≤ Cinitial) (hCcut : 0 < Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c Tstar Lwin Cwindow : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,∃(Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase epsilon shell ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u))
    (w : ℕ→ActualSlowWindowChoice)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n)) :
    ∃Ci : ℝ,0 < Ci ∧ ∃err : ℕ→ℝ,(∀n,0 ≤ err n) ∧ Tendsto err atTop (𝓝 0) ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let star:=retainedMassPrefixIndex (w n).star.val as
        ∀(i V U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W n ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W n →
        0 < V → i < V → V ≤ star → partitionPoint 0 as V ≤ Cinitial*(M n).xs →
        partitionPoint 0 as i ≤ Cmass*(M n).xs →
        partitionPoint 0 as star ≤ Cmass*W n →
        cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ∀seedMass : ℝ,
        let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
          [nativeActualInitialState as i star seedMass (hi.trans (hs.le.trans hU))]).map
          (fun Q=>((W n)⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast (M n) U Q .higherTaylor)).sum|/
          (chi*K star) ≤
            Ci*(M n).xs^2*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius (dim n) (M n).bf (M n).hf as i+1/(dim n+1:ℕ))+
              err n*(M n).xs^3 := by
  obtain ⟨Ci,hCi,err,herr,Herr,H⟩:=actual_inherited_initial_higher_Taylor_forest_modulus_along
    depth Bclock Temp Cf Cmass Cinitial Ccut cK hTemp hCf hCmass hCinitial hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource hsmall Hshell w hw
  refine ⟨Ci,hCi,err,herr,Herr,?_⟩
  have HW1:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  filter_upwards [H,Hsource,HW1] with n hn hsClocks hW1
  have hxW:(M n).xs≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hxs1:=hxW.trans hW1
  have hW:0< W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with jGrid hj
  dsimp only at hj ⊢
  intro i V U hi hs hU hcutlo hcut hV hiV hVstar hcutI hmi hmassstar hstarK seedMass
  apply (actual_higher_Taylor_category_signed_sum_abs_le_error_sum (M n) hCf hsClocks hxs1
    (finiteCutMasses_ordered us hus jGrid) hs hU hW hcK hstarK _).trans
  exact hj i V U hi hs hU hcutlo hcut hV hiV hVstar hcutI hmi hmassstar hstarK seedMass

end OAI.SKFluctuations.Cavity
