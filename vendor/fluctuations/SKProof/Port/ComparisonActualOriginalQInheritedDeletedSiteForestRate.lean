module

public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQCriticalScaleNumerics
public import SKProof.Port.ComparisonActualOriginalQRawResourcePairBudget
public import SKProof.Port.ComparisonActualOriginalQPullbackFourCutReadout
public import SKProof.Port.ComparisonActualOriginalQCavityCategoryInterfaces
public import SKProof.Port.ComparisonActualOriginalQActualDeletedSiteContrast
public import ComparisonSignedCavityActualDeletedSiteContrast
public import ComparisonSignedCavityActualConstantSourceCategoryReduction
public import ComparisonSignedCavityInheritedFourGaCurrentForest

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 28000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_minimum_inherited_deleted_site_forest_rate_original_q
    (seedBound k₀ r₀ depth : ℕ) (Bclock Temp Cf Cmass cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
        ActualOriginalQSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        ∀(U i star : ℕ) (seed : List NativeResourceMark)
          (st : NativeActualResourceState (Spin n×Bool) as i star),
          seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves ≤ r₀ →
          NativeActualResourceGenerated i star U seed st.generation st.tree st.term → i ≤ star →
        ∀(hs : star < U) (hU : U ≤ as.length),
        ∀x W : ℝ,M.xs ≤ x → x ≤ W →
          partitionPoint 0 as i ≤ Cmass*x → partitionPoint 0 as star ≤ Cmass*W →
          cK*W ≤ nativeContinuumMixedClock n M.sweepBf M.sweepHf as star →
          |nativeActualFourOtherCategorySum_original_q M U W
            (nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [st]) .deletedSite| ≤
            C*|st.term.coefficient| *((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2)*
              nativeResourceScale x W 1 seed := by
  obtain ⟨C₀,hC₀,HR⟩:=eventually_actual_minimum_inherited_centered_deleted_site_rate_original_q
    (D:=D) (seedBound+k₀+depth) Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cw:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hCw : 0 ≤ Cw:=by dsimp only [Cw];positivity
  let Vcost:=nativeActualWeightedFrontierCost nativeActualOriginalFourGCenteredBranches Cw 3 r₀ depth
  have hVcost : 0 ≤ Vcost:=nativeActualWeightedFrontierCost_nonneg _ hCw _ _ _
  let C:=2*Vcost*((3/2:ℝ)*C₀)+1
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HR] with n hn
  intro M hs0 hsxs hsource hxs1 L us hus hret hmesh
  filter_upwards [hn M hs0 hsxs hsource hxs1 L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  have ho:=finiteCutMasses_ordered us hus jGrid
  intro U i star seed st hseed hgen hleaf hP hi hs hU x W hxsx hxW hmi hms HK
  let K:=nativeContinuumMixedClock n M.sweepBf M.sweepHf as
  let b:=fun j=>(M.sweepBf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest_original_q M hs hU W depth [st]
  let rate:=((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2)*nativeResourceScale x W 1 seed
  let B:=(3/2:ℝ)*C₀*rate
  have hx : 0 < x:=M.hxs.trans_le hxsx
  have hW : 0 < W:=hx.trans_le hxW
  have hscale : 0 < nativeResourceScale x W 1 seed:=native_resource_raw_scale_pos _ hx hW
  have hrate : 0 ≤ rate:=by dsimp only [rate];positivity
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  have Hrow Q (hQ : Q∈rows) :
      |(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_original_q M U Q .deletedSite| ≤
        B*|Q.term.coefficient|:=by
    have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
      (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hP) Q hQ
    have Hdepth:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
      k₀ (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hgen) Q hQ
    have Hdegree : seed.length+Q.generation ≤ seedBound+k₀+depth:=by omega
    have H0 : |(W⁻¹)^Q.generation*nativeActualOriginalCenteredResourceDeletedSite_original_q M U Q| ≤
        C₀*|Q.term.coefficient| *rate:=by
      have H:=hj U i star Q.generation Q.tree Q.term seed Hvalid Hdegree hi (by omega)
        x W hxsx hxW hmi hms
      exact H.trans_eq (by dsimp only [rate,nativeActualOriginalCenteredResourceDeletedSite_original_q];ring)
    have H1 : |(W⁻¹)^Q.generation*nativeActualOriginalCenteredResourceDeletedSite_original_q M U Q.retarget| ≤
        C₀*|Q.term.coefficient| *rate:=by
      have H:=hj U i star Q.generation _ (Q.term.retarget 0) seed Hvalid.retarget Hdegree hi (by omega)
        x W hxsx hxW hmi hms
      exact H.trans_eq (by dsimp only [rate,nativeActualOriginalCenteredResourceDeletedSite_original_q,
        NativeActualResourceState.retarget,NativeResourceTerm.retarget];ring)
    exact (native_actual_original_deleted_site_contrast_abs_le_original_q M U ho Q W _ H0 H1).trans_eq
      (by dsimp only [B];ring)
  have Hsum:=nativeActualFourCenteredForest_singleton_abs_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    weight hCw (fun Q tag=>actual_continuum_four_G_weight_bound_of_small_source_clocks_original_q
      M hCf hsource hxs1 hW hcK as ho hs hU HK Q tag) depth st hleaf
    (fun Q=>(W⁻¹)^Q.generation*nativeActualOriginalFourOtherCategoryContrast_original_q M U Q .deletedSite)
    hB (fun Q hQ=>(Hrow Q hQ).trans_eq (mul_comm _ _))
  change |nativeActualFourOtherCategorySum_original_q M U W rows .deletedSite| ≤ _ at Hsum
  apply Hsum.trans
  have HC : 2*Vcost*((3/2:ℝ)*C₀) ≤ C:=by dsimp only [C];linarith
  have HH:=mul_le_mul_of_nonneg_left HC (mul_nonneg (abs_nonneg st.term.coefficient) hrate)
  calc
    _=|st.term.coefficient| *rate*(2*Vcost*((3/2:ℝ)*C₀)):=by dsimp only [B,Vcost];ring
    _≤|st.term.coefficient| *rate*C:=HH
    _=_:=by dsimp only [rate];ring

end OAI.SKFluctuations.Cavity
