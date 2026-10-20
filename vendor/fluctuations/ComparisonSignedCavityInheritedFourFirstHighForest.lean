module

public import ComparisonSignedCavityInheritedFourFirstHighProfile
public import ComparisonSignedCavityActualFourForestHighProfile
public import ComparisonSignedCavityActualFourResourceIteration
public import ComparisonSignedCavityActualSmallSourceFourWeights
public import ComparisonNativeActualInheritedHighTailPowers

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_shell_history_four_first_high_forest_rate
    (depth k₀ seedBound r₀ : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F cK : ℝ)
    (hTemp : 0  ≤  Temp) (hCf : 0  ≤  Cf) (hCm : 0  ≤  Cmass) (hcK : 0<cK)
    {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hCcal : 1  ≤  Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro  ≤  1/2)
    (hFmass : 1+2*cu  ≤  F) (hFradius : 1+1/Rmacro  ≤  F)
    (hc : 0<c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        NativeActualSmallSourceClocks M Temp Cf →
        M.xs^2  ≤  Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale  ≤  Rmacro/2 →
        (Az+1/cl)*(1+Cmass)*M.canonicalDirectTestBandScale  ≤  Rmacro/4 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val  ≤  1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹  ≤  M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (_hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length)
          (seed : List NativeResourceMark) (st : NativeActualResourceState (Spin n×Bool) as i star),
          seed.length ≤ seedBound → st.generation=k₀ → st.tree.leaves ≤ r₀ →
          NativeActualResourceGenerated i star U seed st.generation st.tree st.term →
          (∀f : ℕ→ℝ,(∀j,j<U→f j=0)→st.tree.forkCost f=0) →
          2*c*W ≤ partitionPoint 0 as U →
          partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
          cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
          (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum  ≤
          |st.term.coefficient| *C*M.context.N^(-(actualMassSavingExponent m delta/256))*
            nativeResourceScale M.xs W 1 seed*M.xs^2 := by
  let rBound:=r₀+6*depth
  let Ttot:=Temp+2*Cf
  let Cweight:=Ttot/(Real.exp (-4*Ttot)*cK)
  have hw0 : 0 ≤ Cweight:=by dsimp only [Cweight,Ttot];positivity
  let V:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cweight 3 r₀ depth
  have hV : 0 ≤ V:=nativeActualWeightedProfileFrontierCost_nonneg _ hw0 _ _ _
  obtain ⟨C₀,hC₀,Hsource⟩:=eventually_actual_minimum_inherited_four_first_high_profile
    (D:=D) (seedBound+k₀+depth) Bclock Temp Cf Cmass Ccal Rmacro F cK hTemp hCf hCm hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers (D:=D) (Cs:=Ccal^2)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hc hcouter
  let C₁:=2*C₀*nativeGammaFirstHighVariation (rBound+1)*V
  have hC₁ : 0 ≤ C₁:=by dsimp only [C₁];exact mul_nonneg (mul_nonneg (by positivity)
    (nativeGammaFirstHighVariation_nonneg _)) hV
  let C:=C₁+1
  refine ⟨C,by dsimp only [C];linarith,?_⟩
  filter_upwards [Hsource,Htail] with n hnSource hnTail
  intro M Tbase epsilon shell ts hb hh hsource hcompare hmacroW hsmall L us hus hret hmesh
  have hW1 : M.canonicalDirectTestBandScale ≤ 1:=by linarith
  have hxs1 : M.xs ≤ 1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnSource M hsource hxs1 hcompare L us hus hret hmesh,
    hnTail M Tbase epsilon shell ts hb hh hcompare hW1 us hus] with jGrid hgridSource hgridTail
  dsimp only at hgridSource hgridTail ⊢
  intro i star U hi hs hU seed st hseedlength hgen hleaf hP hfork hcutlo hmi hms hstarK
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (Q : NativeActualResourceState (Spin n×Bool) as i star) tag=>
    nativeOriginalClockParentWeight W U K Q (nativeOriginalClockFourGBranchBeta U K b Q tag)
  let rows:=nativeActualMinimumFourCenteredForest M hs hU W depth [st]
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hW : 0<W:=M.canonical_direct_test_band_pos
  have hlo j (hj : j<U) : R j=0:=by simp [R,nativeOriginalHighErrorEnvelope,hj]
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hrate : W*edgeBudget 0 as R ≤ M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=by
    have HH:=hgridTail U hU hcutlo 2 (by norm_num) (by norm_num)
      (show 2-(2:ℝ) ≤ actualMassSavingExponent m delta/128 by
        have Heta:=actualMassSavingExponent_pos hm hdelta;linarith)
    have Hextra:=edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) 2)
    change edgeBudget 0 as (fun j=>R j^ (2:ℝ))+W*edgeBudget 0 as R ≤ _ at HH
    linarith
  have hseed : 0 ≤ nativeResourceScale M.xs W 1 seed:=by
    unfold nativeResourceScale
    apply List.prod_nonneg
    intro z hz
    obtain ⟨mark,hm,rfl⟩:=List.mem_map.mp hz
    exact (mark.savedScale_pos M.hxs hW zero_lt_one).le
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourFirstHighError M U W Q| ≤
      |Q.term.coefficient| *C₀*nativeResourceScale M.xs W 1 seed*W*
        nativeGammaFirstHighVariation (rBound+1)*(Q.tree.forkCost R+edgeBudget 0 as R):=by
    have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth [st]
      (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hP) Q hQ
    have Hdepth:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth [st]
      k₀ (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hgen) Q hQ
    have Hleaf:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth [st]
      r₀ (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hleaf) Q hQ
    have Hdegree : Q.term.resources.length ≤ seedBound+k₀+depth:=by
      rw [Hvalid.total_factor_depth]
      omega
    exact hgridSource i star U rBound seed Q Hvalid Hdegree hi hs hU Hleaf hmacroW hsmall hmi hms hstarK
  have HS : (rows.map (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum ≤
      C₀*nativeResourceScale M.xs W 1 seed*W*nativeGammaFirstHighVariation (rBound+1)*
        (rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum:=by
    apply (List.sum_le_sum Hrow).trans_eq
    rw [←List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro Q hQ
    ring
  have Hhist:=nativeActualFourCenteredForest_wholeProfile_le ho Γ
    (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs (hs.le.trans hU)
    weight hw0 (fun Q tag=>actual_continuum_four_G_weight_bound_of_small_source_clocks M hCf hsource hxs1 hW hcK
      as ho hs hU hstarK Q tag) depth [st] r₀
    (by intro P hP';have HP:=List.mem_singleton.mp hP';subst P;exact hleaf) R hR hlo
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,hfork R hlo,zero_add] at Hhist
  have Hscaled:=mul_le_mul_of_nonneg_left Hhist
    (show 0 ≤ C₀*nativeResourceScale M.xs W 1 seed*W*nativeGammaFirstHighVariation (rBound+1) by
      exact mul_nonneg (by positivity) (nativeGammaFirstHighVariation_nonneg _))
  have Hsaved:=mul_le_mul_of_nonneg_left Hrate
    (show 0 ≤ |st.term.coefficient| *C₁*nativeResourceScale M.xs W 1 seed by positivity)
  apply HS.trans
  apply Hscaled.trans
  calc
    _=|st.term.coefficient| *C₁*nativeResourceScale M.xs W 1 seed*(W*edgeBudget 0 as R):=by
      dsimp only [C₁,V]
      ring
    _ ≤ |st.term.coefficient| *C₁*nativeResourceScale M.xs W 1 seed*
      (M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2):=Hsaved
    _ ≤ |st.term.coefficient| *C*nativeResourceScale M.xs W 1 seed*
      (M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2):=by
      gcongr
      dsimp only [C]
      linarith
    _=_:=by ring

end OAI.SKFluctuations.Cavity
