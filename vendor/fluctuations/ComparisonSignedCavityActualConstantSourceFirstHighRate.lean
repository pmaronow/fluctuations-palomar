module

public import ComparisonSignedCavityInheritedFourFirstHighForest
public import ComparisonSignedCavityActualConstantChildHighProfile
public import ComparisonSignedCavityActualConstantJointFourReadout

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
set_option maxHeartbeats 26000000

theorem eventually_actual_shell_history_constant_source_first_high_rate
    (depth : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F cK : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCm : 0≤Cmass) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct)
    (hCcal : 1≤Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro≤1/2)
    (hFmass : 1+2*cu≤F) (hFradius : 1+1/Rmacro≤F)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1)≤c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell Ttotal : ℝ) (ts : List ComparisonHistoryTerm),
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u∈Icc (0:ℝ) 1,M.h u+M.b u≤Ttotal) →
        M.xs^2≤Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale≤Rmacro/2 →
        (Az+1/cl)*(1+Cmass)*M.canonicalDirectTestBandScale≤Rmacro/4 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(star U : ℕ) (hs : star < U) (hU : U≤as.length),
          2*c*W≤partitionPoint 0 as U → partitionPoint 0 as star≤Cmass*W →
          cK*W≤nativeContinuumMixedClock n M.bf M.hf as star →
        ((nativeActualMinimumFourCenteredForest M hs hU W depth
          (nativeActualConstantSourceChildren M as star U hs hU)).map
          (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  let rBound:=3+6*depth
  let Cweight:=(Temp+2*Cf)/(Real.exp (-4*(Temp+2*Cf))*cK)
  have hw0 : 0≤Cweight:=by dsimp only [Cweight];positivity
  let V:=nativeActualWeightedProfileFrontierCost nativeActualOriginalFourGCenteredBranches Cweight 3 3 depth
  have hV : 0≤V:=nativeActualWeightedProfileFrontierCost_nonneg _ hw0 _ _ _
  obtain ⟨C₀,hC₀,Hsource⟩:=eventually_actual_minimum_inherited_four_first_high_profile
    (D:=D) (1+depth) Bclock Temp Cf Cmass Ccal Rmacro F cK hTemp hCf hCm hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  have Htail:=eventually_actual_shell_history_original_high_envelope_powers (D:=D) (Cs:=Ccal^2)
    Bclock Temp Cf hTemp hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg Ccal) hc hcouter
  let C₁:=12*C₀*nativeGammaFirstHighVariation (rBound+1)*V
  have hC₁ : 0≤C₁:=by dsimp only [C₁];exact mul_nonneg (mul_nonneg (by positivity)
    (nativeGammaFirstHighVariation_nonneg _)) hV
  let C:=C₁+1
  refine ⟨C,by dsimp only [C];linarith,?_⟩
  filter_upwards [Hsource,Htail] with n hnSource hnTail
  intro M Tbase epsilon shell Ttotal ts hb hh hsource htotal hcompare hmacroW hsmall L us hus hret hmesh
  have hW1 : M.canonicalDirectTestBandScale≤1:=by linarith
  have hxs1 : M.xs≤1:=M.canonical_direct_test_band_ge_scale.trans hW1
  filter_upwards [hnSource M hsource hxs1 hcompare L us hus hret hmesh,
    hnTail M Tbase epsilon shell ts hb hh hcompare hW1 us hus] with jGrid hgridSource hgridTail
  dsimp only at hgridSource hgridTail ⊢
  intro star U hs hU hcutlo hms hstarK
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let Γ:=nativeOriginalHighRowGamma (n:=n) (as:=as) U K
  let weight:=fun (st : NativeActualResourceState (Spin n×Bool) as 0 star) tag=>
    nativeOriginalClockParentWeight W U K st (nativeOriginalClockFourGBranchBeta U K b st tag)
  let children:=nativeActualConstantSourceChildren M as star U hs hU
  let rows:=nativeActualMinimumFourCenteredForest M hs hU W depth children
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as (4*Cf+2*Temp) Temp
  have ho:=finiteCutMasses_ordered us hus jGrid
  have hW : 0 < W:=M.canonical_direct_test_band_pos
  have hlo j (hj : j < U) : R j=0:=by simp [R,nativeOriginalHighErrorEnvelope,hj]
  have hR j : 0≤R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have Hrate : W*edgeBudget 0 as R≤M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2:=by
    have HH:=hgridTail U hU hcutlo 2 (by norm_num) (by norm_num)
      (show 2-(2:ℝ)≤actualMassSavingExponent m delta/128 by
        have Heta:=actualMassSavingExponent_pos hm hdelta;linarith)
    have Hextra:=edgeBudget_nonneg ho (fun j=>Real.rpow_nonneg (hR j) 2)
    change edgeBudget 0 as (fun j=>R j^(2:ℝ))+W*edgeBudget 0 as R≤_ at HH
    linarith
  have Hrow Q (hQ : Q∈rows) : |nativeActualOriginalFourFirstHighError M U W Q|≤
      |Q.term.coefficient| *C₀*W*nativeGammaFirstHighVariation (rBound+1)*
        (Q.tree.forkCost R+edgeBudget 0 as R):=by
    have Hvalid:=nativeActualFourCenteredForest_valid Γ hs (hs.le.trans hU) weight depth children
      (seed:=[]) (fun P hP=>nativeActualConstantSourceChildren_valid M hs hU P hP) Q hQ
    have Hdepth:=nativeActualFourCenteredForest_generation_bound Γ hs (hs.le.trans hU) weight depth children
      1 (fun P hP=>nativeActualConstantSourceChildren_generation M hs hU P hP) Q hQ
    have Hleaf:=nativeActualFourCenteredForest_leaves_bound Γ hs (hs.le.trans hU) weight depth children
      3 (fun P hP=>nativeActualConstantSourceChildren_leaves M hs hU P hP) Q hQ
    have Hdegree : Q.term.resources.length≤1+depth:=by rw [Hvalid.total_factor_depth];simp only [List.length_nil,zero_add];omega
    have Hmi : partitionPoint 0 as 0≤Cmass*M.xs:=by
      simpa only [partitionPoint,partitionValues_zero,id_eq] using mul_nonneg hCm M.hxs.le
    have H:=hgridSource 0 star U rBound [] Q Hvalid Hdegree (Nat.zero_le _) hs hU Hleaf
      hmacroW hsmall Hmi hms hstarK
    simpa only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one] using H
  have HS : (rows.map (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum≤
      C₀*W*nativeGammaFirstHighVariation (rBound+1)*
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
      as ho hs hU hstarK Q tag) depth children 3
    (fun P hP=>nativeActualConstantSourceChildren_leaves M hs hU P hP) R hR hlo
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hchi:=actual_minimum_continuum_susceptibility_mem_unit M htotal as ho U (by omega) hU
  have hchi : |chi|≤1:=by rw [abs_of_nonneg Hchi.1];exact Hchi.2
  have Hfamily : (children.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum≤
      6*edgeBudget 0 as R:=by
    have H:=native_actual_constant_child_family_wholeProfile_le (i:=0) ho Γ
      (fun Q p _=>nativeOriginalHighRowGamma_abs_le_one ho U K Q p) hs hU chi hchi R hR hlo
    norm_num only [nativeActualProfileOpVariation,Nat.cast_one] at H
    exact H
  have Hprofile:=Hhist.trans (mul_le_mul_of_nonneg_left Hfamily (by positivity : 0≤2*V))
  have Hscaled:=mul_le_mul_of_nonneg_left Hprofile
    (show 0≤C₀*W*nativeGammaFirstHighVariation (rBound+1) by
      exact mul_nonneg (by positivity) (nativeGammaFirstHighVariation_nonneg _))
  have Hsaved:=mul_le_mul_of_nonneg_left Hrate hC₁
  apply HS.trans
  apply Hscaled.trans
  calc
    _=C₁*(W*edgeBudget 0 as R):=by dsimp only [C₁,V];ring
    _≤C₁*(M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2):=Hsaved
    _≤C*(M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2):=by
      gcongr
      dsimp only [C]
      linarith
    _=_:=by ring

end OAI.SKFluctuations.Cavity
