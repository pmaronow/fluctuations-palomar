module

public import ComparisonSignedCavityInheritedFourFirstHighRoots
public import ComparisonNativeActualSelectedBadHistorySourceClocks

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
set_option maxHeartbeats 18000000

theorem actual_selected_bad_history_four_first_high_initial_rate_along
    (depth : ℕ) (Cmass cK : ℝ) (hCm : 0 ≤ Cmass) (hcK : 0<cK)
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=(M n).canonicalDirectTestBandScale
        ∀(i star U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (a : ℝ),
          2*c*W ≤ partitionPoint 0 as U →
          partitionPoint 0 as i ≤ Cmass*(M n).xs → partitionPoint 0 as star ≤ Cmass*W →
          cK*W ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ((nativeActualMinimumFourCenteredForest (M n) hs hU W depth
          [nativeActualInitialState as i star a (by omega)]).map
          (fun Q=>|nativeActualOriginalFourFirstHighError (M n) U W Q|)).sum ≤
          C*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^3 := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_four_first_high_initial_rate
    (D:=D) depth Bclock Temp Cf Cmass Ccal (1/2) (4+2*cu) cK
    hTemp hCf hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal
    (by norm_num) (by norm_num) (by linarith) (by norm_num;linarith) hc hcouter
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/4))
  have HG : ∀ᶠn in atTop,(Az+1/cl)*(1+Cmass)*(M n).canonicalDirectTestBandScale ≤ (1:ℝ)/8:=by
    have H:=hWlim.const_mul ((Az+1/cl)*(1+Cmass))
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/8))
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually HR,Hsource,Hps,hcompare,HW,HG] with n hn hs hp hcali hw hg
  exact hn (M n) Temp epsilon shell ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
    hp.2.1 hp.2.2 hs hcali (by norm_num at hw ⊢;exact hw) (by norm_num at hg ⊢;exact hg)

theorem actual_selected_bad_history_four_first_high_projected_constant_rate_along
    (depth : ℕ) (Cmass cK : ℝ) (hCm : 0 ≤ Cmass) (hcK : 0<cK)
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (hWlim : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn in atTop,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=(M n).canonicalDirectTestBandScale
        ∀(star U : ℕ) (hs : star<U) (hU : U ≤ as.length),
          2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as star ≤ Cmass*W →
          cK*W ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star →
        ((nativeActualMinimumFourCenteredForest (M n) hs hU W depth
          [(nativeActualConstantState as 0 star).projection (hs.le.trans hU)]).map
          (fun Q=>|nativeActualOriginalFourFirstHighError (M n) U W Q|)).sum ≤
          C*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^2 := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_four_first_high_projected_constant_rate
    (D:=D) depth Bclock Temp Cf Cmass Ccal (1/2) (4+2*cu) cK
    hTemp hCf hCm hcK hm hdelta hroom hcl hcu hAz hC0 hCt hCcal
    (by norm_num) (by norm_num) (by linarith) (by norm_num;linarith) hc hcouter
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/4))
  have HG : ∀ᶠn in atTop,(Az+1/cl)*(1+Cmass)*(M n).canonicalDirectTestBandScale ≤ (1:ℝ)/8:=by
    have H:=hWlim.const_mul ((Az+1/cl)*(1+Cmass))
    simp only [mul_zero] at H
    exact H.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1/8))
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually HR,Hsource,Hps,hcompare,HW,HG] with n hn hs hp hcali hw hg
  exact hn (M n) Temp epsilon shell ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
    hp.2.1 hp.2.2 hs hcali (by norm_num at hw ⊢;exact hw) (by norm_num at hg ⊢;exact hg)

end OAI.SKFluctuations.LaplaceWindowFormalization
