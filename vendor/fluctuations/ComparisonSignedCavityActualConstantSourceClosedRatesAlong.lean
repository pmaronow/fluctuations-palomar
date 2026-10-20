module

public import ComparisonSignedCavityActualConstantSourceRatesOnCutsAlong
public import ComparisonSignedCavityActualConstantChildGaRestorationRateAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 26000000
variable {dim : ℕ → ℕ}

theorem eventually_actual_inherited_continuum_clock_mass_upper
    (Bclock Temp Cf : ℝ) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃CK : ℝ,0 < CK ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      NativeActualSmallSourceClocks M Temp Cf →
      ∀u∈Icc (0:ℝ) 1,actualMixedClock (n+1) M.bf M.hf u ≤ CK*(M.xs+u) := by
  obtain ⟨B,hB,HB⟩:=eventually_actual_minimum_mass_mean_upper
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨1+Cf+Temp*B,by positivity,?_⟩
  filter_upwards [HB] with n hn
  intro M hsource u hu
  have Hmean : orderedPathS (n+1) M.bf M.hf u ≤ B*(M.xs+u):=by
    by_cases hp : 0 < u
    · exact hn M u ⟨hp,hu.2⟩
    · have hz : u=0:=le_antisymm (le_of_not_gt hp) hu.1
      rw [hz,orderedPathS,orderedPathPair_zero]
      simpa only [add_zero] using mul_nonneg hB.le M.hxs.le
  have HC:=hsource u hu
  have Hprod:=mul_le_mul HC.1 Hmean (M.mass_mean_nonneg hu) hTemp
  have Hpos : 0 ≤ M.xs+u:=add_nonneg M.hxs.le hu.1
  dsimp only [actualMixedClock]
  nlinarith only [HC.2,Hprod,Hpos]

def ActualConstantSourceGaRestorationOnGivenCutsAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (C : ℝ)
    (M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let star:=retainedMassPrefixIndex (w n).star.val as
    let U:=retainedMassPrefixIndex (high n).val as
    ∃hs : star < U,∃hU : U ≤ as.length,
    ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
      (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourGaRestorationError (M n) U (W n) Q|)).sum ≤
      C*(M n).context.N^(-(actualMassSavingExponent m delta/256))*(M n).xs^2

theorem actual_selected_bad_history_constant_source_restoration_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass)
    (hcK : 0 < cK) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ → ActualSlowWindowChoice) (high outer : ℕ → PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceGaRestorationOnGivenCutsAlong depth C M W w high outer := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M epsilon shell hepsilon hb hh Hhistory
  obtain ⟨C,hC,HR⟩:=eventually_actual_shell_history_constant_child_G_restoration_forest_rate_along
    dim hdim depth Bclock Temp Cf Cmass Cmass cK hTemp hCf hCm hCm hcK
    (D:=D) (Cs:=Ccal^2) hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg _) hc hcouter
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,Hsource,Hps,Htotal,Hcuts,hcompare,HW] with n hn hs hp ht hcuts hcomp hw
  intro L us hus hret hmesh hstar hhigh houter
  have H:=hn (M n) Temp epsilon shell Temp ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
    hs hp.2.1 hp.2.2 ht.1 hcomp (by simpa only [hcanonical n] using hw) L us hus hret hmesh
  filter_upwards [H] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,Houter,_,_,_,_,_,HK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter j
  refine ⟨Hs,HUV.le.trans HV,?_⟩
  have hW : 0 ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_pos.le
  have Hmass':=Hmass.trans (mul_le_mul_of_nonneg_right hA hW)
  have Hhigh':=(partitionPoint_mono _ (finiteCutMasses_ordered us hus j) HUV.le).trans
    (Houter.trans (mul_le_mul_of_nonneg_right hA hW))
  have HH:=hj _ _ Hs (HUV.le.trans HV)
    (by simpa only [hcanonical n] using Hfirst) (by simpa only [hcanonical n] using Hhigh')
    (by simpa only [hcanonical n] using Hmass') (by simpa only [hcanonical n] using HK)
  rw [show nativeActualMinimumFourCenteredForest (M n) Hs (HUV.le.trans HV) (W n) depth
    (nativeActualConstantSourceChildren (M n) (finiteCutMasses us j)
      (retainedMassPrefixIndex (w n).star.val (finiteCutMasses us j))
      (retainedMassPrefixIndex (high n).val (finiteCutMasses us j)) Hs (HUV.le.trans HV)) = _ from
      nativeActualFourCenteredForest_eq_flatMap_singletons _ _ _ _ _ _]
  simpa only [hcanonical n,nativeActualMinimumFourCenteredForest] using HH

end OAI.SKFluctuations.Cavity
