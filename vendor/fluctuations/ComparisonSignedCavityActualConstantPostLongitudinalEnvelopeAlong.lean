module

public import ComparisonSignedCavityActualConstantPostLongitudinalEnvelope
public import ComparisonSignedCavityActualConstantLongitudinalOnCutsAlong
public import ComparisonSignedCavityActualConstantPostTaylorEnvelopeAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 20000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualConstantSourcePostLongitudinalEnvelopeAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (Temp cK : ℝ) (err : ℕ→ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us → ∀ᶠjGrid in atTop,
      let as:=finiteCutMasses us jGrid
      let star:=retainedMassPrefixIndex (w n).star.val as
      let U:=retainedMassPrefixIndex (high n).val as
      ∃hs : star < U,∃hU : U ≤ as.length,
      nativeActualConstantSourcePostTaylorCategoryEnvelope (M n) hs hU (W n) Temp cK depth ≤
        nativeActualConstantSourcePostLongitudinalCategoryEnvelope (M n) hs hU (W n) Temp cK depth+
          err n*(M n).xs^2

theorem actual_selected_bad_history_constant_post_longitudinal_envelope_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK cKcut A : ℝ}
    (depth : ℕ) (Cmass : ℝ) (hCm : 0 ≤ Cmass) (hA : A ≤ Cmass)
    (hcK : 0 < cK) (hcKcut : 0 < cKcut) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
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
      (high n) (outer n) (radius n) cFirst cKcut A) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧
      ActualConstantSourcePostLongitudinalEnvelopeAlong depth Temp cK err M W w high outer := by
  have HR d:=actual_selected_bad_history_constant_longitudinal_on_given_cuts_along
    (Ccal:=Ccal) d Cmass hCm hA hcKcut hc hcouter hm hdelta hroom hcl hcu hAz hC0 hCt
    hc0 hmargin hcapmargin hdim root M epsilon shell hepsilon hTemp hb hh Hhistory
    W radius hcanonical hWlim hcompare w high outer Hcuts
  choose Cd hCd HD using HR
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  let R:=CK*(1+Cmass)
  let B:=Real.exp (-4*Temp)*cK
  have hB : 0 < B:=mul_pos (Real.exp_pos _) hcK
  have hR : 0 < R:=by dsimp only [R];positivity
  let save n:=((dim n+1:ℕ):ℝ)^(-(actualMassSavingExponent m delta/256))
  let err n:=2*((List.range depth).map Cd).sum*(R/B)*save n
  have Hpow:=(tendsto_rpow_neg_atTop (div_pos (actualMassSavingExponent_pos hm hdelta)
    (by norm_num : (0:ℝ)<256))).comp
    (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hdim))
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [err,save,Function.comp_def,mul_zero] using
      Hpow.const_mul (2*((List.range depth).map Cd).sum*(R/B))
  have HF:=Filter.eventually_all.mpr (fun d : Fin depth=>HD d.val)
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨err,Herr,?_⟩
  filter_upwards [HF,hdim.eventually HK,Hsource,Hcuts,HW] with n hn hclock hsource hcuts hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar hhigh houter
  have Hnet:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hret hmesh hstar hhigh houter)
  filter_upwards [Hnet] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,_,Hmass,_,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks
    (M n) hCf hsource (hxW.trans hW1) hW hcKcut ho hs hU HstarK
  have Hmass':=Hmass.trans (mul_le_mul_of_nonneg_right hA hW.le)
  have HKstar : K star ≤ R*W n:=by
    have H:=hclock (M n) hsource _ (partitionPoint_mem as ho star)
    change K star ≤ CK*((M n).xs+partitionPoint 0 as star) at H
    apply H.trans
    dsimp only [R]
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hxW Hmass') hCK.le]
  have Hd : chi*K star ≤ R*W n:=by
    apply (mul_le_mul_of_nonneg_right hchi
      (native_continuum_mixed_clock_nonneg (dim n) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone as ho star)).trans
    simpa only [one_mul] using HKstar
  refine ⟨hs,hU,?_⟩
  have Hpaid:=actual_constant_source_post_Taylor_envelope_longitudinal_paid
    (M n) hs hU (W n) Temp cK depth (fun d=>R/B*(Cd d*save n)) (by
      intro d hd right
      obtain ⟨_,_,H⟩:=hj ⟨d,hd⟩
      have H':=H right
      change |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d
          (nativeActualConstantSourceChildren (M n) as star U hs hU)) (nativeActualLongitudinalCategory right)|/
        (chi*K star) ≤ Cd d*save n*(M n).xs^2 at H'
      exact actual_saved_denominator_upper_transfer hden hW hB (mul_nonneg (hCd d).le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) Hd H')
  apply Hpaid.trans_eq
  dsimp only [err]
  simp only [List.sum_map_mul_left,List.sum_map_mul_right]
  ring

end OAI.SKFluctuations.Cavity
