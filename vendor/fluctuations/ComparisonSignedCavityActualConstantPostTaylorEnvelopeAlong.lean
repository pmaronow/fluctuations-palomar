module

public import ComparisonSignedCavityActualConstantPostTaylorEnvelope
public import ComparisonSignedCavityActualConstantChildHigherTaylorCategoryAlong
public import ComparisonSignedCavityActualConstantSourceClosedRatesAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
variable {dim : ℕ→ℕ}

def ActualConstantSourcePostTaylorEnvelopeAlong
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
      nativeActualConstantSourcePendingCategoryEnvelope (M n) hs hU (W n) Temp cK depth ≤
        nativeActualConstantSourcePostTaylorCategoryEnvelope (M n) hs hU (W n) Temp cK depth+
          err n*(M n).xs^2

theorem actual_inherited_constant_post_Taylor_envelope_along
    (depth : ℕ) (Bclock Temp Cf A cK cKcut : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hA : 0 < A) (hcK : 0 < cK) (hcKcut : 0 < cKcut)
    {m delta cl cu Az C0 Ct D Tstar Lwin Cs Cwindow c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hCs : 0 ≤ Cs)
    (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (Hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (hsmall : ∀ᶠn in atTop,(M n).xs^2 ≤ Cs*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (Hshell : ∀ᶠn in atTop,∃(Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
      (∀u,(M n).b u=historyMatrixClock Tbase epsilon shell ts u) ∧
      (∀u,(M n).h u=historyFieldClock ts u))
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar Lwin Cwindow (w n))
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) c cKcut A) :
    ∃err : ℕ→ℝ,Tendsto err atTop (𝓝 0) ∧
      ActualConstantSourcePostTaylorEnvelopeAlong depth Temp cK err M W w high outer := by
  have HR d:=actual_inherited_constant_child_higher_Taylor_category_rate_along
    d Bclock Temp Cf A A cKcut hTemp hCf hA.le hA hcKcut
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
    dim hdim M W hcanonical hWlim Hsource hsmall Hshell w hw
  choose e he HE using HR
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  let R:=CK*(1+A)
  let B:=Real.exp (-4*Temp)*cK
  have hB : 0 < B:=mul_pos (Real.exp_pos _) hcK
  have hR : 0 < R:=by dsimp only [R];positivity
  let err n:=((List.range depth).map (fun d=>|e d n|)).sum*(R/B)
  have Hlim (ls : List ℕ) : Tendsto (fun n=>(ls.map (fun d=>|e d n|)).sum) atTop (𝓝 0):=by
    induction ls with
    | nil => simp only [List.map_nil,List.sum_nil]; exact tendsto_const_nhds
    | cons d ds ih => simpa only [List.map_cons,List.sum_cons,abs_zero,zero_add] using (he d).abs.add ih
  have Herr : Tendsto err atTop (𝓝 0):=by
    simpa only [zero_mul] using (Hlim (List.range depth)).mul_const (R/B)
  have HF:=Filter.eventually_all.mpr (fun d : Fin depth=>HE d.val)
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  refine ⟨err,Herr,?_⟩
  filter_upwards [HF,hdim.eventually HK,Hsource,Hcuts,HW] with n hn hclock hsource hcuts hW1
  have hxW : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxW
  intro L us hus hret hmesh hstar hhigh houter
  have Hnet:=Filter.eventually_all.mpr (fun d : Fin depth=>hn d L us hus hret hmesh hstar)
  filter_upwards [Hnet] with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  obtain ⟨hs,HUV,HV,Hlo,Hmass,Houter,_,_,_,_,_,HstarK,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter jGrid
  have hU:=HUV.le.trans HV
  have Hupper : partitionPoint 0 as U ≤ min (A*W n) 1:=
    le_min ((partitionPoint_mono as ho HUV.le).trans Houter) (partitionPoint_mem as ho U).2
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  obtain ⟨hden,hchi,_⟩:=actual_minimum_four_denominator_bounds_of_small_source_clocks
    (M n) hCf hsource (hxW.trans hW1) hW hcKcut ho hs hU HstarK
  have HKstar : K star ≤ R*W n:=by
    have H:=hclock (M n) hsource _ (partitionPoint_mem as ho star)
    change K star ≤ CK*((M n).xs+partitionPoint 0 as star) at H
    apply H.trans
    dsimp only [R]
    nlinarith only [mul_le_mul_of_nonneg_left (add_le_add hxW Hmass) hCK.le]
  have Hd : chi*K star ≤ R*W n:=by
    apply (mul_le_mul_of_nonneg_right hchi
      (native_continuum_mixed_clock_nonneg (dim n) (M n).bf (M n).hf
        (M n).inherited_bf_monotone (M n).inherited_hf_monotone as ho star)).trans
    simpa only [one_mul] using HKstar
  refine ⟨hs,hU,?_⟩
  have Hpaid:=actual_constant_source_pending_envelope_higher_Taylor_paid
    (M n) hs hU (W n) Temp cK depth (fun d=>R/B*|e d n|) (by
      intro d hd
      have H:=hj ⟨d,hd⟩ U hs hU Hlo Hupper Hmass HstarK
      change |nativeActualFourOtherCategorySum (M n) U (W n)
        (nativeActualMinimumFourCenteredForest (M n) hs hU (W n) d
          (nativeActualConstantSourceChildren (M n) as star U hs hU)) .higherTaylor|/
          (chi*K star) ≤ e d n*(M n).xs^2 at H
      have H':=H.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg (M n).xs))
      exact actual_saved_denominator_upper_transfer hden hW hB (abs_nonneg _) Hd H')
  apply Hpaid.trans_eq
  dsimp only [err]
  rw [List.sum_map_mul_left]
  ring

end OAI.SKFluctuations.Cavity
