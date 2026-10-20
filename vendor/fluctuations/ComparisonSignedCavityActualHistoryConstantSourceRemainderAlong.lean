module

public import ComparisonSignedCavityActualConstantSourceRemainderParts
public import ComparisonSignedCavityActualConstantSourceClosedRatesAlong
public import ComparisonSignedCavityActualMinimumOmittedSiteProduct

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 26000000

theorem actual_selected_bad_history_constant_source_remainder_on_given_cuts_along
    {m delta cl cu Az C0 Ct D Bclock Temp Ccal c0 cFirst cK A : ℝ}
    (hA : 0 ≤ A) (hc : 0 < cFirst) (hcouter : 2*cu*(Az+1) ≤ cFirst)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hTemp : 0 ≤ Temp)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock Temp epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W radius : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ∃C : ℝ,0 < C ∧∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
      (w n).star∈us → high n∈us → outer n∈us → ∀ᶠj in atTop,
        let as:=finiteCutMasses us j
        let star:=retainedMassPrefixIndex (w n).star.val as
        let U:=retainedMassPrefixIndex (high n).val as
        |nativeActualConstantSourceRemainder (M n) as star U| ≤ C*W n*(M n).xs^2+
          |nativeActualConstantSourceTaylorPart (M n) as star U| := by
  obtain ⟨Cf,hCf,Hsource⟩:=actual_selected_bad_history_small_source_clocks
    hm hdelta hcl hAz hC0 hc0 hmargin hcapmargin dim hdim root M
    epsilon shell hepsilon hTemp hb hh Hhistory
  obtain ⟨ps,Hps⟩:=Hhistory.literal_readout epsilon shell hb hh
  have Htotal:=actual_selected_bad_history_total_clock_and_root dim root M epsilon shell hepsilon hb hh Hhistory
  obtain ⟨CL,hCL,HR⟩:=eventually_actual_shell_history_retained_constant_longitudinal_rate_along
    dim hdim 2 Bclock Temp Cf A hTemp hCf hA
    (D:=D) (Cs:=Ccal^2) hm hdelta hroom hcl hcu hAz hC0 hCt (sq_nonneg _) hc hcouter
  obtain ⟨CK,hCK,HK⟩:=eventually_actual_inherited_continuum_clock_mass_upper
    (D:=D) Bclock Temp Cf hTemp hCf hm hdelta hroom hcl hcu hAz hC0 hCt
  have Homit:=hdim.eventually (eventually_actual_omitted_product_cubic_cost_saved
    (delta:=delta) (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock)
    hm hC0 (2*Temp) (by positivity))
  have HW:=hWlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1))
  let C:=2*CK*(1+A)*(1+CL)+1
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HR,hdim.eventually HK,Hsource,Hps,Htotal,Hcuts,hcompare,HW,Homit]
    with n hnL hnK hs hp ht hcuts hcomp hw hnOmit
  intro L us hus hret hmesh hstar hhigh houter
  have hxs : (M n).xs ≤ W n:=by rw [hcanonical];exact (M n).canonical_direct_test_band_ge_scale
  have hW : 0 < W n:=(M n).hxs.trans_le hxs
  have hxs1 : (M n).xs ≤ 1:=hxs.trans hw
  have H:=hnL (M n) Temp epsilon shell ((ps.map (fun P=>P n)).map (fun P=>P.toHistoryTerm))
    hs hp.2.1 hp.2.2 ht.1 ht.2 hcomp (by simpa only [hcanonical n] using hw) L us hus hret hmesh
  have HM:=eventually_native_finite_physical_mean_uniform_center (dim n) (M n).bf (M n).hf
    (M n).inherited_bf_monotone (M n).inherited_hf_monotone ((M n).inherited_zero_root_field ht.2)
    us hus (1/(dim n+1:ℕ)) (by positivity)
  filter_upwards [H,HM] with j hj hjM
  dsimp only at hj hjM ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let U:=retainedMassPrefixIndex (high n).val as
  let g:=nativeFreshAtSlot (ClockTree.single (S:=Spin (dim n)×Bool) as) 0 (singleSlot as) star
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus j
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,Houter,_,_,_,_,_,_,_⟩:=
    hcuts.finite_net_readout us hus hstar hhigh houter j
  have hU:=HUV.le.trans HV
  have Hhigh:=(partitionPoint_mono as ho HUV.le).trans Houter
  have Hleaves : g.tree.leaves ≤ 2:=by
    have Hleaf:=(ClockTree.single (S:=Spin (dim n)×Bool) as).markedAttach_leaves 0 g
      (nativeFreshAtSlot_mem _ 0 (singleSlot as) star)
    simpa only [single_leaves_exact] using Hleaf
  have HL:=hj U g.tree hU Hleaves (by simpa only [hcanonical n] using Hfirst)
    (by simpa only [hcanonical n] using Hhigh)
    (native_constant_calibration_fresh_tree_HIGH_fork_free as star U Hs)
  have Hclock : nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star ≤ CK*(1+A)*W n:=by
    rw [native_continuum_mixed_clock_retained_eq (dim n) (M n).bf (M n).hf as ho
      (w n).star (finiteCutMasses_nodes us j hstar)]
    have Hc:=hnK (M n) hs (w n).star.val
      ⟨(w n).star.property.le,hcuts.star_lt.le.trans (hcuts.high_lt.le.trans hcuts.outer_le_one)⟩
    have Hmass':(w n).star.val ≤ A*W n:=
      hcuts.star_lt.le.trans (hcuts.high_lt.le.trans hcuts.outer_scale)
    nlinarith only [Hc,hCK,hxs,Hmass']
  have Hret:=actual_constant_source_retained_part_abs_le (M n)
    (E:=((M n).context.N^(-(1:ℝ)/3)+CL*(M n).context.N^(-(actualMassSavingExponent m delta/256)))*(M n).xs^2)
    ht.1 as ho star U Hs hU Hclock HL
  have Hmean:=actual_constant_source_mean_part_abs_le (M n) ht.1 as ho star U Hs hU
    (hjM star (Hs.le.trans hU))
  have hN : 1 ≤ (M n).context.N:=by change (1:ℝ) ≤ (dim n+1:ℕ);exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  have H1:=Real.rpow_le_one_of_one_le_of_nonpos hN (show -(1:ℝ)/3 ≤ 0 by norm_num)
  have H2:=Real.rpow_le_one_of_one_le_of_nonpos hN
    (show -(actualMassSavingExponent m delta/256) ≤ 0 by linarith [actualMassSavingExponent_pos hm hdelta])
  have Hret' : |nativeActualConstantSourceRetainedPart (M n) as star U| ≤
      2*CK*(1+A)*(1+CL)*W n*(M n).xs^2:=by
    apply Hret.trans
    have HE : (M n).context.N^(-(1:ℝ)/3)+CL*(M n).context.N^(-(actualMassSavingExponent m delta/256)) ≤ 1+CL:=by
      nlinarith
    have HH:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right HE (sq_nonneg (M n).xs))
      (show 0 ≤ 2*(CK*(1+A)*W n) by positivity)
    convert HH using 1
    ring
  have HO:=hnOmit (M n) (W n) hxs
  have H6:=Real.rpow_le_one_of_one_le_of_nonpos hN (show -(1:ℝ)/6 ≤ 0 by norm_num)
  have HO' : 2*Temp/(dim n+1:ℕ) ≤ W n*(M n).xs^2:=by
    have Hden : (dim n+1:ℕ)*(M n).xs ≤ (dim n+1:ℕ)*(1:ℝ):=
      mul_le_mul_of_nonneg_left hxs1 (by positivity)
    have Hdiv:=div_le_div_of_nonneg_left (show 0 ≤ 2*Temp by positivity)
      (show 0 < (dim n+1:ℕ)*(M n).xs by have :=(M n).hxs;positivity) Hden
    simp only [mul_one] at Hdiv
    apply Hdiv.trans (HO.trans _)
    change (M n).context.N^(-(1:ℝ)/6)*(W n*(M n).xs^2) ≤ _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right H6 (by positivity : 0 ≤ W n*(M n).xs^2)
  rw [nativeActualConstantSourceRemainder_eq_parts]
  have Habs:=(abs_add_le
    (nativeActualConstantSourceRetainedPart (M n) as star U+nativeActualConstantSourceMeanPart (M n) as star U)
    (nativeActualConstantSourceTaylorPart (M n) as star U)).trans
      (add_le_add (abs_add_le _ _) le_rfl)
  dsimp only [C]
  nlinarith only [Habs,Hret',Hmean,HO']

end OAI.SKFluctuations.LaplaceWindowFormalization
