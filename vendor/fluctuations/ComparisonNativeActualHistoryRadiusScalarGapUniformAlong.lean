module

public import ComparisonNativeActualHistoryOriginalScalarGapPointwiseAlong
public import ComparisonNativeActualOriginalThermalNormUpperAlong
public import ComparisonNativeActualRadiusStripGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 20000000

theorem exists_actual_selected_bad_history_radius_scalar_gap_uniform_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (epsilon shell : ℝ) (hepsilon : 0 ≤ epsilon) (hshell : 0 < shell) (hTemp : 0 < T-epsilon)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs) :
    ∃B : ℝ,0 < B ∧ ∀ᶠn in atTop,
      ∃htotal : ∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T,
      ∀r∈(M n).actualRadiusTargetStrip c C,
        |(orderedPathS (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r)-
          scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
            ((M n).inheritedScalarMassProfile
              (hTemp.trans_le (sub_le_self T hepsilon)) htotal)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf ((M n).alpha.val.val r)))/(M n).xs^3| ≤ B := by
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have HW : Tendsto (fun n=>(M n).canonicalDirectTestBandScale) atTop (𝓝 0) := by
    convert hWlim using 1
    exact funext (fun n=>(hcanonical n).symm)
  obtain ⟨Cp,hCp,rate,hrate,Hrate,Hpoint⟩:=
    exists_actual_selected_bad_history_original_scalar_gap_pointwise_along C hC
      hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01 hmargin hcapmargin hgapmargin
      dim hdim root M epsilon shell hepsilon hshell hTemp hb hh Hhistory W hcanonical hWlim hcompare
  obtain ⟨Cd,hCd,HD⟩:=eventually_actual_original_thermal_norm_upper_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M C hC.le
  have Hsite:=actual_scalar_gap_site_ratio_tendsto_zero_along hm hC0 dim hdim M HW
  let B:=Cp*(Cd+1)+1
  have hB : 0 < B:=by dsimp only [B];positivity
  refine ⟨B,hB,?_⟩
  filter_upwards [Hpoint,HD,Hrate.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1)),
    Hsite.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with n hn hDn hrate1 hsite1
  obtain ⟨htotal,hn⟩:=hn
  refine ⟨htotal,?_⟩
  intro r hr
  let u:=(M n).alpha.val.val r
  have hu : 0 < u:=(mul_pos hc (M n).hxs).trans_le hr.2.1
  have hu1 : u ≤ 1:=((M n).alpha.val.property.1 r).2
  have huC : u ≤ C*(M n).xs:=hr.2.2
  have HP:=hn u hu huC
  have HDD:=hDn u ⟨hu,hu1⟩ huC
  have HN : 1/(dim n+1:ℕ) ≤ (M n).xs:=by
    have H:=(div_le_iff₀ (mul_pos (M n).context.hN (M n).hxs)).mp hsite1
    apply (div_le_iff₀ (show (0:ℝ)<(dim n+1:ℕ) from by exact_mod_cast Nat.zero_lt_succ _)).mpr
    simpa only [NativeOverlapContext.N,mul_comm,mul_one] using H
  rw [abs_div,abs_of_pos (pow_pos (M n).hxs 3)]
  apply (div_le_iff₀ (pow_pos (M n).hxs 3)).mpr
  have HM:=mul_le_mul_of_nonneg_left (add_le_add HDD HN) (mul_nonneg hCp (sq_nonneg (M n).xs))
  have HE:=mul_le_mul_of_nonneg_right hrate1 (pow_pos (M n).hxs 3).le
  apply HP.trans
  dsimp only [B]
  nlinarith only [HM,HE]

end OAI.SKFluctuations.LaplaceWindowFormalization
