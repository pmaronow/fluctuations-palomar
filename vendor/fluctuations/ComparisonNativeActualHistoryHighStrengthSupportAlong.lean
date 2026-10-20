module

public import ComparisonNativeActualHistoryHighStrengthResponseAlong
public import ComparisonNativeActualScalarSupportClosure

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy Cavity NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 16000000

theorem actual_selected_bad_history_high_strength_support_zero_along
    {m delta cl cu Az C0 Ct D Bclock T Ccal c0 : ℝ}
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
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs/
      (M n).xs^2) atTop atTop)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (V g : ℝ→ℝ) {R t : ℝ} (ht : 0 < t) (htR : t < R)
    (hV : ∀a ≤ R,Tendsto (fun n=>(quantileMassProfile (M n).R
      (fun u _=>comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u)).val
          ((M n).xs*a)/(M n).xs) atTop (𝓝 (V a)))
    (hsupport : ∀e : ℝ,0 < e→t+e < R→V (t-e) < V (t+e))
    (hG : ∀Rclock : ℝ,0<Rclock→ TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse (hTemp.trans_le (sub_le_self T hepsilon))
        ((M n).inheritedScalarMassProfile (hTemp.trans_le (sub_le_self T hepsilon)) (htotal n)))
      (T-epsilon) (M n).xs) g atTop (Icc (0:ℝ) Rclock))
    (hg : ∀Rclock : ℝ,0<Rclock→ ContinuousOn g (Icc (0:ℝ) Rclock)) : g t=0 := by
  let C:=starMassBandConstant cu Az+cu*(|R|+1)+1
  have hCbase:=star_mass_band_constant_pos hcu hAz
  have hC : 0 < C:=by dsimp only [C];positivity
  have hCband : starMassBandConstant cu Az ≤ C:=by
    dsimp only [C]
    have H : 0 ≤ cu*(|R|+1):=by positivity
    linarith
  have hRC : R < C/cu:=by
    apply (lt_div_iff₀ hcu).mpr
    dsimp only [C]
    have H:=mul_le_mul_of_nonneg_right (le_abs_self R) hcu.le
    nlinarith
  let v:=fun n=>min (C*(M n).xs) 1
  have hxspos n : 0 < (M n).xs:=(M n).hxs
  have hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0):=by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have hv n : v n∈Icc (0:ℝ) 1:=
    ⟨le_min (mul_nonneg hC.le (hxspos n).le) zero_le_one,min_le_right _ _⟩
  have hvc n : v n ≤ C*(M n).xs:=min_le_left _ _
  have hcut : ∀ᶠn in atTop,(M n).xs*R < (M n).R (v n):=by
    have Hsmall : ∀ᶠn in atTop,C*(M n).xs ≤ 1:=by
      have H:=hxlim.const_mul C
      simpa only [mul_zero] using H.eventually (eventually_le_nhds (show C*(0:ℝ)<1 by simp))
    filter_upwards [Hsmall] with n hn
    dsimp only [v]
    rw [min_eq_left hn]
    have HR:=((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz
      (hxspos n) le_rfl hCband hn (show C*(M n).xs∈Icc (C*(M n).xs) (C*(M n).xs) from
        ⟨le_rfl,le_rfl⟩)).1
    have H:=mul_lt_mul_of_pos_right hRC (hxspos n)
    exact (show (M n).xs*R < (C/cu)*(M n).xs by nlinarith only [H]).trans_le HR
  have Hresponse:=actual_selected_bad_history_high_strength_response_along
    C hC hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hc0 hc01
    hmargin hcapmargin hgapmargin dim hdim root M epsilon shell hepsilon hshell hTemp
    hb hh Hhistory W hcanonical hWlim hcompare hlarge htotal v hv hvc g hG hg
  have Hmass:=comparison_actual_radius_cdf_support_mass (fun n=>(M n).R)
    (fun n=>(M n).xs) v V
    (fun n=>(comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).monotoneOn _)
    (fun n u _=>comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u)
    hxspos hv hcut hV htR hsupport
  exact comparison_scalar_zero_of_positive_mass_on_compact
    (fun n=>comparisonNormalizedClockMass (M n).xs (v n)) (fun _=>inferInstance)
    (fun n (z : ParisiFinite.OrderPoint)=>(M n).R z/(M n).xs)
    (fun n (z : ParisiFinite.OrderPoint)=>
      actualMixedClock (dim n+1) (M n).bf (M n).hf z/((T-epsilon)*(M n).xs))
    _ g ht htR
    (fun n=>((comparisonSweepQuantile_continuous (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).measurable.comp
        measurable_subtype_coe).div_const _)
    (fun n=>(Hresponse.1 n).abs) (fun n=>(Hresponse.2.2.1 n).abs)
    Hresponse.2.1 Hresponse.2.2.2 Hmass (hG R (ht.trans htR))
    ((hg R (ht.trans htR)).continuousAt (Icc_mem_nhds ht htR))

end OAI.SKFluctuations.LaplaceWindowFormalization
