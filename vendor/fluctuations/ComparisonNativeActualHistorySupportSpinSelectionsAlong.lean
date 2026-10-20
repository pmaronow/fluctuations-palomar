module

public import ComparisonNativeActualLocalScalarLimitData
public import ComparisonNativeActualSelectedBadHistoryInitialMismatchAlong
public import ComparisonScalarCDFSupportZeros
public import ComparisonScalarSupportZeros

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 15000000
set_option backward.isDefEq.respectTransparency false

theorem exists_actual_selected_bad_history_support_spin_selections_along
    {m delta cl cu Az C0 Ct D Bclock T Slocal c0 : ℝ} (hT : 0 < T)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ → ℕ) (hdim : Tendsto dim atTop atTop)
    (root M : (n:ℕ) → NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ → ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (epsilon shell : ℝ)
    (hb : ∀ᶠn in atTop,∀u,(root n).b u=initialShellMatrixClock T epsilon shell u)
    (hh : ∀ᶠn in atTop,∀u,(root n).h u=0)
    (Hhistory : ActualSelectedBadHistoryChain c0 root M)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T)
    (d : ActualInheritedLocalScalarLimitData hT Slocal M htotal)
    (p : ℝ) (hp : ∀delta : ℝ,0 < delta → d.V.mass (p-delta) < d.V.mass (p+delta)) :
    ∃ns : ℕ → ℕ,Tendsto ns atTop atTop ∧ ∃w : ℕ → ParisiFinite.OrderPoint,
      Tendsto (fun j=>(M (ns j)).R (w j)/(M (ns j)).xs) atTop (𝓝 p) ∧
      Tendsto (fun j=>orderedPathS (dim (ns j)+1) (M (ns j)).bf (M (ns j)).hf
        (w j)/(M (ns j)).xs) atTop (𝓝 p) := by
  let R := p+1
  let C := starMassBandConstant cu Az+cu*(|R|+1)+1
  have hCbase := star_mass_band_constant_pos hcu hAz
  have hC : 0 < C := by dsimp only [C]; positivity
  have hCband : starMassBandConstant cu Az ≤ C := by
    dsimp only [C]
    have H : 0 ≤ cu*(|R|+1) := by positivity
    linarith
  have hRC : R < C/cu := by
    apply (lt_div_iff₀ hcu).mpr
    dsimp only [C]
    have H := mul_le_mul_of_nonneg_right (le_abs_self R) hcu.le
    nlinarith
  let v := fun n=>min (C*(M n).xs) 1
  have hv n : v n∈Icc (0:ℝ) 1 :=
    ⟨le_min (mul_nonneg hC.le (M n).hxs.le) zero_le_one,min_le_right _ _⟩
  have hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>(M n).hxs.le) _ hWlim
    intro n
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  have Hsmall : ∀ᶠn in atTop,C*(M n).xs ≤ 1 := by
    have H := hx.const_mul C
    simpa only [mul_zero] using H.eventually (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  have Hcut : ∀ᶠn in atTop,(M n).xs*R < (M n).R (v n) := by
    filter_upwards [Hsmall] with n hn
    dsimp only [v]
    rw [min_eq_left hn]
    have HR := ((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz
      (M n).hxs le_rfl hCband hn
      (show C*(M n).xs∈Icc (C*(M n).xs) (C*(M n).xs) from ⟨le_rfl,le_rfl⟩)).1
    have H := mul_lt_mul_of_pos_right hRC (M n).hxs
    exact (show (M n).xs*R < (C/cu)*(M n).xs by nlinarith only [H]).trans_le HR
  let mu := fun n=>comparisonNormalizedClockMass (M n).xs (v n)
  let radius := fun n (w : ParisiFinite.OrderPoint)=>(M n).R w/(M n).xs
  let spin := fun n (w : ParisiFinite.OrderPoint)=>
    orderedPathS (dim n+1) (M n).bf (M n).hf w/(M n).xs
  have Hmass : ∀eps : ℝ,0 < eps → ∃c : ℝ,0 < c ∧
      ∀ᶠn in atTop,c ≤ (mu n).real {w | |radius n w-p| < eps} :=
    comparison_actual_radius_cdf_support_mass (fun n=>(M n).R) (fun n=>(M n).xs) v d.V.mass
      (fun n=>(comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).monotoneOn _)
      (fun n u _=>comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u)
      (fun n=>(M n).hxs) hv Hcut (fun t _=>d.radius_cdf_limit t)
      (by dsimp only [R]; linarith) (fun delta hd _=>hp delta hd)
  have Hr n : Measurable (radius n) :=
    ((comparisonSweepQuantile_continuous (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).measurable.comp
        measurable_subtype_coe).div_const _
  have Hmi n : Integrable (fun w=>spin n w-radius n w) (mu n) := by
    have Hsm : Measurable (spin n) := by
      have Hmono : Monotone (fun w : ParisiFinite.OrderPoint=>
          orderedPathS (dim n+1) (M n).bf (M n).hf w) :=
        fun u v huv=>(M n).mass_mean_monotone u.property v.property huv
      exact Hmono.measurable.div_const _
    apply Integrable.of_bound ((Hsm.sub (Hr n)).aestronglyMeasurable) (1/(M n).xs)
    filter_upwards [] with w
    have HS := (M n).mass_mean_unit_bounds w.property
    have HR := comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha w
    dsimp only [spin,radius,Pi.sub_apply]
    rw [Real.norm_eq_abs,←sub_div,abs_div,abs_of_pos (M n).hxs]
    apply div_le_div_of_nonneg_right _ (M n).hxs.le
    exact abs_le.mpr ⟨by linarith only [HS.1,HR.2],by linarith only [HS.2,HR.1]⟩
  have Hfull := actual_selected_bad_history_initial_mass_absolute_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim root M (fun n=>(M n).xs)
      (fun _=>le_rfl) hx epsilon shell hb hh Hhistory C hC
  have Hmis : Tendsto (fun n=>∫w,|spin n w-radius n w|∂mu n) atTop (𝓝 0) := by
    apply Hfull.congr'
    filter_upwards [Hsmall] with n hn
    rw [comparison_normalized_clock_error_exact
      (orderedPathS (dim n+1) (M n).bf (M n).hf) (M n).R (M n).hxs,
      comparison_original_retained_integral_eq_interval (hv n)
        (fun u=>|orderedPathS (dim n+1) (M n).bf (M n).hf u-(M n).R u|)]
    simp only [v,min_eq_left hn]
  obtain ⟨ns,hns,w,Hrsel,Hssel,_⟩ := comparison_mass_support_exists_scalar_selections
    mu (fun _=>inferInstance) radius spin (fun _ _=>0) Hr
    (fun _=>by
      apply Integrable.of_bound (by simpa only [abs_zero] using aestronglyMeasurable_const) 0
      filter_upwards [] with w
      simp only [abs_zero,norm_zero,le_refl]) (fun n=>(Hmi n).abs)
    (by simpa only [abs_zero,integral_zero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0)))
    Hmis Hmass
  exact ⟨ns,hns,w,Hrsel,Hssel⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
