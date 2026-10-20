module

public import ComparisonScalarPrimitives
public import ComparisonNativeActualOriginalMassMismatch
public import ComparisonNativeActualScalarCalibration
public import ComparisonScalarMassClosureOn
public import ComparisonScalarBoundedStrengthMass

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
set_option maxHeartbeats 8000000

theorem comparison_scalar_zero_of_positive_mass_on_compact
    {Ω : Type*} [MeasurableSpace Ω]
    (mu : ℕ→Measure Ω) (hfinite : ∀n,IsFiniteMeasure (mu n))
    (radius clock : ℕ→Ω→ℝ) (G : ℕ→ℝ→ℝ) (g : ℝ→ℝ) {t R : ℝ}
    (ht : 0 < t) (htR : t < R)
    (hr : ∀n,Measurable (radius n))
    (hGint : ∀n,Integrable (fun w=>|G n (clock n w)|) (mu n))
    (hKint : ∀n,Integrable (fun w=>|clock n w-radius n w|) (mu n))
    (hGzero : Tendsto (fun n=>∫w,|G n (clock n w)|∂mu n) atTop (𝓝 0))
    (hKzero : Tendsto (fun n=>∫w,|clock n w-radius n w|∂mu n) atTop (𝓝 0))
    (hmass : ∀eps : ℝ,0 < eps→∃c : ℝ,0 < c ∧
      ∀ᶠn in atTop,c ≤ (mu n).real {w | |radius n w-t| < eps})
    (hG : TendstoUniformlyOn G g atTop (Icc (0:ℝ) R)) (hg : ContinuousAt g t) : g t=0 := by
  obtain ⟨ns,hns,w,_,hclock,hzero⟩:=comparison_mass_support_exists_scalar_selections
    mu hfinite radius clock G hr hGint hKint hGzero hKzero hmass
  have hmem : ∀ᶠj in atTop,clock (ns j) (w j)∈Icc (0:ℝ) R := by
    filter_upwards [hclock.eventually (eventually_gt_nhds ht),
      hclock.eventually (eventually_lt_nhds htR)] with j hj0 hjR
    exact ⟨hj0.le,hjR.le⟩
  have H:=(hG.seq_tendstoUniformlyOn ns hns).tendsto_comp hg.continuousWithinAt
    (tendsto_nhdsWithin_iff.mpr ⟨hclock,hmem⟩)
  exact tendsto_nhds_unique H hzero

theorem comparison_rescaled_covariance_response_eq_actual {T : ℝ}
    (hT : 0 < T) (alpha : boundedMassProfiles) (x : ℝ) :
    comparisonRescaledScalarResponse (scalarCovarianceResponse hT alpha) T x=
      comparisonActualScalarResponse hT alpha x := by
  funext t
  have he : T*x*t/T=x*t := by field_simp
  simp only [comparisonRescaledScalarResponse,scalarCovarianceResponse,
    comparisonActualScalarResponse,he]

namespace NativeOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem bare_mixed_clock_eq_nativeScalarClock {n : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hb : ∀u,M.b u=T) (hh : ∀u,M.h u=0) (u : ℝ) :
    actualMixedClock (n+1) M.bf M.hf u=
      comparisonNativeScalarClock 0 T (laplaceComparisonStrength M.context.d M.lam (M.R u))
        (M.R u) (orderedPathS (n+1) M.bf M.hf u) := by
  have hr:=comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.alpha u
  have hg0:=(laplaceComparisonStrength_pos M.context.d M.hlam (M.R u)).le
  have hgT:=(laplaceComparisonStrength_le M.context.d M.hlam.le (M.R u)).trans
    (M.hlb.trans_eq (hb 0))
  unfold actualMixedClock
  change ((M.h u+laplaceComparisonStrength M.context.d M.lam (M.R u)*M.R u).toNNReal:ℝ)+
    ((M.b u-laplaceComparisonStrength M.context.d M.lam (M.R u)).toNNReal:ℝ)*
      orderedPathS (n+1) M.bf M.hf u=_
  rw [hh u,hb u,zero_add,Real.coe_toNNReal _ (mul_nonneg hg0 hr.1),
    Real.coe_toNNReal _ (sub_nonneg.mpr hgT)]
  simp only [comparisonNativeScalarClock,zero_add]

theorem actual_radius_compact_retained_cut
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    {C R : ℝ} (hC : starMassBandConstant cu Az ≤ C) (hR : R < C/cu) :
    (∀n,min (C*W n) 1∈Icc (0:ℝ) 1) ∧
    (∀n,min (C*W n) 1 ≤ C*W n) ∧
    ∀ᶠn in atTop,W n*R < (M n).R (min (C*W n) 1) := by
  have hCp : 0 < C := (star_mass_band_constant_pos hcu hAz).trans_le hC
  have hW n : 0 < W n := (M n).hxs.trans_le (hxs n)
  refine ⟨fun n=>⟨le_min (mul_nonneg hCp.le (hW n).le) zero_le_one,min_le_right _ _⟩,
    fun n=>min_le_left _ _,?_⟩
  have HW:=(hWlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  filter_upwards [HW] with n hn
  rw [min_eq_left hn]
  have HR:=((M n).actual_closed_regular_mass_band_radius_bounds hcl hcu hAz
    (hW n) (hxs n) hC hn (show C*W n∈Icc (C*W n) (C*W n) from ⟨le_rfl,le_rfl⟩)).1
  have H:=mul_lt_mul_of_pos_right hR (hW n)
  exact (show W n*R < (C/cu)*W n by nlinarith only [H]).trans_le HR

theorem actual_bare_bounded_strength_scalar_support_zero
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W v : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hT : 0 < T) (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0)
    (V g : ℝ→ℝ) {C K R t : ℝ} (hC : 0 < C) (hK : 0 ≤ K)
    (hv : ∀n,v n∈Icc (0:ℝ) 1) (hvc : ∀n,v n ≤ C*W n)
    (hwork : ∀n,laplaceComparisonStrength (M n).context.d (M n).lam (W n)/(W n)^2 ≤ K)
    (hcut : ∀ᶠn in atTop,W n*R < (M n).R (v n))
    (hV : ∀a ≤ R,Tendsto (fun n=>(quantileMassProfile (M n).R
      (fun u _=>comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
        (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u)).val
          (W n*a)/W n) atTop (𝓝 (V a)))
    (ht : 0 < t) (htR : t < R)
    (hsupport : ∀e : ℝ,0 < e→t+e < R→V (t-e) < V (t+e))
    (hcav : ∀n,Integrable (fun w : ParisiFinite.OrderPoint=>
      (M n).bareScalarCavityResidual hT (hb n) (hh n) w/(W n)^3)
        (comparisonNormalizedClockMass (W n) (v n)))
    (hcav0 : Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |(M n).bareScalarCavityResidual hT (hb n) (hh n) w/(W n)^3|
        ∂comparisonNormalizedClockMass (W n) (v n)) atTop (𝓝 0))
    (hG : TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hT ((M n).bareScalarMassProfile hT (hb n) (hh n))) T (W n))
        g atTop (Icc (0:ℝ) R)) (hg : ContinuousAt g t) : g t=0 := by
  let μ:=fun n=>(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n}
  let ν:=fun n=>comparisonNormalizedClockMass (W n) (v n)
  let rad:=fun n (w : ParisiFinite.OrderPoint)=>(M n).R w
  let S:=fun n (w : ParisiFinite.OrderPoint)=>orderedPathS (n+1) (M n).bf (M n).hf w
  let e:=fun n w=>laplaceComparisonStrength (M n).context.d (M n).lam (rad n w)
  let Γ:=fun n=>scalarCovarianceResponse hT ((M n).bareScalarMassProfile hT (hb n) (hh n))
  let h0:=fun (_n : ℕ) (_w : ParisiFinite.OrderPoint)=>(0:ℝ)
  let b0:=fun (_n : ℕ) (_w : ParisiFinite.OrderPoint)=>T
  have hW n:0 < W n := (M n).hxs.trans_le (hxs n)
  have hrm n:Measurable (rad n) :=
    ((comparisonSweepQuantile_continuous (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).measurable.comp
        measurable_subtype_coe)
  have hmass n:(μ n).real univ ≤ C*W n := by
    rw [comparison_original_retained_mass_exact (hv n)]
    exact hvc n
  have hzero:=actual_original_retained_squared_mismatch_ratio_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt M W v hxs hWlim hb hh C hC hv hvc
  have herr:=comparison_original_mass_bounded_strength_errors μ (fun _=>inferInstance)
    rad (fun n w=>S n w-rad n w) (fun n=>(M n).context.d) (fun n=>(M n).lam) W
    hrm (fun n=>((M n).original_retained_mismatch_integrable (v n)).1)
    (fun n=>((M n).original_retained_mismatch_integrable (v n)).2)
    (fun n=>(M n).context.hd) (fun n=>(M n).hlam.le) hW (fun n=>(M n).hld)
    hC.le hK hmass hwork hzero
  have hclock n (w : ParisiFinite.OrderPoint) :
      comparisonScalarMassClockOn h0 b0 e S rad n w=actualMixedClock (n+1) (M n).bf (M n).hf w :=
    ((M n).bare_mixed_clock_eq_nativeScalarClock (hb n) (hh n) w).symm
  have hcav' n:Integrable (fun w=>(S n w-Γ n
      (comparisonScalarMassClockOn h0 b0 e S rad n w))/(W n)^3) (ν n) := by
    simp_rw [hclock]
    exact hcav n
  have hcav0' : Tendsto (fun n=>∫w,|(S n w-Γ n
      (comparisonScalarMassClockOn h0 b0 e S rad n w))/(W n)^3|∂ν n) atTop (𝓝 0) := by
    simp_rw [hclock]
    exact hcav0
  have hbare n:Integrable (fun w=>((b0 n w-T)*S n w+h0 n w)/(W n)^3) (ν n) := by
    simp only [b0,h0,sub_self,zero_mul,add_zero,zero_div]
    exact integrable_zero _ _ _
  have hbare0 : Tendsto (fun n=>∫w,|((b0 n w-T)*S n w+h0 n w)/(W n)^3|∂ν n)
      atTop (𝓝 0) := by
    simp only [b0,h0,sub_self,zero_mul,add_zero,zero_div,abs_zero,integral_zero]
    exact tendsto_const_nhds
  have hresponse:=comparison_scalar_mass_response_L1_tendsto_on ν Γ h0 b0 e S rad W hT
    (fun n=>(hW n).ne') herr.2.2.1 hcav' hbare herr.2.2.2 hcav0' hbare0
  have hspin n:Integrable (fun w=>S n w/W n-rad n w/W n) (ν n) := by
    simpa only [sub_div,ν,μ,comparisonNormalizedClockMass,Function.comp_def] using herr.1 n
  have hspin0 : Tendsto (fun n=>∫w,|S n w/W n-rad n w/W n|∂ν n) atTop (𝓝 0) := by
    simpa only [sub_div,ν,μ,comparisonNormalizedClockMass,Function.comp_def] using herr.2.1
  have hclock0:=comparison_scalar_mass_clock_L1_tendsto_on ν h0 b0 e S rad W hT
    (fun n=>(hW n).ne') hWlim hspin herr.2.2.1 hbare hspin0 herr.2.2.2 hbare0
  have hpositive:=comparison_actual_radius_cdf_support_mass (fun n=>(M n).R) W v V
    (fun n=>(comparisonSweepQuantile_monotone (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha).monotoneOn _)
    (fun n u _=>comparisonSweepQuantile_bounds (M n).context.hc (M n).context.hk
      (M n).context.hkc (M n).context.hm (M n).context.hM (M n).alpha u)
    hW hv hcut hV htR hsupport
  exact comparison_scalar_zero_of_positive_mass_on_compact ν (fun _=>inferInstance)
    (fun n w=>rad n w/W n)
    (fun n w=>comparisonScalarMassClockOn h0 b0 e S rad n w/(T*W n))
    (fun n=>comparisonRescaledScalarResponse (Γ n) T (W n)) g ht htR
    (fun n=>(hrm n).div_const _) (fun n=>(hresponse.1 n).abs)
    (fun n=>(hclock0.1 n).abs) hresponse.2 hclock0.2 hpositive hG hg

theorem actual_bare_bounded_strength_scalar_support_zero_subsequence
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (M : (n : ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W v : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hT : 0 < T) (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0)
    (phi : ℕ→ℕ) (hphi : Tendsto phi atTop atTop)
    (V g : ℝ→ℝ) {C K R t : ℝ} (hC : 0 < C) (hK : 0 ≤ K)
    (hv : ∀n,v n∈Icc (0:ℝ) 1) (hvc : ∀n,v n ≤ C*W n)
    (hwork : ∀n,laplaceComparisonStrength (M (phi n)).context.d (M (phi n)).lam (W (phi n))/(W (phi n))^2 ≤ K)
    (hcut : ∀ᶠn in atTop,W (phi n)*R < (M (phi n)).R (v (phi n)))
    (hV : ∀a ≤ R,Tendsto (fun n=>(quantileMassProfile (M (phi n)).R
      (fun u _=>comparisonSweepQuantile_bounds (M (phi n)).context.hc (M (phi n)).context.hk
        (M (phi n)).context.hkc (M (phi n)).context.hm (M (phi n)).context.hM (M (phi n)).alpha u)).val
          (W (phi n)*a)/W (phi n)) atTop (𝓝 (V a)))
    (ht : 0 < t) (htR : t < R)
    (hsupport : ∀e : ℝ,0 < e→t+e < R→V (t-e) < V (t+e))
    (hcav : ∀n,Integrable (fun w : ParisiFinite.OrderPoint=>
      (M (phi n)).bareScalarCavityResidual hT (hb (phi n)) (hh (phi n)) w/(W (phi n))^3)
        (comparisonNormalizedClockMass (W (phi n)) (v (phi n))))
    (hcav0 : Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |(M (phi n)).bareScalarCavityResidual hT (hb (phi n)) (hh (phi n)) w/(W (phi n))^3|
        ∂comparisonNormalizedClockMass (W (phi n)) (v (phi n))) atTop (𝓝 0))
    (hG : TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hT ((M (phi n)).bareScalarMassProfile hT (hb (phi n)) (hh (phi n)))) T (W (phi n)))
        g atTop (Icc (0:ℝ) R)) (hg : ContinuousAt g t) : g t=0 := by
  let μ:=fun n=>(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v (phi n)}
  let ν:=fun n=>comparisonNormalizedClockMass (W (phi n)) (v (phi n))
  let rad:=fun n (w : ParisiFinite.OrderPoint)=>(M (phi n)).R w
  let S:=fun n (w : ParisiFinite.OrderPoint)=>orderedPathS (phi n+1) (M (phi n)).bf (M (phi n)).hf w
  let e:=fun n w=>laplaceComparisonStrength (M (phi n)).context.d (M (phi n)).lam (rad n w)
  let Γ:=fun n=>scalarCovarianceResponse hT ((M (phi n)).bareScalarMassProfile hT (hb (phi n)) (hh (phi n)))
  let h0:=fun (_n : ℕ) (_w : ParisiFinite.OrderPoint)=>(0:ℝ)
  let b0:=fun (_n : ℕ) (_w : ParisiFinite.OrderPoint)=>T
  have hW n:0 < W (phi n) := (M (phi n)).hxs.trans_le (hxs (phi n))
  have hrm n:Measurable (rad n) :=
    ((comparisonSweepQuantile_continuous (M (phi n)).context.hc (M (phi n)).context.hk
      (M (phi n)).context.hkc (M (phi n)).context.hm (M (phi n)).context.hM (M (phi n)).alpha).measurable.comp
        measurable_subtype_coe)
  have hmass n:(μ n).real univ ≤ C*W (phi n) := by
    rw [comparison_original_retained_mass_exact (hv (phi n))]
    exact hvc (phi n)
  have hzero:=actual_original_retained_squared_mismatch_ratio_tendsto_zero
    hm hdelta hroom hcl hcu hAz hC0 hCt M W v hxs hWlim hb hh C hC hv hvc
  have hzeroSub:=hzero.comp hphi
  have herr:=comparison_original_mass_bounded_strength_errors μ (fun _=>inferInstance)
    rad (fun n w=>S n w-rad n w) (fun n=>(M (phi n)).context.d) (fun n=>(M (phi n)).lam) (W ∘ phi)
    hrm (fun n=>((M (phi n)).original_retained_mismatch_integrable (v (phi n))).1)
    (fun n=>((M (phi n)).original_retained_mismatch_integrable (v (phi n))).2)
    (fun n=>(M (phi n)).context.hd) (fun n=>(M (phi n)).hlam.le) hW (fun n=>(M (phi n)).hld)
    hC.le hK hmass hwork hzeroSub
  have hclock n (w : ParisiFinite.OrderPoint) :
      comparisonScalarMassClockOn h0 b0 e S rad n w=actualMixedClock (phi n+1) (M (phi n)).bf (M (phi n)).hf w :=
    ((M (phi n)).bare_mixed_clock_eq_nativeScalarClock (hb (phi n)) (hh (phi n)) w).symm
  have hcav' n:Integrable (fun w=>(S n w-Γ n
      (comparisonScalarMassClockOn h0 b0 e S rad n w))/(W (phi n))^3) (ν n) := by
    simp_rw [hclock]
    exact hcav n
  have hcav0' : Tendsto (fun n=>∫w,|(S n w-Γ n
      (comparisonScalarMassClockOn h0 b0 e S rad n w))/(W (phi n))^3|∂ν n) atTop (𝓝 0) := by
    simp_rw [hclock]
    exact hcav0
  have hbare n:Integrable (fun w=>((b0 n w-T)*S n w+h0 n w)/(W (phi n))^3) (ν n) := by
    simp only [b0,h0,sub_self,zero_mul,add_zero,zero_div]
    exact integrable_zero _ _ _
  have hbare0 : Tendsto (fun n=>∫w,|((b0 n w-T)*S n w+h0 n w)/(W (phi n))^3|∂ν n)
      atTop (𝓝 0) := by
    simp only [b0,h0,sub_self,zero_mul,add_zero,zero_div,abs_zero,integral_zero]
    exact tendsto_const_nhds
  have hresponse:=comparison_scalar_mass_response_L1_tendsto_on ν Γ h0 b0 e S rad (W ∘ phi) hT
    (fun n=>(hW n).ne') herr.2.2.1 hcav' hbare herr.2.2.2 hcav0' hbare0
  have hspin n:Integrable (fun w=>S n w/W (phi n)-rad n w/W (phi n)) (ν n) := by
    simpa only [sub_div,ν,μ,comparisonNormalizedClockMass,Function.comp_def] using herr.1 n
  have hspin0 : Tendsto (fun n=>∫w,|S n w/W (phi n)-rad n w/W (phi n)|∂ν n) atTop (𝓝 0) := by
    simpa only [sub_div,ν,μ,comparisonNormalizedClockMass,Function.comp_def] using herr.2.1
  have hclock0:=comparison_scalar_mass_clock_L1_tendsto_on ν h0 b0 e S rad (W ∘ phi) hT
    (fun n=>(hW n).ne') (hWlim.comp hphi) hspin herr.2.2.1 hbare hspin0 herr.2.2.2 hbare0
  have hpositive:=comparison_actual_radius_cdf_support_mass (fun n=>(M (phi n)).R) (W ∘ phi) (v ∘ phi) V
    (fun n=>(comparisonSweepQuantile_monotone (M (phi n)).context.hc (M (phi n)).context.hk
      (M (phi n)).context.hkc (M (phi n)).context.hm (M (phi n)).context.hM (M (phi n)).alpha).monotoneOn _)
    (fun n u _=>comparisonSweepQuantile_bounds (M (phi n)).context.hc (M (phi n)).context.hk
      (M (phi n)).context.hkc (M (phi n)).context.hm (M (phi n)).context.hM (M (phi n)).alpha u)
    hW (fun n=>hv (phi n)) hcut hV htR hsupport
  exact comparison_scalar_zero_of_positive_mass_on_compact ν (fun _=>inferInstance)
    (fun n w=>rad n w/W (phi n))
    (fun n w=>comparisonScalarMassClockOn h0 b0 e S rad n w/(T*W (phi n)))
    (fun n=>comparisonRescaledScalarResponse (Γ n) T (W (phi n))) g ht htR
    (fun n=>(hrm n).div_const _) (fun n=>(hresponse.1 n).abs)
    (fun n=>(hclock0.1 n).abs) hresponse.2 hclock0.2 hpositive hG hg

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
