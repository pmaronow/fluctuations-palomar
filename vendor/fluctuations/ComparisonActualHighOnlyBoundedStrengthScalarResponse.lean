module

public import ComparisonActualHighOnlyRegularInitialMassMismatchAlong
public import ComparisonActualHighOnlyLargerWorkingScale
public import ComparisonActualHighOnlyPositiveBareError
public import ComparisonActualHighOnlyScalarLimitData
public import ComparisonScalarEventuallyBoundedStrengthMass
public import ComparisonNativeActualInheritedCalibration

@[expose] public section
set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighOnlyOverlapMinimum
open Hierarchy
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem coefficient_le_strength_high_only {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (u : ℝ) :
    M.coefficient u ≤ laplaceComparisonStrength M.context.d M.lam (M.R u) := by
  change omittedStrengthCoefficient M.context.d M.data.s M.R M.lam u ≤ _
  unfold omittedStrengthCoefficient
  split_ifs
  · exact le_rfl
  · exact (laplaceComparisonStrength_pos M.context.d M.hlam _).le

theorem inherited_clock_cubic_error_of_eq4_high_only {n : ℕ}
    (M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u x Cb Ch Ce Cr Cs : ℝ} (hu : u∈Icc (0:ℝ) 1)
    (hx : 0 ≤ x) (hCb : 0 ≤ Cb) (hCe : 0 ≤ Ce)
    (hb : |M.b u-T| ≤ Cb*x^2) (hh : |M.h u| ≤ Ch*x^3)
    (he : laplaceComparisonStrength M.context.d M.lam (M.R u) ≤ Ce*x^2)
    (hr : |M.R u-orderedPathS (n+1) M.bf M.hf u| ≤ Cr*x)
    (hs : orderedPathS (n+1) M.bf M.hf u ≤ Cs*x) :
    |actualMixedClock (n+1) M.bf M.hf u-T*orderedPathS (n+1) M.bf M.hf u| ≤
      (Ch+Cb*Cs+Ce*Cr)*x^3 := by
  rw [M.inherited_mixed_clock_eq_nativeScalarClock hu]
  exact native_scalar_clock_cubic_error_of_eq4 hx hCb hCe hb hh
    (by rw [abs_of_nonneg (M.coefficient_nonneg u)];exact (M.coefficient_le_strength_high_only u).trans he)
    hr (by rwa [abs_of_nonneg (M.mass_mean_nonneg hu)])

end OAI.SKFluctuations.LaplaceWindowFormalization.ActualHighOnlyOverlapMinimum

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 8000000
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock T : ℝ}

theorem actual_inherited_local_temperature_restricted_response_tendsto_zero_along_high_only
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighOnlyOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : HighOnlyActualComparableBandContext M T)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs ≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hclock : ∀ᶠn in atTop,NativePullbackClockRegularity (M n).alpha.val.val (M n).b (M n).h 0 1)
    (hT : 0 < T) {Tamb : ℝ} (hTamb : 0 < Tamb)
    (htotal : ∀n u,u∈Icc (0:ℝ) 1 → (M n).h u+(M n).b u ≤ Tamb)
    (F : ℕ→Set ParisiFinite.OrderPoint) (hF : ∀n,MeasurableSet (F n))
    (C K : ℝ) (hC : 0 < C) (hK : 0 ≤ K)
    (hcut : ∀n w,w∈F n → (w:ℝ) ≤ C*W n)
    (hwork : ∀ᶠn in atTop,laplaceComparisonStrength (M n).context.d (M n).lam (W n)/(W n)^2 ≤ K)
    (hEq4 : ∀epsilon > 0,∀ᶠn in atTop,∀w∈F n,
      |(M n).b w-T| ≤ epsilon*(W n)^2 ∧ |(M n).h w| ≤ epsilon*(W n)^3)
    (hcav : ∀n,Integrable (fun w : ParisiFinite.OrderPoint=>
      (M n).inheritedScalarCavityResidual hTamb (htotal n) w/(W n)^3)
        (ENNReal.ofReal (1/W n) • (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (F n)))
    (hcav0 : Tendsto (fun n=>∫w : ParisiFinite.OrderPoint,
      |(M n).inheritedScalarCavityResidual hTamb (htotal n) w/(W n)^3|
        ∂(ENNReal.ofReal (1/W n) • (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (F n)))
        atTop (𝓝 0)) :
    let nu:=fun n=>ENNReal.ofReal (1/W n) •
      (uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (F n)
    let G:=fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hTamb ((M n).inheritedScalarMassProfile hTamb (htotal n))) T (W n)
    let q:=fun n (w : ParisiFinite.OrderPoint)=>actualMixedClock (dim n+1) (M n).bf (M n).hf w/(T*W n)
    (∀n,Integrable (fun w=>G n (q n w)) (nu n)) ∧
      Tendsto (fun n=>∫w,|G n (q n w)|∂nu n) atTop (𝓝 0) ∧
    (∀n,Integrable (fun w=>q n w-(M n).R w/W n) (nu n)) ∧
      Tendsto (fun n=>∫w,|q n w-(M n).R w/W n|∂nu n) atTop (𝓝 0) := by
  dsimp only
  let mu:=fun n=>(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (F n)
  let nu:=fun n=>ENNReal.ofReal (1/W n) • mu n
  have (n : ℕ) : IsFiniteMeasure (nu n) := by
    constructor
    simp only [nu,Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  let v:=fun n=>min (C*W n) 1
  let mu0:=fun n=>(uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict {w | (w:ℝ) ≤ v n}
  let rad:=fun n (w : ParisiFinite.OrderPoint)=>(M n).R w
  let S:=fun n (w : ParisiFinite.OrderPoint)=>orderedPathS (dim n+1) (M n).bf (M n).hf w
  let e:=fun n (w : ParisiFinite.OrderPoint)=>(M n).coefficient w
  let Gamma:=fun n=>scalarCovarianceResponse hTamb ((M n).inheritedScalarMassProfile hTamb (htotal n))
  let h0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).h w
  let b0:=fun n (w : ParisiFinite.OrderPoint)=>(M n).b w
  have hW n : 0 < W n := (M n).hxs.trans_le (hxs n)
  have hv n : v n∈Icc (0:ℝ) 1 := ⟨le_min (mul_nonneg hC.le (hW n).le) zero_le_one,min_le_right _ _⟩
  have hvc n : v n ≤ C*W n := min_le_left _ _
  have hsub n : F n ⊆ {w : ParisiFinite.OrderPoint | (w:ℝ) ≤ v n} :=
    fun w hw=>le_min (hcut n w hw) w.property.2
  have hmu n : mu n ≤ mu0 n := Measure.restrict_mono (hsub n) le_rfl
  have hi n : Integrable (fun w=>S n w-rad n w) (mu n) :=
    (((M n).original_retained_mismatch_integrable (v n)).1).mono_measure (hmu n)
  have hi2 n : Integrable (fun w=>(S n w-rad n w)^2) (mu n) :=
    (((M n).original_retained_mismatch_integrable (v n)).2).mono_measure (hmu n)
  have hmass n : (mu n).real univ ≤ C*W n := by
    change ((uniformOrderMass : Measure ParisiFinite.OrderPoint).restrict (F n)).real univ ≤ _
    rw [measureReal_restrict_apply' (hF n),univ_inter]
    exact (measureReal_mono (μ:=(uniformOrderMass : Measure ParisiFinite.OrderPoint)) (hsub n)).trans
      ((uniformOrderMass_atMost (hv n)).le.trans (hvc n))
  have Hzero:=regular_original_retained_squared_mismatch_ratio_tendsto_zero_along
    hm hdelta hroom hcl hcu hAz hC0 hCt dim hdim M W v hxs hWlim hclock C hC hv hvc
    (G.omission_over_larger_scale_zero W hxs) (G.eventually_geometric_gates.mono fun n hn=>⟨hn.2,hn.1⟩)
  have hzero : Tendsto (fun n=>(∫w,(S n w-rad n w)^2∂mu n)/(W n)^3) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>div_nonneg (integral_nonneg (fun _=>sq_nonneg _)) (pow_nonneg (hW n).le _)) _ Hzero
    intro n
    exact div_le_div_of_nonneg_right
      (integral_mono_measure (hmu n) (ae_of_all _ (fun _=>sq_nonneg _))
        ((M n).original_retained_mismatch_integrable (v n)).2) (pow_nonneg (hW n).le _)
  have hrm n : Measurable (rad n) :=
    (omittedSweepQuantile_continuous zero_le_one ⟨(M n).data.hs.1,(M n).data.hs1⟩ (M n).context.hc (M n).context.hk (M n).context.hkc
      (M n).context.hm (M n).context.hM (M n).alpha).measurable.comp measurable_subtype_coe
  have herr:=comparison_original_mass_eventually_bounded_strength_errors mu (fun _=>inferInstance)
    rad (fun n w=>S n w-rad n w) (fun n=>(M n).context.d) (fun n=>(M n).lam) W
    hrm hi hi2 (fun n=>(M n).context.hd) (fun n=>(M n).hlam.le) hW (fun n=>(M n).hld)
    hC.le hK hmass hwork hzero
  have hiWeighted n : Integrable (fun w=>e n w*(S n w-rad n w)/(W n)^3) (nu n) :=
    (M n).original_weighted_mismatch_integrable _ _
  have hweighted0 : Tendsto (fun n=>∫w,|e n w*(S n w-rad n w)/(W n)^3|∂nu n) atTop (𝓝 0) := by
    apply squeeze_zero (fun n=>integral_nonneg (fun _=>abs_nonneg _)) _ herr.2.2.2
    intro n
    apply integral_mono (hiWeighted n).abs (herr.2.2.1 n).abs
    intro w
    dsimp only [e]
    simp only [abs_div,abs_mul,abs_of_nonneg ((M n).coefficient_nonneg w),
      abs_of_nonneg (laplaceComparisonStrength_pos (M n).context.d (M n).hlam (rad n w)).le]
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right ((M n).coefficient_le_strength_high_only w) (abs_nonneg _))
      (abs_nonneg _)
  have hclock n (w : ParisiFinite.OrderPoint) :
      comparisonScalarMassClockOn h0 b0 e S rad n w=actualMixedClock (dim n+1) (M n).bf (M n).hf w :=
    ((M n).inherited_mixed_clock_eq_nativeScalarClock w.property).symm
  have hcav' n : Integrable (fun w=>(S n w-Gamma n
      (comparisonScalarMassClockOn h0 b0 e S rad n w))/(W n)^3) (nu n) := by
    simp_rw [hclock];exact hcav n
  have hcav0' : Tendsto (fun n=>∫w,|(S n w-Gamma n
      (comparisonScalarMassClockOn h0 b0 e S rad n w))/(W n)^3|∂nu n) atTop (𝓝 0) := by
    simp_rw [hclock];exact hcav0
  have hbare:=actual_inherited_restricted_bare_error_of_vanishing_clocks_along hm hdelta hroom hcl hcu hAz hC0 hCt
    dim hdim M G W hxs F hF C hC hcut hEq4
  have hresponse:=comparison_scalar_mass_response_L1_tendsto_on nu Gamma h0 b0 e S rad W hT
    (fun n=>(hW n).ne') hiWeighted hcav' hbare.1 hweighted0 hcav0' hbare.2
  have hspin n : Integrable (fun w=>S n w/W n-rad n w/W n) (nu n) := by
    simpa only [sub_div] using herr.1 n
  have hspin0 : Tendsto (fun n=>∫w,|S n w/W n-rad n w/W n|∂nu n) atTop (𝓝 0) := by
    simpa only [sub_div] using herr.2.1
  have hclock0:=comparison_scalar_mass_clock_L1_tendsto_on nu h0 b0 e S rad W hT
    (fun n=>(hW n).ne') hWlim hspin hiWeighted hbare.1 hspin0 hweighted0 hbare.2
  simp_rw [hclock] at hresponse hclock0
  exact ⟨hresponse.1,hresponse.2,hclock0.1,hclock0.2⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
