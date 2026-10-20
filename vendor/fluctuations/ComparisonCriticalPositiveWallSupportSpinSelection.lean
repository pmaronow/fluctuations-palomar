module

public import ComparisonCriticalPositiveWallGradientCore
public import ComparisonActualHighWallCriticalMeanRadiusL1Along
public import ComparisonActualHighWallOriginsAlong
public import ComparisonActualHighWallScalarLimitData
public import ComparisonScalarCDFSupportZeros
public import ComparisonScalarSupportZeros
public import ComparisonGlobalProfileRigidity
public import ComparisonActualHighWallStarClockDistinct
public import ComparisonNativeActualOriginalMassMismatch

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy NativeOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 18000000

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem mass_mean_le_radius_spin_of_radius_le
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u r : ℝ} (hu : u∈Icc (0:ℝ) 1)
    (hur : M.data.wallRadius M.alpha u ≤ r) :
    orderedPathS (n+1) M.bf M.hf u ≤
      orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r) := by
  have hrmin : M.data.rmin ≤ r := (M.data.wallRadius_bounds M.alpha u).1.trans hur
  have hsr : M.data.s ≤ M.alpha.val.val r := by
    have H := M.alpha.val.property.2 hrmin
    simpa only [M.alpha.property.1] using H
  by_cases hus : u ≤ M.data.s
  · exact M.mass_mean_monotone hu (M.alpha.val.property.1 r) (hus.trans hsr)
  · have hsu : M.data.s ≤ u := le_of_not_ge hus
    have H := M.alpha.val.property.2 hur
    rw [M.data.wallRadius_spec M.alpha ⟨hsu,hu.2⟩] at H
    exact M.mass_mean_monotone hu (M.alpha.val.property.1 r) H

theorem radius_spin_le_mass_mean_of_radius_le
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {u r : ℝ} (hu : u∈Icc M.data.s 1)
    (hur : r ≤ M.data.wallRadius M.alpha u) :
    orderedPathS (n+1) M.bf M.hf (M.alpha.val.val r) ≤
      orderedPathS (n+1) M.bf M.hf u := by
  have H := M.alpha.val.property.2 hur
  rw [M.data.wallRadius_spec M.alpha hu] at H
  exact M.mass_mean_monotone (M.alpha.val.property.1 r)
    ⟨M.data.hs.1.le.trans hu.1,hu.2⟩ H

end ActualHighWallOverlapMinimum

theorem exists_critical_positive_wall_support_spin_selections_along
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hxlim : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (V : ℝ→ℝ)
    (hCDF : ∀t,Tendsto (fun n=>(M n).actualRadiusMassProfile.val
      ((M n).xs*t)/(M n).xs) atTop (𝓝 (V t)))
    {p : ℝ} (hp0 : 0 ≤ p) (hp : p∈comparisonIncrementSupport V) :
    ∃ns : ℕ→ℕ,Tendsto ns atTop atTop ∧
      ∃w : ℕ→ParisiFinite.OrderPoint,
        Tendsto (fun j=>(M (ns j)).data.wallRadius (M (ns j)).alpha (w j)/
          (M (ns j)).xs) atTop (𝓝 p) ∧
        Tendsto (fun j=>orderedPathS (dim (ns j)+1)
          (M (ns j)).bf (M (ns j)).hf (w j)/(M (ns j)).xs)
          atTop (𝓝 p) := by
  let R := p+1
  let C := starMassBandConstant cu Az+cu*(|R|+1)+1
  have hCbase := star_mass_band_constant_pos hcu hAz
  have hC : 0 < C := by dsimp only [C];positivity
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
  have Hsmall : ∀ᶠn in atTop,C*(M n).xs ≤ 1 := by
    have H := hxlim.const_mul C
    simpa only [mul_zero] using H.eventually
      (eventually_le_nhds (show C*(0:ℝ) < 1 by simp))
  have Hhigh : ∀ᶠn in atTop,(M n).data.s ≤ C*(M n).xs := by
    filter_upwards [hsRatio.eventually (eventually_le_nhds hC)] with n hn
    exact (div_le_iff₀ (M n).hxs).mp hn
  have Hcut : ∀ᶠn in atTop,(M n).xs*R <
      (M n).data.wallRadius (M n).alpha (v n) := by
    filter_upwards [Hsmall,Hhigh] with n hnSmall hnHigh
    dsimp only [v]
    rw [min_eq_left hnSmall]
    have HR := ((M n).actual_closed_regular_mass_band_radius_bounds
      hcl hcu hAz (M n).hxs le_rfl hCband hnSmall hnHigh
      (show C*(M n).xs∈Icc (C*(M n).xs) (C*(M n).xs) from ⟨le_rfl,le_rfl⟩)).1
    have H := mul_lt_mul_of_pos_right hRC (M n).hxs
    exact (show (M n).xs*R < (C/cu)*(M n).xs by nlinarith only [H]).trans_le HR
  let mu := fun n=>comparisonNormalizedClockMass (M n).xs (v n)
  let radius := fun n (w : ParisiFinite.OrderPoint)=>(M n).data.wallRadius (M n).alpha w/(M n).xs
  let spin := fun n (w : ParisiFinite.OrderPoint)=>
    orderedPathS (dim n+1) (M n).bf (M n).hf w/(M n).xs
  have Hmass : ∀eps : ℝ,0 < eps → ∃c : ℝ,0 < c ∧
      ∀ᶠn in atTop,c ≤ (mu n).real {w | |radius n w-p| < eps} :=
    comparison_actual_radius_cdf_support_mass
      (fun n=>(M n).data.wallRadius (M n).alpha)
      (fun n=>(M n).xs) v V
      (fun n=>((M n).data.wallRadius_monotone (M n).alpha).monotoneOn _)
      (fun n u _=>⟨(M n).data.hrbounds.1.le.trans
        ((M n).data.wallRadius_bounds (M n).alpha u).1,
        ((M n).data.wallRadius_bounds (M n).alpha u).2⟩)
      (fun n=>(M n).hxs) hv Hcut
      (by
        intro t _
        simpa only [ActualHighWallOverlapMinimum.actualRadiusMassProfile] using hCDF t)
      (by dsimp only [R];linarith) (fun δ hδ _=>hp δ hδ)
  have Hr n : Measurable (radius n) :=
    (((M n).data.wallRadius_monotone (M n).alpha).measurable.comp
      measurable_subtype_coe).div_const _
  have Hmi n : Integrable (fun w=>spin n w-radius n w) (mu n) := by
    have Hsm : Measurable (spin n) := by
      have Hmono : Monotone (fun w : ParisiFinite.OrderPoint=>
          orderedPathS (dim n+1) (M n).bf (M n).hf w) :=
        fun u v huv=>(M n).mass_mean_monotone u.property v.property huv
      exact Hmono.measurable.div_const _
    apply Integrable.of_bound ((Hsm.sub (Hr n)).aestronglyMeasurable) (1/(M n).xs)
    filter_upwards [] with w
    have HS := ((M n).full_mass_moments.2.2 w w.property).1
    have HR := (M n).data.wallRadius_bounds (M n).alpha w
    dsimp only [spin,radius,Pi.sub_apply]
    rw [Real.norm_eq_abs,←sub_div,abs_div,abs_of_pos (M n).hxs]
    apply div_le_div_of_nonneg_right _ (M n).hxs.le
    exact abs_le.mpr ⟨by linarith only [HS.1,HR.2],
      by linarith only [HS.2,HR.1,(M n).data.hrbounds.1]⟩
  have Hfull := ActualHighWallOverlapMinimum.actual_high_wall_critical_mean_radius_l1_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hxlim hsRatio C hC
  have Hmis : Tendsto (fun n=>∫w,|spin n w-radius n w|∂mu n) atTop (𝓝 0) := by
    apply Hfull.congr'
    filter_upwards [Hsmall] with n hn
    rw [comparison_normalized_clock_error_exact
      (orderedPathS (dim n+1) (M n).bf (M n).hf)
      ((M n).data.wallRadius (M n).alpha) (M n).hxs,
      comparison_original_retained_integral_eq_interval (hv n)
        (fun u=>|orderedPathS (dim n+1) (M n).bf (M n).hf u-
          (M n).data.wallRadius (M n).alpha u|)]
    simp only [v,min_eq_left hn]
  obtain ⟨ns,hns,w,Hrsel,Hssel,_⟩ := comparison_mass_support_exists_scalar_selections
    mu (fun _=>inferInstance) radius spin (fun _ _=>0) Hr
    (fun _=>by
      apply Integrable.of_bound (by simpa only [abs_zero] using aestronglyMeasurable_const) 0
      filter_upwards [] with w
      simp only [abs_zero,norm_zero,le_refl]) (fun n=>(Hmi n).abs)
    (by simpa only [abs_zero,integral_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ=>(0:ℝ)) atTop (𝓝 0)))
    Hmis Hmass
  exact ⟨ns,hns,w,Hrsel,Hssel⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
