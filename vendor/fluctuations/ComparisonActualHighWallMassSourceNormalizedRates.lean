module

public import ComparisonActualHighWallMassSourcePointwise
public import ComparisonActualHighWallCriticalClockRadiusL1Along
public import ComparisonNativeActualNormalizedScalarGap

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal
set_option maxHeartbeats 9000000

namespace ActualHighWallOverlapMinimum

theorem actual_high_wall_critical_normalized_mass_rates
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1)
      m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (hMassSource : ∀C>0,Tendsto (fun n=>
      (∫u in 0..C*(M n).xs,
        |orderedPathS (dim n+1) (M n).bf (M n).hf u-
          scalarCovarianceResponse hT
            ((M n).data.scalarMassProfile (M n).alpha)
            (actualMixedClock (dim n+1) (M n).bf (M n).hf u)|)/
        (M n).xs^4) atTop (𝓝 0))
    (C : ℝ) (hC : 1 ≤ C) :
    let v := fun n=>min (C*(M n).xs) 1
    let mu := fun n=>comparisonNormalizedClockMass (M n).xs (v n)
    let S := fun n (w : ParisiFinite.OrderPoint) =>
      orderedPathS (dim n+1) (M n).bf (M n).hf w
    let R := fun n (w : ParisiFinite.OrderPoint) =>
      (M n).data.wallRadius (M n).alpha w
    let K := fun n (w : ParisiFinite.OrderPoint) =>
      actualMixedClock (dim n+1) (M n).bf (M n).hf w
    let Gamma := fun n=>scalarCovarianceResponse hT
      ((M n).data.scalarMassProfile (M n).alpha)
    let q := fun n (w : ParisiFinite.OrderPoint) =>
      actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf w/(M n).xs
    Tendsto (fun n=>∫w,|(S n w-Gamma n (K n w))/(M n).xs^3|∂mu n)
      atTop (𝓝 0) ∧
    Tendsto (fun n=>∫w,|S n w/(M n).xs-R n w/(M n).xs|∂mu n)
      atTop (𝓝 0) ∧
    Tendsto (fun n=>∫w,|q n w-R n w/(M n).xs|∂mu n)
      atTop (𝓝 0) := by
  dsimp only
  let v := fun n=>min (C*(M n).xs) 1
  have hv n : v n∈Icc (0:ℝ) 1 :=
    ⟨le_min (mul_nonneg (zero_le_one.trans hC) (M n).hxs.le) zero_le_one,
      min_le_right _ _⟩
  have Hunit : ∀ᶠn in atTop,C*(M n).xs ≤ 1 :=
    (hx.const_mul C).eventually
      (eventually_le_nhds (show C*(0:ℝ)<1 by simp))
  have Hsource := hMassSource C (zero_lt_one.trans_le hC)
  have Hmean := actual_high_wall_critical_mean_radius_l1_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hD dim hdim M hfixed hx hsRatio
    C (zero_lt_one.trans_le hC)
  have Hclock := actual_high_wall_critical_clock_radius_l1_along
    hm hdelta hroom hcl hcu hAz hC0 hCt hD hT dim hdim M hfixed
    (fun n=>by rw [hTeq n]) hx hsRatio C hC
  refine ⟨?_,?_,?_⟩
  · apply Hsource.congr'
    filter_upwards [Hunit] with n hn
    have heq : v n=C*(M n).xs := min_eq_left hn
    rw [comparison_normalized_cubic_residual_integral_exact
      (fun u=>orderedPathS (dim n+1) (M n).bf (M n).hf u-
        scalarCovarianceResponse hT ((M n).data.scalarMassProfile (M n).alpha)
          (actualMixedClock (dim n+1) (M n).bf (M n).hf u)) (M n).hxs (hv n),heq]
  · apply Hmean.congr'
    filter_upwards [Hunit] with n hn
    have heq : v n=C*(M n).xs := min_eq_left hn
    rw [comparison_normalized_clock_error_exact
      (orderedPathS (dim n+1) (M n).bf (M n).hf)
      ((M n).data.wallRadius (M n).alpha) (M n).hxs,
      comparison_original_retained_integral_eq_interval (hv n)
        (fun u=>|orderedPathS (dim n+1) (M n).bf (M n).hf u-
          (M n).data.wallRadius (M n).alpha u|),heq]
  · apply Hclock.congr'
    filter_upwards [Hunit] with n hn
    have heq : v n=C*(M n).xs := min_eq_left hn
    rw [comparison_normalized_clock_error_exact
      (actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf)
      ((M n).data.wallRadius (M n).alpha) (M n).hxs,
      comparison_original_retained_integral_eq_interval (hv n)
        (fun u=>|actualScalarClockQuantile T (dim n+1) (M n).bf (M n).hf u-
          (M n).data.wallRadius (M n).alpha u|),heq]
    rw [←hTeq n]

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
