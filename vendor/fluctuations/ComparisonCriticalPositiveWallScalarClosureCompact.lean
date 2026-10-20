module

public import ComparisonCriticalPositiveWallScalarClosureExactClockL1
public import ComparisonCriticalPositiveWallPhysicalScalarClockAlong
public import ComparisonCriticalPositiveWallScaledRadiusIntegrability
public import ComparisonCriticalPositiveWallRadiusScalarRescaling
public import ComparisonCriticalPositiveWallStrengthIdentity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000

theorem critical_positive_wall_scalar_closure_compact_of_physical_radius_L1
    {m delta cl cu Az C0 Ct D Bclock Tloc T : ℝ}
    (hTloc : 0 < Tloc) (hT : 0 < T)
    (dim : ℕ→ℕ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hrmin : Tendsto (fun n=>(M n).data.rmin/(M n).xs) atTop (𝓝 0))
    (alpha : ℕ→boundedMassProfiles)
    (g spin : ℝ→ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {A : Set ℝ}
    (hspin : ∀t∈Icc a b,Tendsto (fun n=>(M n).actualScaledRadiusSpin t)
      atTop (𝓝 (spin t)))
    (hG : TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hTloc (alpha n)) T (M n).xs) g atTop A)
    (hgc : ∀t∈Icc a b,ContinuousWithinAt g A (spin t))
    (hK : ∀ᶠn in atTop,∀t∈Icc a b,
      actualMixedClock (dim n+1) (M n).bf (M n).hf
        ((M n).alpha.val.val ((M n).xs*t))/(T*(M n).xs)∈A)
    (hL1 : Tendsto (fun n=>(∫r in Ioo ((M n).xs*a) ((M n).xs*b),
      |(M n).radiusS r-scalarCovarianceResponse hTloc (alpha n)
        (actualMixedClock (dim n+1) (M n).bf (M n).hf
          ((M n).alpha.val.val r))|)/(M n).xs^4) atTop (𝓝 0)) :
    ∀ᵐt∂volume.restrict (Icc a b),
      g (spin t)=laplaceComparisonShape t/T*(spin t-t) := by
  let Gamma := fun n=>scalarCovarianceResponse hTloc (alpha n)
  let e := fun n t=>(M n).data.g ((M n).xs*t)
  let s := fun n t=>(M n).radiusS ((M n).xs*t)
  let x := fun n=>(M n).xs
  let K := fun n t=>actualMixedClock (dim n+1) (M n).bf (M n).hf
    ((M n).alpha.val.val ((M n).xs*t))
  have hEq : ∀ᶠn in atTop,∀t∈Icc a b,
      K n t=comparisonNativeScalarClock 0 T (e n t) (x n*t) (s n t) := by
    filter_upwards [eventually_actual_positive_wall_scaled_radius_scalar_clock_exact
      dim M hx hrmin ha] with n hn t ht
    simpa only [K,e,s,x,hTeq n] using hn t ht
  have he : ∀t∈Icc a b,Tendsto (fun n=>e n t/(x n)^2) atTop
      (𝓝 (laplaceComparisonShape t)) := by
    intro t _
    have H : (fun n=>e n t/(x n)^2)=(fun _=>laplaceComparisonShape t) := by
      funext n
      exact (M n).critical_wall_strength_scaled_identity (hfixed n) t
    rw [H]
    exact tendsto_const_nhds
  have hs : ∀t∈Icc a b,Tendsto (fun n=>s n t/x n) atTop (𝓝 (spin t)) := by
    intro t ht
    exact hspin t ht
  have hiActual n : Integrable (fun t=>(s n t-Gamma n (K n t))/(x n)^3)
      (volume.restrict (Icc a b)) := by
    simpa only [IntegrableOn,s,Gamma,K,x] using
      (M n).actual_positive_wall_scaled_radius_scalar_integrable hTloc (alpha n) a b
  have hi : ∀ᶠn in atTop,Integrable (fun t=>(s n t-
      Gamma n (comparisonNativeScalarClock 0 T (e n t) (x n*t) (s n t)))/(x n)^3)
      (volume.restrict (Icc a b)) := by
    filter_upwards [hEq] with n hn
    apply (hiActual n).congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hn t ht]
  have hScaled : Tendsto (fun n=>∫t in Icc a b,
      |(s n t-Gamma n (K n t))/(x n)^3|) atTop (𝓝 0) := by
    have H : (fun n=>∫t in Icc a b,
        |(s n t-Gamma n (K n t))/(x n)^3|) =
        (fun n=>(∫r in Ioo ((M n).xs*a) ((M n).xs*b),
          |(M n).radiusS r-Gamma n
            (actualMixedClock (dim n+1) (M n).bf (M n).hf
              ((M n).alpha.val.val r))|)/(M n).xs^4) := by
      funext n
      exact comparison_positive_wall_radius_absolute_cubic_rescaling
        (fun r=>(M n).radiusS r-Gamma n
          (actualMixedClock (dim n+1) (M n).bf (M n).hf
            ((M n).alpha.val.val r))) hab (M n).hxs
    rw [H]
    exact hL1
  have hScaledNative : Tendsto (fun n=>∫t in Icc a b,
      |(s n t-Gamma n (comparisonNativeScalarClock 0 T (e n t)
        (x n*t) (s n t)))/(x n)^3|) atTop (𝓝 0) := by
    apply hScaled.congr'
    filter_upwards [hEq] with n hn
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hn t ht]
  apply comparison_scalar_closure_of_exact_clock_radius_L1 Gamma e s x
    g laplaceComparisonShape spin hT (fun n=>(M n).hxs) hx he hs hG hgc
  · filter_upwards [hEq,hK] with n hn heK t ht
    rw [←hn t ht]
    exact heK t ht
  · exact hi
  · exact hScaledNative

end OAI.SKFluctuations.LaplaceWindowFormalization
