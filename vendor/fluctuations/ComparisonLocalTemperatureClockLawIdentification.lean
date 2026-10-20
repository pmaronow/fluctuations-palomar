module

public import ComparisonNormalizedLocalTemperatureClockCDF
public import ComparisonGlobalClockLawIdentification

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy ProbabilityTheory
open scoped Topology
set_option maxHeartbeats 8000000

theorem comparison_actual_local_temperature_clock_laws_ae_identified
    (q r : ℕ → ℝ → ℝ) (gamma : ℝ) (x : ℕ → ℝ) (U V : ℝ → ℝ)
    (hgamma : 0<gamma)
    (hq : ∀n,MonotoneOn (q n) (Icc (0:ℝ) 1))
    (hr : ∀n,MonotoneOn (r n) (Icc (0:ℝ) 1))
    (hqb : ∀n u,u∈Icc (0:ℝ) 1 → q n u∈Icc (0:ℝ) 1)
    (hrb : ∀n u,u∈Icc (0:ℝ) 1 → r n u∈Icc (0:ℝ) 1)
    (hx : ∀n,0<x n) (hVm : Monotone V)
    (hU : ∀t : ℝ,Tendsto (fun n=>(quantileMassProfile (q n) (hqb n)).val
      (gamma*(x n*t))/x n) atTop (𝓝 (U t)))
    (hV : ∀t : ℝ,Tendsto (fun n=>(quantileMassProfile (r n) (hrb n)).val
      (x n*t)/x n) atTop (𝓝 (V t)))
    (hlocal : ∀R : ℝ,0<R → ∃v : ℕ → ℝ,
      (∀n,v n∈Icc (0:ℝ) 1) ∧
      (∀ᶠn in atTop,gamma*(x n*R)<q n (v n) ∧ x n*R<r n (v n)) ∧
      Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ)≤v n},
        |q n (w:ℝ)/gamma-r n (w:ℝ)|∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(x n)^2)
        atTop (𝓝 0)) : U=ᵐ[volume] V := by
  have hc : ∀ᵐt : ℝ,ContinuousAt V t := by
    apply ae_iff.mpr
    exact hVm.countable_not_continuousAt.measure_zero volume
  filter_upwards [hc] with t ht
  let R:=max (t+1) 1
  have hR:0<R:=zero_lt_one.trans_le (le_max_right _ _)
  have htR:t<R:=lt_of_lt_of_le (by linarith) (le_max_left _ _)
  obtain ⟨v,hv,hcut,hzero⟩:=hlocal R hR
  let mu:=fun n=>comparisonNormalizedClockMass (x n) (v n)
  let Q:=fun n (w : ParisiFinite.OrderPoint)=>q n (w:ℝ)/(gamma*x n)
  let P:=fun n (w : ParisiFinite.OrderPoint)=>r n (w:ℝ)/x n
  have hUi : ∀s≤R,Tendsto (fun n=>comparisonClockCDF (mu n) (Q n) s) atTop (𝓝 (U s)) := by
    intro s hs
    apply (hU s).congr'
    filter_upwards [hcut] with n hn
    exact (comparison_normalized_local_temperature_clock_cdf_exact
      (q n) (hq n) (hqb n) hgamma (hx n) (hv n) hs hn.1).symm
  have hVi : ∀s≤R,Tendsto (fun n=>comparisonClockCDF (mu n) (P n) s) atTop (𝓝 (V s)) := by
    intro s hs
    apply (hV s).congr'
    filter_upwards [hcut] with n hn
    exact (comparison_normalized_clock_cdf_exact (r n) (hr n) (hrb n)
      (hx n) (hv n) hs hn.2).symm
  have hzi : Tendsto (fun n=>∫w,|Q n w-P n w|∂mu n) atTop (𝓝 0) := by
    apply hzero.congr'
    exact Eventually.of_forall fun n=>by
      simpa only [Q,P,mu,div_div] using
        (comparison_normalized_clock_error_exact (fun u=>q n u/gamma) (r n)
          (v:=v n) (hx n)).symm
  exact comparison_clock_cdf_limits_eq_below_cut mu (fun n=>inferInstance) Q P U V htR
    (fun n=>comparison_normalized_local_temperature_clock_error_integrable
      (q n) (r n) (hq n) (hr n) (hqb n) (hrb n) hgamma (hx n))
    hzi hUi hVi ht

theorem comparison_shifted_local_temperature_scalar_radius_laws_ae_identified
    (A : ComparisonShiftedInverseSequence) (q : ℕ → ℝ → ℝ) (gamma : ℝ) (x : ℕ → ℝ)
    (U V : ℝ → ℝ) (hgamma : 0<gamma) (horigin : ∀n,0≤A.origin n)
    (hq : ∀n,MonotoneOn (q n) (Icc (0:ℝ) 1))
    (hqb : ∀n u,u∈Icc (0:ℝ) 1 → q n u∈Icc (0:ℝ) 1)
    (hx : ∀n,0<x n) (hVm : Monotone V)
    (hu0 : Tendsto (fun n=>A.u0 n/x n) atTop (𝓝 0))
    (hU : ∀t : ℝ,Tendsto (fun n=>(quantileMassProfile (q n) (hqb n)).val
      (gamma*(x n*t))/x n) atTop (𝓝 (U t)))
    (hV : ∀t : ℝ,Tendsto (fun n=>(A.alpha n).val.val (x n*t)/x n) atTop (𝓝 (V t)))
    (hlocal : ∀R : ℝ,0<R → ∃v : ℕ → ℝ,
      (∀n,v n∈Icc (0:ℝ) 1) ∧
      (∀ᶠn in atTop,gamma*(x n*R)<q n (v n) ∧ x n*R<A.radius n (v n)) ∧
      Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ)≤v n},
        |q n (w:ℝ)/gamma-A.radius n (w:ℝ)|∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(x n)^2)
        atTop (𝓝 0)) : U=ᵐ[volume] V :=
  comparison_actual_local_temperature_clock_laws_ae_identified q A.radius gamma x U V
    hgamma hq (fun n=>(A.radius_monotone n).monotoneOn _)
    hqb (A.radiusUnitBounds horigin) hx hVm hU
    (A.radius_quantile_cdf_limit horigin x hx hu0 V hV) hlocal

end OAI.SKFluctuations.LaplaceWindowFormalization
