module

public import ComparisonGlobalProfileRigidity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 3000000

def comparisonGlobalScalarSlope (U : ℝ → ℝ) (A B sigma t : ℝ) : ℝ :=
  sigma+∫s in 0..t,A*s-B*U s

def comparisonGlobalScalarResponse (U : ℝ → ℝ) (A B sigma t : ℝ) : ℝ :=
  ∫s in 0..t,comparisonGlobalScalarSlope U A B sigma s

theorem comparison_global_scalar_flux_intervalIntegrable
    {U : ℝ → ℝ} (hU : Monotone U) (A B a b : ℝ) :
    IntervalIntegrable (fun s=>A*s-B*U s) volume a b :=
  ((continuous_id.const_mul A).intervalIntegrable a b).sub
    ((hU.intervalIntegrable (a:=a) (b:=b)).const_mul B)

theorem comparison_global_scalar_slope_continuous {U : ℝ → ℝ}
    (hU : Monotone U) (A B sigma : ℝ) : Continuous (comparisonGlobalScalarSlope U A B sigma) := by
  exact continuous_const.add (intervalIntegral.continuous_primitive
    (comparison_global_scalar_flux_intervalIntegrable hU A B) 0)

theorem comparison_global_scalar_response_deriv {U : ℝ → ℝ}
    (hU : Monotone U) (A B sigma t : ℝ) :
    HasDerivAt (comparisonGlobalScalarResponse U A B sigma)
      (comparisonGlobalScalarSlope U A B sigma t) t := by
  have hc := comparison_global_scalar_slope_continuous hU A B sigma
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter volume (𝓝 t)) hc.continuousAt

theorem comparison_global_scalar_slope_primitive {U : ℝ → ℝ}
    (hU : Monotone U) (A B sigma a b : ℝ) :
    comparisonGlobalScalarSlope U A B sigma b-comparisonGlobalScalarSlope U A B sigma a=
      ∫t in a..b,A*t-B*U t := by
  have hh := intervalIntegral.integral_interval_sub_left
    (comparison_global_scalar_flux_intervalIntegrable hU A B 0 b)
    (comparison_global_scalar_flux_intervalIntegrable hU A B 0 a)
  unfold comparisonGlobalScalarSlope
  linarith

theorem comparison_global_scalar_slope_ae_deriv {U : ℝ → ℝ}
    (hU : Monotone U) (A B sigma : ℝ) :
    ∀ᵐ t ∂volume,HasDerivAt (comparisonGlobalScalarSlope U A B sigma) (A*t-B*U t) t := by
  have hUL : LocallyIntegrable U volume := hU.locallyIntegrable
  have hBU : LocallyIntegrable (fun t=>B*U t) volume := by
    convert hUL.smul B using 1
  have hF : LocallyIntegrable (fun t=>A*t-B*U t) volume :=
    (continuous_id.const_mul A).locallyIntegrable.sub hBU
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hF] with t ht
  exact (ht 0).const_add sigma

theorem comparison_global_scalar_primitives_rigidity
    {U V : ℝ → ℝ} {A B c R sigma : ℝ}
    (hU : Monotone U) (hV : Monotone V) (hUV : U=ᵐ[volume] V)
    (hU0 : ∀t>0,0≤U t) (hVneg : ∀t<0,V t=0)
    (hA : 0<A) (hB : 0<B) (hc : 0<c) (hgrowth : ∀t,R≤t → c*t≤V t)
    (hzero : ∀t∈comparisonIncrementSupport V,comparisonGlobalScalarResponse U A B sigma t=0)
    (hvirtual : ∀a b,0≤a → a<b → a∈comparisonIncrementSupport V → b∈comparisonIncrementSupport V →
      (∀r∈Ioo a b,r∉comparisonIncrementSupport V) → 0<V ((a+b)/2) →
      Nonempty (ComparisonVirtualGapData (comparisonGlobalScalarResponse U A B sigma) a b)) :
    (∀t>0,U t=(A/B)*t) ∧ (∀t>0,V t=(A/B)*t) := by
  apply comparison_global_profile_rigidity hU hV hUV hU0 hVneg hA hB hc hgrowth
    (fun t _=>comparison_global_scalar_response_deriv hU A B sigma t)
    (comparison_global_scalar_slope_continuous hU A B sigma).continuousOn
    (fun a b _ _=>comparison_global_scalar_slope_primitive hU A B sigma a b)
    ?_ (by simp [comparisonGlobalScalarResponse]) hzero hvirtual
  filter_upwards [comparison_global_scalar_slope_ae_deriv hU A B sigma] with t ht _
  exact ht

end OAI.SKFluctuations.LaplaceWindowFormalization
