module

public import ComparisonActualHighWallScalarLimitData
public import ComparisonNativeActualLocalScalarLimitGlobalRigidity
public import ComparisonNativeActualLocalScalarLimitZeroPrimitives

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false

namespace ActualHighWallLocalScalarLimitData
variable {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0 < T}
  {dim : ℕ→ℕ}
  {M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
  {htotal : ∀n,∀u∈Icc (0:ℝ) 1,((M n).hf u:ℝ)+((M n).bf u:ℝ)≤T}

def comp (d : ActualHighWallLocalScalarLimitData hT S M htotal)
    (phi : ℕ→ℕ) (hphi : StrictMono phi) :
    ActualHighWallLocalScalarLimitData hT S (fun n=>M (phi n)) (fun n=>htotal (phi n)) where
  origin_small := d.origin_small.comp hphi.tendsto_atTop
  omitted_small := d.omitted_small.comp hphi.tendsto_atTop
  beta := d.beta
  radiusLimit := d.radiusLimit
  U := d.U
  V := d.V
  sigma := d.sigma
  ambient_limit := d.ambient_limit.comp hphi.tendsto_atTop
  radius_limit := d.radius_limit.comp hphi.tendsto_atTop
  scalar_cdf_limit t := (d.scalar_cdf_limit t).comp hphi.tendsto_atTop
  radius_cdf_limit t := (d.radius_cdf_limit t).comp hphi.tendsto_atTop
  limits R hR := ⟨(d.limits R hR).1,
    (d.limits R hR).2.1.seq_tendstoUniformlyOn phi hphi.tendsto_atTop,
    (d.limits R hR).2.2.seq_tendstoUniformlyOn phi hphi.tendsto_atTop⟩
  positive_coefficients := d.positive_coefficients
  coefficient_ratio := d.coefficient_ratio
  support_zero := d.support_zero

theorem radius_outer_growth (d : ActualHighWallLocalScalarLimitData hT S M htotal)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    ∀t : ℝ,Az≤t→cl*t≤d.V.mass t ∧ d.V.mass t≤cu*t :=
  (ActualHighWallOverlapMinimum.actualInverseSequence M).rescaled_cdf_outer_growth
    (fun n=>(M n).xs) (fun n=>(M n).z) d.V.mass
    (fun n=>(M n).hxs) hx
    (Eventually.of_forall fun n=>(M n).hzxs)
    (Eventually.of_forall fun n=>(M n).regular)
    d.radius_inverse_cdf_limit

theorem global_profile_rigidity_of_coupled_laws
    (d : ActualHighWallLocalScalarLimitData hT S M htotal)
    (hUV : d.U.mass =ᵐ[volume] d.V.mass) (hcl : 0 < cl)
    (hxs : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hvirtual : ∀a b,0≤a→a<b→
      a∈comparisonIncrementSupport d.V.mass→b∈comparisonIncrementSupport d.V.mass→
      (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass)→
      Nonempty (ComparisonVirtualGapData
        (comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma) a b)) :
    (∀t>0,d.U.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) ∧
    (∀t>0,d.V.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) := by
  let A := S^3*(scalarTailSpatialJet hT d.beta 4 0 0)^2
  let B := 2*S^2*(scalarTailSpatialJet hT d.beta 2 0 0)^3
  have hresponse : comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma=
      comparisonGlobalScalarResponse d.U.mass A B d.sigma := rfl
  have hzero : ∀t∈comparisonIncrementSupport d.V.mass,
      comparisonGlobalScalarResponse d.U.mass A B d.sigma t=0 := by
    intro t ht
    rw [←hresponse]
    by_cases htp : 0<t
    · exact d.support_zero t htp ht
    · have ht0 : t=0 := le_antisymm (not_lt.mp htp)
        (comparison_increment_support_nonnegative d.radius_negative_axis_zero ht)
      simp only [ht0,comparisonLocalScalarLimitResponse,intervalIntegral.integral_same]
  have H := comparison_global_scalar_primitives_rigidity
    d.U.monotone d.V.monotone hUV (fun t _=>d.U.nonneg t) d.radius_negative_axis_zero
    d.positive_coefficients.1 d.positive_coefficients.2 hcl
    (fun t ht=>(d.radius_outer_growth hxs t ht).1) hzero
    (fun a b ha hab has hbs hgap _=>by
      rw [←hresponse]
      exact hvirtual a b ha hab has hbs hgap)
  simpa only [d.coefficient_ratio] using H

theorem scalar_primitives_zero_of_linear_profiles
    (d : ActualHighWallLocalScalarLimitData hT S M htotal)
    (hUlinear : ∀t>0,d.U.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t)
    (hVlinear : ∀t>0,d.V.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) :
    d.sigma=0 ∧
      (∀t≥0,comparisonLocalScalarLimitSlope hT S d.beta d.U d.sigma t=0) ∧
      (∀t≥0,comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma t=0) := by
  let A := S^3*(scalarTailSpatialJet hT d.beta 4 0 0)^2
  let B := 2*S^2*(scalarTailSpatialJet hT d.beta 2 0 0)^3
  have hratio : A/B=(S/T)*scalarInitialDensityConstant hT d.beta := d.coefficient_ratio
  have hresponse : comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma=
      comparisonGlobalScalarResponse d.U.mass A B d.sigma := rfl
  have hzero : ∀t∈comparisonIncrementSupport d.V.mass,
      comparisonGlobalScalarResponse d.U.mass A B d.sigma t=0 := by
    intro t ht
    rw [←hresponse]
    by_cases htp : 0<t
    · exact d.support_zero t htp ht
    · have ht0 : t=0 := le_antisymm (not_lt.mp htp)
        (comparison_increment_support_nonnegative d.radius_negative_axis_zero ht)
      simp only [ht0,comparisonLocalScalarLimitResponse,intervalIntegral.integral_same]
  exact comparison_linear_scalar_primitives_zero (A:=A) (B:=B) d.V.monotone
    d.positive_coefficients.1 d.positive_coefficients.2
    (fun t ht=>by simpa only [hratio] using hUlinear t ht)
    (fun t ht=>by simpa only [hratio] using hVlinear t ht) hzero

theorem compact_scalar_zero_limits_of_linear_profiles
    (d : ActualHighWallLocalScalarLimitData hT S M htotal)
    (hUlinear : ∀t>0,d.U.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t)
    (hVlinear : ∀t>0,d.V.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) :
    ∀R : ℝ,0<R→
      TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT S
        ((M n).inheritedScalarMassProfile hT (htotal n)) (M n).xs)
        (fun _=>0) atTop (Icc (0:ℝ) R) ∧
      TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
        (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfile hT (htotal n)))
        S (M n).xs) (fun _=>0) atTop (Icc (0:ℝ) R) := by
  have Hzero := d.scalar_primitives_zero_of_linear_profiles hUlinear hVlinear
  intro R hR
  exact ⟨((d.limits R hR).2.1).congr_right (fun t ht=>Hzero.2.1 t ht.1),
    ((d.limits R hR).2.2).congr_right (fun t ht=>Hzero.2.2 t ht.1)⟩

theorem original_radius_locally_uniform_of_linear_profile
    (d : ActualHighWallLocalScalarLimitData hT S M htotal)
    {kappa : ℝ} (hkappa : 0<kappa)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hlinear : ∀t>0,d.V.mass t=kappa*t) :
    TendstoLocallyUniformlyOn (fun n v=>(M n).data.wallRadius (M n).alpha ((M n).xs*v)/(M n).xs)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ)) := by
  exact (ActualHighWallOverlapMinimum.actualInverseSequence M).rescaled_inverse_locally_uniform
    (fun n=>(M n).xs) hkappa (fun n=>(M n).hxs) hx d.omitted_small
    (fun t ht=>by
      simpa only [ActualHighWallOverlapMinimum.actualInverseSequence,hlinear t ht]
        using d.radius_inverse_cdf_limit t)

theorem original_radius_uniform_on_compact_of_linear_profile
    (d : ActualHighWallLocalScalarLimitData hT S M htotal)
    {kappa : ℝ} (hkappa : 0<kappa)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hlinear : ∀t>0,d.V.mass t=kappa*t)
    {a b : ℝ} (ha : 0<a) :
    TendstoUniformlyOn (fun n v=>(M n).data.wallRadius (M n).alpha ((M n).xs*v)/(M n).xs)
      (fun v=>v/kappa) atTop (Icc a b) := by
  exact (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).mp
    ((d.original_radius_locally_uniform_of_linear_profile hkappa hx hlinear).mono
      (fun _ hv=>ha.trans_le hv.1))

end ActualHighWallLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization
