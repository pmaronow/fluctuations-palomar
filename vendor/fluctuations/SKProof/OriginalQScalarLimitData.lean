module

public import ComparisonActualHighWallThetaZeroSelectedAmplitude
public import ComparisonActualHighWallInnovation
public import ComparisonNativeActualLocalScalarLimitData
public import ComparisonShiftedQuantileCDF

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal
namespace ActualThetaZeroOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}

def originalQShiftedInverseSequence
    (Q : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock) :
    ComparisonShiftedInverseSequence where
  origin:=fun n=>(Q n).data.rmin
  u0:=fun n=>(Q n).data.s
  c:=fun n=>(Q n).data.k 1
  k:=fun n=>(Q n).data.k
  M:=fun n=>(Q n).data.M
  hwork:=fun n=>(Q n).data.hr
  hc:=fun n=>(Q n).data.hc
  hk:=fun n=>(Q n).data.hk
  hkc:=fun n=>(Q n).data.hkc
  hm:=fun n=>(Q n).data.hm
  hM:=fun n=>(Q n).data.hM
  alpha:=fun n=>(Q n).alpha

def inheritedScalarMassProfile {n : ℕ}
    (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {T : ℝ} (hT : 0<T)
    (htotal : ∀u∈Icc (0:ℝ) 1,(Q.sweepHf u:ℝ)+(Q.sweepBf u:ℝ) ≤ T) : boundedMassProfiles :=
  actualMixedMassProfile hT (n+1) Q.data.hn Q.sweepBf Q.sweepHf
    Q.sweep_bf_monotone Q.sweep_hf_monotone htotal

def actualRadiusMassProfile {n : ℕ}
    (Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) : boundedMassProfiles :=
  quantileMassProfile (Q.data.wallRadius Q.alpha)
    (fun u _=>⟨Q.data.hrbounds.1.le.trans (Q.data.wallRadius_bounds Q.alpha u).1,
      (Q.data.wallRadius_bounds Q.alpha u).2⟩)

end ActualThetaZeroOverlapMinimum

structure OriginalQLocalScalarLimitData
    {m delta cl cu Az C0 Ct D Bclock T : ℝ} (hT : 0<T) (S : ℝ)
    {dim : ℕ→ℕ}
    (Q : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,((Q n).sweepHf u:ℝ)+((Q n).sweepBf u:ℝ) ≤ T) where
  origin_small : Tendsto (fun n=>(Q n).data.rmin/(Q n).xs) atTop (𝓝 0)
  omitted_small : Tendsto (fun n=>(Q n).data.s/(Q n).xs) atTop (𝓝 0)
  beta : boundedMassProfiles
  radiusLimit : boundedMassProfiles
  U : NonnegativeMassProfile
  V : NonnegativeMassProfile
  sigma : ℝ
  ambient_limit : Tendsto (fun n=>(Q n).inheritedScalarMassProfile hT (htotal n)) atTop (𝓝 beta)
  radius_limit : Tendsto (fun n=>(Q n).actualRadiusMassProfile) atTop (𝓝 radiusLimit)
  scalar_cdf_limit : ∀t : ℝ,Tendsto (fun n=>
    ((Q n).inheritedScalarMassProfile hT (htotal n)).val ((S/T)*((Q n).xs*t))/(Q n).xs)
      atTop (𝓝 (U.mass t))
  radius_cdf_limit : ∀t : ℝ,Tendsto (fun n=>
    (Q n).actualRadiusMassProfile.val ((Q n).xs*t)/(Q n).xs) atTop (𝓝 (V.mass t))
  limits : ∀R : ℝ,0<R→
    ContinuousOn (comparisonLocalScalarLimitSlope hT S beta U sigma) (Icc (0:ℝ) R) ∧
    TendstoUniformlyOn (fun n=>comparisonLocalScalarSlope hT S
      ((Q n).inheritedScalarMassProfile hT (htotal n)) (Q n).xs)
      (comparisonLocalScalarLimitSlope hT S beta U sigma) atTop (Icc (0:ℝ) R) ∧
    TendstoUniformlyOn (fun n=>comparisonRescaledScalarResponse
      (scalarCovarianceResponse hT ((Q n).inheritedScalarMassProfile hT (htotal n))) S (Q n).xs)
      (comparisonLocalScalarLimitResponse hT S beta U sigma) atTop (Icc (0:ℝ) R)
  positive_coefficients : 0<S^3*(scalarTailSpatialJet hT beta 4 0 0)^2 ∧
    0<2*S^2*(scalarTailSpatialJet hT beta 2 0 0)^3
  coefficient_ratio : (S^3*(scalarTailSpatialJet hT beta 4 0 0)^2)/
    (2*S^2*(scalarTailSpatialJet hT beta 2 0 0)^3)=(S/T)*scalarInitialDensityConstant hT beta
  support_zero : ∀t : ℝ,0<t→(∀e : ℝ,0<e→V.mass (t-e)<V.mass (t+e))→
    comparisonLocalScalarLimitResponse hT S beta U sigma t=0

namespace OriginalQLocalScalarLimitData
variable {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0<T} {dim : ℕ→ℕ}
  {Q : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
  {htotal : ∀n,∀u∈Icc (0:ℝ) 1,((Q n).sweepHf u:ℝ)+((Q n).sweepBf u:ℝ) ≤ T}

theorem radius_inverse_cdf_limit_original_q (d : OriginalQLocalScalarLimitData hT S Q htotal) :
    ∀t : ℝ,Tendsto (fun n=>(Q n).alpha.val.val ((Q n).xs*t)/(Q n).xs)
      atTop (𝓝 (d.V.mass t)) := by
  intro t
  let A:=ActualThetaZeroOverlapMinimum.originalQShiftedInverseSequence Q
  have Hdiff : Tendsto (fun n=>((Q n).actualRadiusMassProfile.val ((Q n).xs*t)-
      (Q n).alpha.val.val ((Q n).xs*t))/(Q n).xs) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_norm_tendsto_zero).mpr
    apply squeeze_zero (fun _=>norm_nonneg _) _ d.omitted_small
    intro n
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (Q n).hxs]
    exact div_le_div_of_nonneg_right
      (A.radius_cdf_error_le_omitted_mass (fun n=>(Q n).data.hrbounds.1.le) n ((Q n).xs*t)) (Q n).hxs.le
  have H:=(d.radius_cdf_limit t).sub Hdiff
  simp only [sub_zero] at H
  convert H using 1
  ext n
  ring

theorem radius_negative_axis_zero_original_q (d : OriginalQLocalScalarLimitData hT S Q htotal) :
    ∀t : ℝ,t<0→d.V.mass t=0 :=
  (ActualThetaZeroOverlapMinimum.originalQShiftedInverseSequence Q).rescaled_cdf_negative_axis_zero
    (fun n=>(Q n).xs) d.V.mass (fun n=>(Q n).hxs) (fun n=>(Q n).data.hrbounds.1.le)
    d.omitted_small d.radius_inverse_cdf_limit_original_q

def comp (d : OriginalQLocalScalarLimitData hT S Q htotal)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    OriginalQLocalScalarLimitData hT S (fun n => Q (phi n))
      (fun n => htotal (phi n)) where
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

end OriginalQLocalScalarLimitData

end OAI.SKFluctuations.LaplaceWindowFormalization
