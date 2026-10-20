module

public import ComparisonQuantileLinearLimit
public import ComparisonGlobalScalarRigidity
public import ComparisonJointScalarRadiusCompactness

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy GaussianCalculus Scalar
open scoped Topology
set_option maxHeartbeats 5000000

def comparisonNativeScalarA {T : ℝ} (hT : 0 < T) (beta : boundedMassProfiles) : ℝ :=
  T^3*(scalarTailSpatialJet hT beta 4 0 0)^2

def comparisonNativeScalarB {T : ℝ} (hT : 0 < T) (beta : boundedMassProfiles) : ℝ :=
  2*T^2*(scalarTailSpatialJet hT beta 2 0 0)^3

theorem comparison_native_scalar_coefficients_pos {T : ℝ} (hT : 0 < T)
    (beta : boundedMassProfiles) :
    0 < comparisonNativeScalarA hT beta ∧ 0 < comparisonNativeScalarB hT beta := by
  have h4 : scalarTailSpatialJet hT beta 4 0 0 < 0 :=
    scalarProfileJet_four_zero_neg (rescaledMassProfile beta hT)
      (fun s => (beta.property.1 (s/T)).2) _ _
  have h2 : 0 < scalarTailSpatialJet hT beta 2 0 0 :=
    scalarProfileJet_curvature_pos (rescaledMassProfile beta hT)
      (fun s => (beta.property.1 (s/T)).2) _ _ _
  exact ⟨mul_pos (pow_pos hT 3) (sq_pos_of_ne_zero h4.ne),by
    unfold comparisonNativeScalarB
    positivity⟩

theorem comparison_linear_profile_support_positive {V : ℝ → ℝ} {kappa t : ℝ}
    (hV : Monotone V) (hkappa : 0 < kappa)
    (hlinear : ∀s > 0, V s=kappa*s) (ht : 0 < t) :
    t ∈ comparisonIncrementSupport V := by
  intro eps heps
  rw [hlinear (t+eps) (by linarith)]
  by_cases hlo : 0 < t-eps
  · rw [hlinear (t-eps) hlo]
    nlinarith
  · have hm := hV (show t-eps ≤ t/2 by linarith)
    rw [hlinear (t/2) (by linarith)] at hm
    nlinarith

theorem comparison_linear_scalar_primitives_zero
    {U V : ℝ → ℝ} {A B sigma : ℝ}
    (hV : Monotone V) (hA : 0 < A) (hB : 0 < B)
    (hUlinear : ∀t > 0, U t=(A/B)*t)
    (hVlinear : ∀t > 0, V t=(A/B)*t)
    (hzero : ∀t ∈ comparisonIncrementSupport V,comparisonGlobalScalarResponse U A B sigma t=0) :
    sigma=0 ∧ (∀t ≥ 0, comparisonGlobalScalarSlope U A B sigma t=0) ∧
      (∀t ≥ 0, comparisonGlobalScalarResponse U A B sigma t=0) := by
  have hp t (ht : 0 ≤ t) : comparisonGlobalScalarSlope U A B sigma t=sigma := by
    have hz : (∫s in 0..t,A*s-B*U s)=0 := by
      apply intervalIntegral.integral_zero_ae
      filter_upwards [] with s hs
      rw [uIoc_of_le ht] at hs
      rw [hUlinear s hs.1]
      field_simp
      <;> ring
    simp only [comparisonGlobalScalarSlope,hz,add_zero]
  have hg t (ht : 0 ≤ t) : comparisonGlobalScalarResponse U A B sigma t=t*sigma := by
    unfold comparisonGlobalScalarResponse
    calc
      (∫s in 0..t,comparisonGlobalScalarSlope U A B sigma s) = ∫s in 0..t,sigma := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [] with s hs
        rw [uIoc_of_le ht] at hs
        exact hp s hs.1.le
      _ = t*sigma := by simp
  have hz1 := hzero 1 (comparison_linear_profile_support_positive hV (div_pos hA hB)
    hVlinear zero_lt_one)
  rw [hg 1 zero_le_one,one_mul] at hz1
  refine ⟨hz1,fun t ht => (hp t ht).trans hz1,?_⟩
  intro t ht
  rw [hg t ht,hz1,mul_zero]

structure ComparisonNativeProfileLimitData
    (A : ComparisonShiftedInverseSequence) (q : ℕ → ℝ → ℝ) (x : ℕ → ℝ)
    {T : ℝ} (hT : 0 < T) (beta : boundedMassProfiles)
    (U V : ℝ → ℝ) (sigma cl cu Az : ℝ) where
  qmono : ∀n, MonotoneOn (q n) (Icc (0 : ℝ) 1)
  qbounds : ∀n u, u ∈ Icc (0 : ℝ) 1 → q n u ∈ Icc (0 : ℝ) 1
  xpos : ∀n, 0 < x n
  xzero : Tendsto x atTop (𝓝 0)
  origin_nonnegative : ∀n, 0 ≤ A.origin n
  omitted_small : Tendsto (fun n => A.u0 n/x n) atTop (𝓝 0)
  scalar_law : ∀t, Tendsto (fun n => (quantileMassProfile (q n) (qbounds n)).val (x n*t)/x n)
    atTop (𝓝 (U t))
  radius_law : ∀t, Tendsto (fun n => (A.alpha n).val.val (x n*t)/x n) atTop (𝓝 (V t))
  lower_pos : 0 < cl
  threshold : ℕ → ℝ
  threshold_bound : ∀ᶠ n in atTop, threshold n ≤ Az*x n
  outer_regular : ∀ᶠ n in atTop, ∀r ∈ Icc (threshold n) 1,
    cl*r ≤ (A.alpha n).val.val r ∧ (A.alpha n).val.val r ≤ cu*r
  original_coupling : ∀R > 0, ∃v : ℕ → ℝ,
    (∀n, v n ∈ Icc (0 : ℝ) 1) ∧
    (∀ᶠ n in atTop, x n*R < q n (v n) ∧ x n*R < A.radius n (v n)) ∧
    Tendsto (fun n => (∫w : ParisiFinite.OrderPoint in {w | (w : ℝ) ≤ v n},
      |q n (w : ℝ)-A.radius n (w : ℝ)| ∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(x n)^2)
      atTop (𝓝 0)
  support_zero : ∀t ∈ comparisonIncrementSupport V,
    comparisonGlobalScalarResponse U (comparisonNativeScalarA hT beta)
      (comparisonNativeScalarB hT beta) sigma t=0
  virtual_gap : ∀a b, 0 ≤ a → a < b → a ∈ comparisonIncrementSupport V →
    b ∈ comparisonIncrementSupport V → (∀r ∈ Ioo a b, r ∉ comparisonIncrementSupport V) →
    0 < V ((a+b)/2) → Nonempty (ComparisonVirtualGapData
      (comparisonGlobalScalarResponse U (comparisonNativeScalarA hT beta)
        (comparisonNativeScalarB hT beta) sigma) a b)

namespace ComparisonNativeProfileLimitData

theorem scalar_monotone {A q x T hT beta U V sigma cl cu Az}
    (d : @ComparisonNativeProfileLimitData A q x T hT beta U V sigma cl cu Az) : Monotone U := by
  intro s t hst
  apply le_of_tendsto_of_tendsto (d.scalar_law s) (d.scalar_law t)
  exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
    ((quantileMassProfile (q n) (d.qbounds n)).property.2
      (mul_le_mul_of_nonneg_left hst (d.xpos n).le)) (d.xpos n).le

theorem radius_monotone {A q x T hT beta U V sigma cl cu Az}
    (d : @ComparisonNativeProfileLimitData A q x T hT beta U V sigma cl cu Az) : Monotone V := by
  intro s t hst
  apply le_of_tendsto_of_tendsto (d.radius_law s) (d.radius_law t)
  exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
    ((A.alpha n).val.property.2 (mul_le_mul_of_nonneg_left hst (d.xpos n).le)) (d.xpos n).le

theorem scalar_nonnegative {A q x T hT beta U V sigma cl cu Az}
    (d : @ComparisonNativeProfileLimitData A q x T hT beta U V sigma cl cu Az) (t : ℝ) : 0 ≤ U t := by
  apply ge_of_tendsto (d.scalar_law t)
  exact Eventually.of_forall fun n => div_nonneg
    ((quantileMassProfile (q n) (d.qbounds n)).property.1 _).1 (d.xpos n).le

theorem rigidity {A q x T hT beta U V sigma cl cu Az}
    (d : @ComparisonNativeProfileLimitData A q x T hT beta U V sigma cl cu Az) :
    let kappa := comparisonNativeScalarA hT beta/comparisonNativeScalarB hT beta
    0 < kappa ∧ (cl ≤ kappa ∧ kappa ≤ cu) ∧
      (∀t > 0, U t=kappa*t) ∧ (∀t > 0, V t=kappa*t) ∧
      TendstoLocallyUniformlyOn (fun n v => A.radius n (x n*v)/x n)
        (fun v => v/kappa) atTop (Ioi (0 : ℝ)) ∧
      TendstoLocallyUniformlyOn (fun n v => q n (x n*v)/x n)
        (fun v => v/kappa) atTop (Ioi (0 : ℝ)) ∧
      sigma=0 ∧
      (∀t ≥ 0, comparisonGlobalScalarSlope U (comparisonNativeScalarA hT beta)
        (comparisonNativeScalarB hT beta) sigma t=0) ∧
      (∀t ≥ 0, comparisonGlobalScalarResponse U (comparisonNativeScalarA hT beta)
        (comparisonNativeScalarB hT beta) sigma t=0) := by
  dsimp only
  have hAB := comparison_native_scalar_coefficients_pos hT beta
  have hk := div_pos hAB.1 hAB.2
  have hUV := comparison_shifted_scalar_radius_laws_ae_identified A q x U V
    d.origin_nonnegative d.qmono d.qbounds d.xpos d.radius_monotone d.omitted_small
    d.scalar_law d.radius_law d.original_coupling
  have hneg := A.rescaled_cdf_negative_axis_zero x V d.xpos d.origin_nonnegative
    d.omitted_small d.radius_law
  have hgrowth := A.rescaled_cdf_outer_growth x d.threshold V d.xpos d.xzero
    d.threshold_bound d.outer_regular d.radius_law
  have hlinear := comparison_global_scalar_primitives_rigidity d.scalar_monotone
    d.radius_monotone hUV (fun t _ => d.scalar_nonnegative t) hneg hAB.1 hAB.2 d.lower_pos
    (fun t ht => (hgrowth t ht).1) d.support_zero d.virtual_gap
  have hbounds := A.rescaled_linear_cdf_slope_bounds x d.threshold V d.xpos d.xzero
    d.threshold_bound d.outer_regular d.radius_law hlinear.2
  have hVR : ∀t > 0,Tendsto (fun n => (A.alpha n).val.val (x n*t)/x n)
      atTop (𝓝 ((comparisonNativeScalarA hT beta/comparisonNativeScalarB hT beta)*t)) := by
    intro t ht
    simpa only [hlinear.2 t ht] using d.radius_law t
  have hUQ : ∀t > 0,Tendsto
      (fun n => (quantileMassProfile (q n) (d.qbounds n)).val (x n*t)/x n)
      atTop (𝓝 ((comparisonNativeScalarA hT beta/comparisonNativeScalarB hT beta)*t)) := by
    intro t ht
    simpa only [hlinear.1 t ht] using d.scalar_law t
  exact ⟨hk,hbounds,hlinear.1,hlinear.2,
    A.rescaled_inverse_locally_uniform x hk d.xpos d.xzero d.omitted_small hVR,
    comparison_quantile_locally_uniform_of_linear_law q x d.qmono d.qbounds d.xpos d.xzero hk hUQ,
    comparison_linear_scalar_primitives_zero d.radius_monotone hAB.1 hAB.2
      hlinear.1 hlinear.2 d.support_zero⟩

end ComparisonNativeProfileLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization
