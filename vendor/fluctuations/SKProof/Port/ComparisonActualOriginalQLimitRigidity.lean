module

public import SKProof.Port.ComparisonActualOriginalQHighScalarCuts
public import SKProof.Port.ComparisonActualOriginalQScalarLimitData
public import ComparisonNativeActualLocalScalarLimitGlobalRigidity
public import ComparisonNativeActualLocalScalarLimitZeroPrimitives
public import SKProof.Port.OriginalQHighOnlyBridge

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open NativeOverlapMinimum ActualThetaZeroOverlapMinimum
open scoped Topology NNReal
set_option maxHeartbeats 18000000
set_option linter.unusedVariables false
namespace ActualOriginalQLocalScalarLimitData
variable {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0<T}
  {dim : ℕ→ℕ}
  {M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
  {htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u≤T}

def comp {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T}
    (d : ActualOriginalQLocalScalarLimitData hT S M htotal)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    ActualOriginalQLocalScalarLimitData hT S (fun n=>M (phi n)) (fun n=>htotal (phi n)) where
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

theorem radius_outer_growth (d : ActualOriginalQLocalScalarLimitData hT S M htotal)
    (hAz : 0≤Az) (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0)) :
    ∀t : ℝ,Az≤t→cl*t≤d.V.mass t ∧ d.V.mass t≤cu*t :=
  (ActualThetaZeroOverlapMinimum.originalQShiftedInverseSequence M).rescaled_cdf_outer_growth
    (fun n=>(M n).xs) (fun n=>(M n).z) d.V.mass (fun n=>(M n).hxs) hx
    (Eventually.of_forall fun n=>(M n).hzxs) (Eventually.of_forall fun n=>(M n).regular)
    d.radius_inverse_cdf_limit

theorem global_profile_rigidity_of_coupled_laws
    {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M n).h u+(M n).b u ≤ T}
    (d : ActualOriginalQLocalScalarLimitData hT S M htotal)
    (hUV : d.U.mass =ᵐ[volume] d.V.mass) (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0))
    (hvirtual : ∀a b,0 ≤ a → a < b →
      a∈comparisonIncrementSupport d.V.mass → b∈comparisonIncrementSupport d.V.mass →
      (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) →
      Nonempty (ComparisonVirtualGapData
        (comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma) a b)) :
    (∀t > 0,d.U.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) ∧
    (∀t > 0,d.V.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) := by
  let A := S^3*(scalarTailSpatialJet hT d.beta 4 0 0)^2
  let B := 2*S^2*(scalarTailSpatialJet hT d.beta 2 0 0)^3
  have hresponse : comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma=
      comparisonGlobalScalarResponse d.U.mass A B d.sigma := rfl
  have hzero : ∀t∈comparisonIncrementSupport d.V.mass,
      comparisonGlobalScalarResponse d.U.mass A B d.sigma t=0 := by
    intro t ht
    rw [←hresponse]
    by_cases htp : 0 < t
    · exact d.support_zero t htp ht
    · have ht0 : t=0 := le_antisymm (not_lt.mp htp)
        (comparison_increment_support_nonnegative d.radius_negative_axis_zero ht)
      simp only [ht0,comparisonLocalScalarLimitResponse,intervalIntegral.integral_same]
  have H := comparison_global_scalar_primitives_rigidity
    d.U.monotone d.V.monotone hUV (fun t _ => d.U.nonneg t) d.radius_negative_axis_zero
    d.positive_coefficients.1 d.positive_coefficients.2 hcl
    (fun t ht => (d.radius_outer_growth hAz hxs t ht).1) hzero
    (fun a b ha hab has hbs hgap _ => by
      rw [←hresponse]
      exact hvirtual a b ha hab has hbs hgap)
  simpa only [d.coefficient_ratio] using H

theorem scalar_primitives_zero_of_linear_profiles
    (d : ActualOriginalQLocalScalarLimitData hT S M htotal)
    (hUlinear : ∀t > 0,d.U.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t)
    (hVlinear : ∀t > 0,d.V.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) :
    d.sigma=0 ∧
      (∀t ≥ 0,comparisonLocalScalarLimitSlope hT S d.beta d.U d.sigma t=0) ∧
      (∀t ≥ 0,comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma t=0) := by
  let A := S^3*(scalarTailSpatialJet hT d.beta 4 0 0)^2
  let B := 2*S^2*(scalarTailSpatialJet hT d.beta 2 0 0)^3
  have hratio : A/B=(S/T)*scalarInitialDensityConstant hT d.beta := d.coefficient_ratio
  have hresponse : comparisonLocalScalarLimitResponse hT S d.beta d.U d.sigma=
      comparisonGlobalScalarResponse d.U.mass A B d.sigma := rfl
  have hzero : ∀t∈comparisonIncrementSupport d.V.mass,
      comparisonGlobalScalarResponse d.U.mass A B d.sigma t=0 := by
    intro t ht
    rw [←hresponse]
    by_cases htp : 0 < t
    · exact d.support_zero t htp ht
    · have ht0 : t=0 := le_antisymm (not_lt.mp htp)
        (comparison_increment_support_nonnegative d.radius_negative_axis_zero ht)
      simp only [ht0,comparisonLocalScalarLimitResponse,intervalIntegral.integral_same]
  have H := comparison_linear_scalar_primitives_zero (A:=A) (B:=B) d.V.monotone
    d.positive_coefficients.1 d.positive_coefficients.2
    (fun t ht => by simpa only [hratio] using hUlinear t ht)
    (fun t ht => by simpa only [hratio] using hVlinear t ht) hzero
  exact H

theorem compact_scalar_zero_limits_of_linear_profiles
    (d : ActualOriginalQLocalScalarLimitData hT S M htotal)
    (hUlinear : ∀t > 0,d.U.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t)
    (hVlinear : ∀t > 0,d.V.mass t=((S/T)*scalarInitialDensityConstant hT d.beta)*t) :
    ∀R : ℝ,0 < R →
      TendstoUniformlyOn (fun n => comparisonLocalScalarSlope hT S
        ((M n).inheritedScalarMassProfileBare hT (htotal n)) (M n).xs)
        (fun _ => 0) atTop (Icc (0 : ℝ) R) ∧
      TendstoUniformlyOn (fun n => comparisonRescaledScalarResponse
        (scalarCovarianceResponse hT ((M n).inheritedScalarMassProfileBare hT (htotal n)))
        S (M n).xs) (fun _ => 0) atTop (Icc (0 : ℝ) R) := by
  have Hzero := d.scalar_primitives_zero_of_linear_profiles hUlinear hVlinear
  intro R hR
  exact ⟨((d.limits R hR).2.1).congr_right (fun t ht => Hzero.2.1 t ht.1),
    ((d.limits R hR).2.2).congr_right (fun t ht => Hzero.2.2 t ht.1)⟩

theorem scalar_radius_laws_ae_eq_of_HIGH_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n:ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u  ≤  T}
    (d : ActualOriginalQLocalScalarLimitData hT T M htotal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1:ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)

    (G : OriginalQComparableBandContext M T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/(M n).xs^2) atTop atTop) :
    d.U.mass=ᵐ[volume] d.V.mass := by
  have hlocal : 0 < T := G.hT
  let gamma:=T/T
  let x:=fun n=>(M n).xs
  let q:=fun n=>actualScalarClockQuantile T (dim n+1) (M n).sweepBf (M n).sweepHf
  have hgamma:0 < gamma:=div_pos hlocal hT
  have hx:∀n,0 < x n:=fun n=>(M n).hxs
  have hxlim:Tendsto x atTop (𝓝 0):=
    G.xs_zero
  have hq:∀n,MonotoneOn (q n) (Icc (0:ℝ) 1):=fun n=>
    actualScalarClockQuantile_monotone hT (dim n+1) (by omega) (M n).sweepBf (M n).sweepHf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone
  have hqb:∀n u,u∈Icc (0:ℝ) 1 → q n u∈Icc (0:ℝ) 1:=fun n=>
    actualScalarClockQuantile_bounds hT (dim n+1) (by omega) (M n).sweepBf (M n).sweepHf
      (M n).inherited_bf_monotone (M n).inherited_hf_monotone
      ((M n).inherited_total_clock_le (htotal n))
  have hU:∀t : ℝ,Tendsto (fun n=>(quantileMassProfile (q n) (hqb n)).val
      (gamma*(x n*t))/x n) atTop (𝓝 (d.U.mass t)):=d.scalar_cdf_limit
  have hlocalLaw:∀R : ℝ,0 < R → ∃v : ℕ → ℝ,
      (∀n,v n∈Icc (0:ℝ) 1) ∧
      (∀ᶠn in atTop,gamma*(x n*R) < q n (v n) ∧ x n*R < (M n).sweepRadius (v n)) ∧
      Tendsto (fun n=>(∫w : ParisiFinite.OrderPoint in {w | (w:ℝ) ≤ v n},
        |q n (w:ℝ)/gamma-(M n).sweepRadius w|∂(uniformOrderMass : Measure ParisiFinite.OrderPoint))/(x n)^2)
        atTop (𝓝 0) := by
    intro R hR
    obtain ⟨C,hC,Hcut,Hcouple⟩:=
      actual_comparable_context_compact_original_scalar_cuts_HIGH_original_q
        hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin
        dim hdim M G hlarge htotal R hR
    let v:=fun n=>min (C*x n) 1
    have hv:∀n,v n∈Icc (0:ℝ) 1:=fun n=>
      ⟨le_min (mul_nonneg hC.le (hx n).le) zero_le_one,min_le_right _ _⟩
    refine ⟨v,hv,?_,?_⟩
    · filter_upwards [Hcut] with n hn
      refine ⟨?_,hn.2⟩
      have hv0:0 < v n:=lt_min (mul_pos hC (hx n)) zero_lt_one
      have H:=mul_lt_mul_of_pos_left hn.1 hgamma
      dsimp only [q]
      rw [actualScalarClockQuantile_on (dim n+1) (M n).sweepBf (M n).sweepHf hv0]
      convert H using 1; dsimp only [gamma,v,x];field_simp [hT.ne',hlocal.ne']
    · have Hroot:=G.total_root_bare_original_q
      apply Hcouple.congr'
      filter_upwards [Hroot] with n hn
      congr 1
      apply integral_congr_ae
      exact Eventually.of_forall fun w=>by
        dsimp only [q,gamma]
        rw [div_self hT.ne',div_one,
          (M n).inherited_local_temperature_scalar_quantile_eq_mixed_of_root T hn.2 w.property.1]
  exact comparison_shifted_local_temperature_scalar_radius_laws_ae_identified
    (ActualThetaZeroOverlapMinimum.originalQShiftedInverseSequence M) q gamma x d.U.mass d.V.mass hgamma
    (fun n=>(M n).data.hrbounds.1.le) hq hqb hx d.V.monotone
    d.omitted_small hU d.radius_inverse_cdf_limit hlocalLaw

theorem global_profile_rigidity_of_HIGH_comparable_context
    {m delta cl cu Az C0 Ct D Bclock T c0 : ℝ} {hT : 0 < T}
    {dim : ℕ → ℕ}
    {M : (n : ℕ) → ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0 : ℝ) 1,(M n).h u+(M n).b u ≤ T}
    (d : ActualOriginalQLocalScalarLimitData hT T M htotal)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc0 : 0 < c0) (hc01 : c0 ≤ 1)
    (hmargin : delta/4 < 3*m-99*delta) (hcapmargin : 100*delta < (1 : ℝ)/3+m)
    (hgapmargin : 0 < 9*m-298*delta) (hdim : Tendsto dim atTop atTop)

    (G : OriginalQComparableBandContext M T)
    (hlarge : Tendsto (fun n=>laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs/(M n).xs^2) atTop atTop)
    (hvirtual : ∀a b,0 ≤ a → a < b →
      a∈comparisonIncrementSupport d.V.mass → b∈comparisonIncrementSupport d.V.mass →
      (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass) →
      Nonempty (ComparisonVirtualGapData
        (comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma) a b)) :
    (∀t > 0,d.U.mass t=((T/T)*scalarInitialDensityConstant hT d.beta)*t) ∧
    (∀t > 0,d.V.mass t=((T/T)*scalarInitialDensityConstant hT d.beta)*t) := by
  have hlocal : 0 < T := G.hT
  have hUV := d.scalar_radius_laws_ae_eq_of_HIGH_comparable_context
    hm hdelta hroom hcl hcu hAz hC0 hCt hc0 hc01 hmargin hcapmargin hgapmargin hdim
    G hlarge
  have hxs : Tendsto (fun n => (M n).xs) atTop (𝓝 0) :=
    G.xs_zero
  exact d.global_profile_rigidity_of_coupled_laws hUV hcl hAz hxs hvirtual

theorem original_radius_locally_uniform_of_comparable_linear_profile
    {m delta cl cu Az C0 Ct D Bclock T S : ℝ} {hT : 0 < T}
    {dim : ℕ→ℕ}
    {M : (n:ℕ)→ActualThetaZeroOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {htotal : ∀n,∀u∈Icc (0:ℝ) 1,(M n).h u+(M n).b u ≤ T}
    (d : ActualOriginalQLocalScalarLimitData hT S M htotal)
    {kappa : ℝ} (hcl : 0 < cl) (hkappa : cl ≤ kappa)
    (G : OriginalQComparableBandContext M T)
    (hlinear : ∀t > 0,d.V.mass t=kappa*t) :
    TendstoLocallyUniformlyOn (fun n v=>(M n).sweepRadius ((M n).xs*v)/(M n).xs)
      (fun v=>v/kappa) atTop (Ioi (0:ℝ)) := by
  exact (ActualThetaZeroOverlapMinimum.originalQShiftedInverseSequence M).rescaled_inverse_locally_uniform
    (fun n=>(M n).xs) (hcl.trans_le hkappa) (fun n=>(M n).hxs) G.xs_zero
    d.omitted_small (fun t ht=>by simpa only [ActualThetaZeroOverlapMinimum.originalQShiftedInverseSequence,hlinear t ht] using d.radius_inverse_cdf_limit t)

end ActualOriginalQLocalScalarLimitData
end OAI.SKFluctuations.LaplaceWindowFormalization
