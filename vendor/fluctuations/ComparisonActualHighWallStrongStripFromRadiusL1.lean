module

public import ComparisonActualHighWallConditionalStrictStrip
public import ComparisonCriticalPositiveWallVirtualGapFromRadiusL1

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal
set_option maxHeartbeats 18000000

theorem eventually_actual_high_wall_strict_strip_of_physical_radius_L1
    {m delta cl cu Az C0 Ct D Bclock T : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hmargin : 2*delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hD : 0 < D) (hT : 0 < T)
    (hclSlack : cl < 2*T*Real.exp (-12*T))
    (hcuSlack :
      T*(ReplicaTree.attachmentCount 1 3 : ℝ)^2/(2*Real.exp (-12*T)) < cu)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (hfixed : ∀n,(M n).xs=(M n).data.d)
    (hTeq : ∀n,(M n).data.T=T)
    (hx : Tendsto (fun n=>(M n).xs) atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/(M n).xs) atTop (𝓝 0))
    (htotal : ∀n,∀u∈Icc (0:ℝ) 1,((M n).hf u:ℝ)+((M n).bf u:ℝ)≤T)
    (d : ActualHighWallLocalScalarLimitData hT T M htotal)
    (hUV : d.U.mass =ᵐ[volume] d.V.mass)
    (s : NonnegativeMassProfile)
    (hspin : ∀r,Tendsto (fun n=>(M n).actualScaledRadiusSpin r)
      atTop (𝓝 (s.mass r)))
    (hRadiusL1 : ∀a b,0≤a→a<b→
      a∈comparisonIncrementSupport d.V.mass→
      b∈comparisonIncrementSupport d.V.mass→
      (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass)→
      ∀u∈Ioo a b,∀v∈Ioo a b,u<v→
        Tendsto (fun n=>(∫r in Ioo ((M n).xs*u) ((M n).xs*v),
          |(M n).radiusS r-scalarCovarianceResponse hT
            ((M n).inheritedScalarMassProfile hT (htotal n))
            (actualMixedClock (dim n+1) (M n).bf (M n).hf
              ((M n).alpha.val.val r))|)/(M n).xs^4) atTop (𝓝 0))
    {K : ℝ} (hK : 1≤K) :
    ∀ᶠn in atTop,∀r∈Icc (M n).data.d (K*(M n).data.d),
      cl*r<(M n).alpha.val.val r ∧ (M n).alpha.val.val r<cu*r := by
  let g := comparisonLocalScalarLimitResponse hT T d.beta d.U d.sigma
  let alpha : ℕ→boundedMassProfiles :=
    fun n=>(M n).inheritedScalarMassProfile hT (htotal n)
  have hG : ∀Q>0,TendstoUniformlyOn
      (fun n=>comparisonRescaledScalarResponse
        (scalarCovarianceResponse hT (alpha n)) T (M n).xs)
      g atTop (Icc (0:ℝ) Q) := by
    intro Q hQ
    exact (d.limits Q hQ).2.2
  have hgc : ∀Q>0,ContinuousOn g (Icc (0:ℝ) Q) := by
    intro Q hQ
    have Hi : IntegrableOn
        (comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma)
        (uIcc (0:ℝ) Q) := by
      simpa only [uIcc_of_le hQ.le] using (d.limits Q hQ).1.integrableOn_Icc
    change ContinuousOn (fun r=>∫t in 0..r,
      comparisonLocalScalarLimitSlope hT T d.beta d.U d.sigma t) (Icc (0:ℝ) Q)
    simpa only [uIcc_of_le hQ.le] using
      intervalIntegral.continuousOn_primitive_interval Hi
  have hvirtual : ∀a b,0≤a→a<b→
      a∈comparisonIncrementSupport d.V.mass→
      b∈comparisonIncrementSupport d.V.mass→
      (∀r∈Ioo a b,r∉comparisonIncrementSupport d.V.mass)→
      Nonempty (ComparisonVirtualGapData g a b) := by
    intro a b ha hab has hbs hgap
    exact critical_positive_wall_virtual_gap_of_physical_radius_L1
      hm hdelta hmargin hcl hcu hAz hC0 hCt hD hT hT
      dim hdim M hfixed hTeq hx hsRatio alpha d.V
      d.radius_negative_axis_zero d.radius_inverse_cdf_limit
      d.radius_cdf_limit s hspin g hG hgc
      ha hab has hbs hgap (hRadiusL1 a b ha hab has hbs hgap)
  have Hprofile := d.complete_direct_profile_of_coupled_laws
    hUV hcl hx hvirtual
  dsimp only at Hprofile
  obtain ⟨_,hVlinear,_,_,hkLow,hkUp,_,_,_,_,_⟩ := Hprofile
  have hclK : cl < scalarInitialDensityConstant hT d.beta :=
    hclSlack.trans_le hkLow
  have hKcu : scalarInitialDensityConstant hT d.beta < cu :=
    hkUp.trans_lt hcuSlack
  have Hstrip := d.eventually_original_inverse_strict_on_fixed_strip
    hcl hclK hKcu hVlinear hK
  filter_upwards [Hstrip] with n hn r hr
  rw [←hfixed n] at hr
  exact hn r hr

end OAI.SKFluctuations.LaplaceWindowFormalization
