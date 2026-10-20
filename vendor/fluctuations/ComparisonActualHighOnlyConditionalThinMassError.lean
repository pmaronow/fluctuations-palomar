module

public import ComparisonActualHighOnlyConditionalErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 12000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum

theorem eventually_actual_conditional_thin_mass_error_high_only
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∀ᶠn:ℕ in atTop,∀a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.d≤1 → a.data.s≤1/4 → a.data.s≤a.xs →
      a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      ∀lo hi:ℝ,lo∈Icc (0:ℝ) 1 → hi∈Icc (0:ℝ) 1 → lo ≤ hi →
      hi-lo ≤ a.data.U → hi ≤ 2*a.xs →
      (∫u in lo..hi,a.comparisonErrorDensity u) ≤ a.data.N^(3*delta)*a.data.E := by
  obtain ⟨K,hK,HB⟩:=eventually_actual_high_only_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=Az+1/cl
  let A:=(3:ℝ)^2*(K+C^2)
  have hA:0≤A:=by dsimp [A];positivity
  have hsR:Tendsto (fun n:ℕ=>((n+1:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hcost:=hsR.eventually (comparison_log_loss_eventually (C:=A) (p:=0) hA hdelta)
  filter_upwards [(tendsto_add_atTop_nat 1).eventually HB,Hcost,
    eventually_actual_minimum_physical_scalar_data_high_only hm hC0] with n hnB hnCost hnScalar
  intro a hd1 hs hsxs hxs lo hi hlo hhi hlh hwidth hupper
  have hxs0:=a.hxs
  have hU0:=a.data.hU
  have hE0:=a.data.hE
  have hlam0:=a.hlam
  have hN0:=a.data.hN
  have hscalar:=hnScalar a hd1
  have HI:Icc lo hi⊆Icc (0:ℝ) 1:=Icc_subset_Icc hlo.1 hhi.2
  have hiE:=a.comparisonErrorDensity_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hlh,uIcc_of_le zero_le_one];exact HI)
  have Hpoint:∀ᵐu∂volume.restrict (Icc lo hi),
      a.comparisonErrorDensity u≤a.lam*(K+C^2)*(3*a.xs)^2:=by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae (volume.ae_ne (0:ℝ))]
      with u hu hu0
    have hup:u∈Ioc (0:ℝ) 1:=⟨lt_of_le_of_ne (HI hu).1 hu0.symm,(HI hu).2⟩
    have HB':=hnB a hs hsxs u hup
    have HR:=a.inverse_radius_le_source_mass hcl hAz (Ioc_subset_Icc_self hup)
    have hR0:0≤a.R u:=(a.shiftedNativeModel.R_bounds _).1
    have HS:0≤orderedPathS (n+1) a.bf a.hf u:=(a.mass_mean_unit_bounds (Ioc_subset_Icc_self hup)).1
    have hR2:(a.R u)^2≤C^2*(a.xs+u)^2:=by
      have H:=pow_le_pow_left₀ hR0 HR 2
      dsimp only [C] at *
      nlinarith only [H]
    have hquadratic:(orderedPathB (n+1) a.bf a.hf u-(orderedPathS (n+1) a.bf a.hf u)^2)+
        (orderedPathS (n+1) a.bf a.hf u-a.R u)^2≤(K+C^2)*(a.xs+u)^2:=by
      nlinarith only [HB',hR2,mul_nonneg HS hR0]
    have hupper':a.xs+u ≤ 2*a.xs+a.xs:=by linarith only [hu.2,hupper]
    have hupper':a.xs+u ≤ 3*a.xs:=by linarith only [hupper']
    have hsq: (a.xs+u)^2≤(3*a.xs)^2:=
      pow_le_pow_left₀ (add_nonneg a.hxs.le (HI hu).1) hupper' 2
    have H1:=mul_le_mul_of_nonneg_left hquadratic (a.coefficient_nonneg u)
    have H2:=mul_le_mul_of_nonneg_right (a.coefficient_le_lam u)
      (show 0≤(K+C^2)*(a.xs+u)^2 by positivity)
    have H3:=mul_le_mul_of_nonneg_left hsq (show 0≤a.lam*(K+C^2) by positivity)
    change a.comparisonErrorDensity u≤_ at H1
    nlinarith only [H1,H2,H3]
  have H:=intervalIntegral.integral_mono_ae_restrict hlh hiE intervalIntegrable_const Hpoint
  rw [intervalIntegral.integral_const] at H
  simp only [smul_eq_mul] at H
  have Hv:=mul_le_mul_of_nonneg_right hwidth
    (show 0≤a.lam*(K+C^2)*(3*a.xs)^2 by positivity)
  have Hbound:(∫u in lo..hi,a.comparisonErrorDensity u)≤A*(a.lam*a.xs^2*a.data.U):=by
    dsimp only [A] at *
    nlinarith only [H,Hv]
  have hcal:a.lam*a.xs^2*a.data.U=a.data.N^(2*delta)*a.data.E:=by
    rw [hxs,comparison_conditional_scale_square a.data.hN a.hlam]
    unfold ActualHighOnlyComparisonData.U comparisonSmallMass
    field_simp
  rw [hcal] at Hbound
  simp only [Real.rpow_zero,mul_one] at hnCost
  have Hcost':=mul_le_mul_of_nonneg_right hnCost
    (show 0≤a.data.N^(2*delta)*a.data.E by positivity)
  have he:a.data.N^delta*(a.data.N^(2*delta)*a.data.E)=a.data.N^(3*delta)*a.data.E:=by
    rw [←mul_assoc,←Real.rpow_add a.data.hN];congr 2;ring
  rw [he] at Hcost'
  exact Hbound.trans Hcost'

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
