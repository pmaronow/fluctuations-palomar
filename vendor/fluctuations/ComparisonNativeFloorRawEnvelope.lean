module

public import ComparisonNativeFloorRestoration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6400000
attribute [local instance] Classical.propDecidable

theorem actual_comparison_floor_error_of_ae_raw
    (m : NativeBandModel) (F : Set ℝ) (hF : MeasurableSet F) {A K : ℝ}
    (hA : 0≤A) (hK : 0≤K)
    (hfloor : ∀ᵐ r,r  ∈  Icc (0:ℝ) 1  →  r  ∈  F  →  
      deriv m.alpha.val.val r=comparisonFloor m.N m.delta m.U r)
    (hraw : ∀ᵐ r,r  ∈  Icc (0:ℝ) 1 → r  ∈  F  →  
      orderedPathB (m.n+1) m.bf m.hf (m.alpha.val.val r)≤K*(A+r)^2) :
    (∫u in 0..1,F.indicator (fun _=>(1:ℝ)) (m.R u)*m.comparisonErrorDensity u) ≤
      (K+1)*(2*m.lam*A^2*m.N^(-m.delta)*m.U+
        4*m.d^3*Real.log m.N*m.N^m.delta*m.U^2*
          Real.log ((1+m.N^(2*m.delta)*m.U)/(m.N^(2*m.delta)*m.U))) := by
  have hmom := comparisonVariableEndpoint_radius_moments m.hc m.hk m.hkc m.hm m.hM
    (m.n+1) (by omega) m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hNp : 0< m.N := zero_lt_one.trans_le m.hN
  have hk := comparisonFloor_continuousOn (δ:=m.delta) hNp m.hU (show (0:ℝ)≤0 by rfl)
  have he : ContinuousOn (laplaceComparisonStrength m.d m.lam) (Icc (0:ℝ) 1) :=
    (laplaceComparisonStrength_contDiff m.d m.lam).continuous.continuousOn
  have hright : IntegrableOn (fun r=>(K+1)*(comparisonFloor m.N m.delta m.U r*
      laplaceComparisonStrength m.d m.lam r*(A+r)^2)) (Icc (0:ℝ) 1) :=
    (((hk.mul he).mul (((continuousOn_const (c:=A)).add continuousOn_id).pow 2)).const_mul (K+1)).integrableOn_Icc
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc,
    comparison_mass_radius_integral m.hc m.hk m.hkc m.hm m.hM m.alpha]
  have hle := integral_mono_of_nonneg
    (f:=fun r=>deriv m.alpha.val.val r*
      (F.indicator (fun _=>(1:ℝ)) (m.R (m.alpha.val.val r))*m.comparisonErrorDensity (m.alpha.val.val r)))
    (g:=fun r=>(K+1)*(comparisonFloor m.N m.delta m.U r*
      laplaceComparisonStrength m.d m.lam r*(A+r)^2)) (by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hmomr := hmom.2.2 r hr
    have hdens := m.alpha.val.property.2.deriv_nonneg (x:=r)
    simp only [NativeBandModel.comparisonErrorDensity,comparisonSweepQuantile_inverse m.hc m.hk m.hkc m.hm m.hM m.alpha hr]
    apply mul_nonneg hdens
    apply mul_nonneg (indicator_nonneg (fun _ _=>zero_le_one) _)
    apply mul_nonneg (laplaceComparisonStrength_pos m.d m.hlam r).le
    change 0≤orderedPathB (m.n+1) m.bf m.hf (m.alpha.val.val r)-
      (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r))^2+
      (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r)^2
    nlinarith [hmomr.2.1,sq_nonneg (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r)]) hright (by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hfloor,ae_restrict_of_ae hraw] with r hr hf hrawr
    have hmomr := hmom.2.2 r hr
    simp only [NativeBandModel.comparisonErrorDensity,comparisonSweepQuantile_inverse m.hc m.hk m.hkc m.hm m.hM m.alpha hr]
    by_cases hrF : r  ∈  F
    · rw [indicator_of_mem hrF,one_mul,hf hr hrF]
      have hquad : m.thermal (m.alpha.val.val r)+
          (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r)^2≤(K+1)*(A+r)^2 := by
        dsimp [NativeBandModel.thermal]
        have hS : 0≤orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r) := hmomr.1.1
        nlinarith [hrawr hr hrF,mul_nonneg hS hr.1,mul_nonneg hA hr.1,sq_nonneg A]
      have hmul := mul_le_mul_of_nonneg_left hquad
        (mul_nonneg (comparisonFloor_pos (δ:=m.delta) hNp m.hU hr.1).le (laplaceComparisonStrength_pos m.d m.hlam r).le)
      nlinarith
    · rw [indicator_of_notMem hrF,zero_mul,mul_zero]
      exact mul_nonneg (by linarith : 0≤K+1)
        (mul_nonneg (mul_nonneg (comparisonFloor_pos (δ:=m.delta) hNp m.hU hr.1).le
          (laplaceComparisonStrength_pos m.d m.hlam r).le) (sq_nonneg _)))
  have hbound := mul_le_mul_of_nonneg_left
    (comparison_floor_quadratic_weight (A:=A) (delta:=m.delta) m.hN m.hlog m.hU m.hd m.hnd m.hlam m.hld)
    (show 0≤K+1 by linarith)
  rw [integral_const_mul] at hle
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc] at hbound
  exact hle.trans hbound

theorem actual_comparison_floor_error_of_normalized_B
    (m : NativeBandModel) (F : Set ℝ) (hF : MeasurableSet F) {A K C : ℝ}
    (hA : 0≤A) (hK : 0≤K) (hC : 0≤C)
    (hfloor : ∀ᵐ r,r ∈ Icc (0:ℝ) 1 → r ∈ F → deriv m.alpha.val.val r=comparisonFloor m.N m.delta m.U r)
    (hB : ∀u ∈ Ioc (0:ℝ) 1,orderedPathB (m.n+1) m.bf m.hf u≤K*(m.xs+u)^2)
    (hscale : ∀r ∈ Icc (0:ℝ) 1,r ∈ F → m.xs+m.alpha.val.val r≤C*(A+r)) :
    (∫u in 0..1,F.indicator (fun _=>(1:ℝ)) (m.R u)*m.comparisonErrorDensity u)≤
      (K*C^2+1)*(2*m.lam*A^2*m.N^(-m.delta)*m.U+
        4*m.d^3*Real.log m.N*m.N^m.delta*m.U^2*
          Real.log ((1+m.N^(2*m.delta)*m.U)/(m.N^(2*m.delta)*m.U))) := by
  apply actual_comparison_floor_error_of_ae_raw m F hF hA (mul_nonneg hK (sq_nonneg C)) hfloor
  filter_upwards [volume.ae_ne (0:ℝ)] with r hr0 hr hrF
  have hrp : 0<r := lt_of_le_of_ne hr.1 hr0.symm
  have hαp : 0 < m.alpha.val.val r := by
    have hh := inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property
      (show (0:ℝ) ∈ Icc (0:ℝ) 1 by simp) hr hrp
    simpa only [m.alpha.property.1] using hh
  have hα1 := (m.alpha.val.property.1 r).2
  have hh := hB _ ⟨hαp,hα1⟩
  have hs := pow_le_pow_left₀ (add_nonneg m.hxs.le hαp.le) (hscale r hr hrF) 2
  have ht := mul_le_mul_of_nonneg_left hs hK
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
