module

public import ComparisonNativeFullBandConstruction
public import ComparisonRadiusSizeRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

theorem laplaceComparisonStrength_radius_upper
    {N d lam r : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N)
    (hd : 0<d) (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (hr : r ∈ Icc (0:ℝ) 1) :
    laplaceComparisonStrength d lam r*r ≤ 2*d^3*Real.log N := by
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hdp : 0<d^3 := pow_pos hd 3
  have hNd : 1≤N*d := by simpa only [mul_comm] using (div_le_iff₀ hNp).mp hnd
  have htN : lam*r/d^3≤N := by
    apply (div_le_iff₀ hdp).mpr
    have h1 := mul_le_mul_of_nonneg_left hr.2 hlam.le
    have h2 := mul_le_mul_of_nonneg_left hNd (sq_nonneg d)
    nlinarith
  unfold laplaceComparisonStrength comparisonStrength laplaceComparisonShape
  split_ifs with ht
  · have hh := (div_le_iff₀ hdp).mp ht
    have hl := mul_le_mul_of_nonneg_left hlog hdp.le
    simp only [mul_one]
    nlinarith
  · have htp : 0<lam*r/d^3 := zero_lt_one.trans (lt_of_not_ge ht)
    have hrp : 0<r := by
      by_contra hh
      have hh1 := div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hlam.le (le_of_not_gt hh)) hdp.le
      linarith
    have hlt := Real.log_le_log htp htN
    have he : lam*((1+Real.log (lam*r/d^3))/(lam*r/d^3))*r=
        d^3*(1+Real.log (lam*r/d^3)) := by
      field_simp [hrp.ne',hlam.ne',hd.ne']
    rw [he]
    have hs := mul_le_mul_of_nonneg_left (show 1+Real.log (lam*r/d^3)≤2*Real.log N by linarith) hdp.le
    nlinarith

theorem comparison_floor_first_moment
    {N delta U : ℝ} (hN : 0<N) (hU : 0<U) :
    (∫r in 0..1,comparisonFloor N delta U r*r) ≤
      N^delta*U^2*Real.log ((1+N^(2*delta)*U)/(N^(2*delta)*U)) := by
  let s := N^(2*delta)*U
  have hs : 0<s := by dsimp [s];positivity
  have hk := comparisonFloor_continuousOn (δ:=delta) hN hU (show (0:ℝ)≤0 by rfl)
  have hc : ContinuousOn (fun r:ℝ=>N^delta*U^2/(r+s)) (Icc 0 1) :=
    continuousOn_const.div (continuousOn_id.add continuousOn_const) (fun r hr=>ne_of_gt (by linarith [hr.1]))
  have hh := intervalIntegral.integral_mono_on zero_le_one
    ((hk.mul continuousOn_id).intervalIntegrable_of_Icc (μ:=volume) zero_le_one)
    (hc.intervalIntegrable_of_Icc (μ:=volume) zero_le_one) (fun r hr=>by
      have hden : 0<r+s := by linarith [hr.1]
      have hratio : r/(r+s)≤1 := (div_le_iff₀ hden).mpr (by linarith)
      have hmul := mul_le_mul_of_nonneg_left hratio (show 0≤N^delta*U^2/(r+s) by positivity)
      have he : comparisonFloor N delta U r*r=(N^delta*U^2/(r+s))*(r/(r+s)) := by
        change (N^delta*U^2)/(r+s)^2*r=_
        field_simp [hden.ne']
        <;> ring
      change comparisonFloor N delta U r*r≤N^delta*U^2/(r+s)
      rw [he]
      simpa only [mul_one] using hmul)
  have he : (∫r in 0..1,N^delta*U^2/(r+s))=
      N^delta*U^2*Real.log ((1+s)/s) := by
    rw [show (fun r:ℝ=>N^delta*U^2/(r+s))=(fun r=>N^delta*U^2*(1/(r+s))) by funext r;ring,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_add_right (f:=fun r:ℝ=>1/r),zero_add,
      integral_one_div_of_pos hs (by linarith : 0<1+s)]
  exact hh.trans_eq he

theorem comparison_floor_quadratic_weight
    {N delta U d lam A : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N)
    (hU : 0<U) (hd : 0<d) (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2) :
    (∫r in 0..1,comparisonFloor N delta U r*laplaceComparisonStrength d lam r*(A+r)^2) ≤
      2*lam*A^2*N^(-delta)*U+
        4*d^3*Real.log N*N^delta*U^2*Real.log ((1+N^(2*delta)*U)/(N^(2*delta)*U)) := by
  have hNp : 0<N := zero_lt_one.trans_le hN
  have hk := comparisonFloor_continuousOn (δ:=delta) hNp hU (show (0:ℝ)≤0 by rfl)
  have he : ContinuousOn (laplaceComparisonStrength d lam) (Icc (0:ℝ) 1) :=
    (laplaceComparisonStrength_contDiff d lam).continuous.continuousOn
  have hleft : IntervalIntegrable (fun r=>comparisonFloor N delta U r*laplaceComparisonStrength d lam r*(A+r)^2) volume 0 1 :=
    ((hk.mul he).mul (((continuousOn_const (c:=A)).add continuousOn_id).pow 2)).intervalIntegrable_of_Icc (μ:=volume) zero_le_one
  have hi1 : IntervalIntegrable (fun r=>2*lam*A^2*comparisonFloor N delta U r) volume 0 1 :=
    (hk.const_mul _).intervalIntegrable_of_Icc (μ:=volume) zero_le_one
  have hi2 : IntervalIntegrable (fun r=>4*d^3*Real.log N*(comparisonFloor N delta U r*r)) volume 0 1 :=
    ((hk.mul continuousOn_id).const_mul _).intervalIntegrable_of_Icc (μ:=volume) zero_le_one
  have hright : IntervalIntegrable (fun r=>2*lam*A^2*comparisonFloor N delta U r+4*d^3*Real.log N*(comparisonFloor N delta U r*r)) volume 0 1 := hi1.add hi2
  have hh := intervalIntegral.integral_mono_on zero_le_one hleft hright (fun r hr=>by
    have hkp := (comparisonFloor_pos (δ:=delta) hNp hU hr.1).le
    have hep := (laplaceComparisonStrength_pos d hlam r).le
    have hel := laplaceComparisonStrength_le d hlam.le r
    have her := laplaceComparisonStrength_radius_upper hN hlog hd hnd hlam hld hr
    have hs : (A+r)^2≤2*A^2+2*r^2 := by nlinarith [sq_nonneg (A-r)]
    have h1 := mul_le_mul_of_nonneg_left hs (mul_nonneg hkp hep)
    have h2 := mul_le_mul_of_nonneg_right hel (mul_nonneg hkp (sq_nonneg A))
    have h3 := mul_le_mul_of_nonneg_right her (mul_nonneg hkp hr.1)
    nlinarith)
  rw [intervalIntegral.integral_add hi1 hi2,
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hh
  have hmass := mul_le_mul_of_nonneg_left (comparisonFloor_total_mass (δ:=delta) hNp hU)
    (show 0≤2*lam*A^2 by positivity)
  have hfirst := mul_le_mul_of_nonneg_left (comparison_floor_first_moment (delta:=delta) hNp hU)
    (show 0≤4*d^3*Real.log N by positivity)
  nlinarith

namespace NativeBandModel

def comparisonErrorDensity (m : NativeBandModel) (u : ℝ) : ℝ :=
  laplaceComparisonStrength m.d m.lam (m.R u)*
    (m.thermal u+(orderedPathS (m.n+1) m.bf m.hf u-m.R u)^2)

end NativeBandModel

theorem actual_comparison_floor_error
    (m : NativeBandModel) (F : Set ℝ) (hF : MeasurableSet F) {A K : ℝ}
    (hA : 0≤A) (hK : 0≤K)
    (hfloor : ∀ᵐ r,r ∈ Icc (0:ℝ) 1 → r ∈ F → 
      deriv m.alpha.val.val r=comparisonFloor m.N m.delta m.U r)
    (hraw : ∀r ∈ Icc (0:ℝ) 1,r ∈ F → 
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
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hfloor] with r hr hf
    have hmomr := hmom.2.2 r hr
    simp only [NativeBandModel.comparisonErrorDensity,comparisonSweepQuantile_inverse m.hc m.hk m.hkc m.hm m.hM m.alpha hr]
    by_cases hrF : r ∈ F
    · rw [indicator_of_mem hrF,one_mul,hf hr hrF]
      have hquad : m.thermal (m.alpha.val.val r)+
          (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r)^2≤(K+1)*(A+r)^2 := by
        dsimp [NativeBandModel.thermal]
        have hS : 0≤orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r) := hmomr.1.1
        nlinarith [hraw r hr hrF,mul_nonneg hS hr.1,mul_nonneg hA hr.1,sq_nonneg A]
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

end OAI.SKFluctuations.LaplaceWindowFormalization
