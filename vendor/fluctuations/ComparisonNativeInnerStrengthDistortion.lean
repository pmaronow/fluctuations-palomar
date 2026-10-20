module

public import ComparisonNativeInnerError

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

theorem comparison_inner_ledger_with_strength_distortion {l : ℕ} (hl : 2<l)
    {N delta E lam P v y D Q C J L T eps K : ℝ}
    (hN : 1 ≤ N) (hE : 0<E) (hlam : 0<lam) (hP : 0<P)
    (hK : 1  ≤  K) (hstrength : N*(N^(-delta)*lam)  ≤  K*P)
    (hv : comparisonSmallMass N E ≤ v)
    (hvA : v ≤ C*comparisonConditionalScale N delta E lam)
    (hy : 0<y) (hyA : y ≤ C*comparisonConditionalScale N delta E lam)
    (hD : 0<D) (hQ : 1 ≤ Q) (hC : 0 ≤ C) (hJ : 0 ≤ J)
    (hL : 0 ≤ L) (hLU : L ≤ comparisonSmallMass N E)
    (hUA : comparisonSmallMass N E ≤ comparisonConditionalScale N delta E lam)
    (hDJ : D ≤ J*L) (hratio : y/D ≤ N^T) (horder : T/((l:ℝ)-1) ≤ eps) :
    lam*v*(2*((Q^2*y)/(P*v^2))^((2:ℝ)/3)+3/(P*v^2)+D^2+
      comparisonReverseMoment l D Q y) ≤ K*comparisonInnerPhysicalCore N delta E Q C J eps := by
  have hNp : 0 < N := zero_lt_one.trans_le hN
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hvp : 0 < v := (comparisonSmallMass_pos hNp hE).trans_le hv
  have hbase := comparison_inner_ledger_physical_cost hl hN hE hlam (mul_pos hKp hP)
    hstrength hv hvA hy hyA hD hQ hC hJ hL hLU hUA hDJ hratio horder
  have hopt : ((Q^2*y)/(P*v^2))^((2:ℝ)/3)  ≤  K*((Q^2*y)/((K*P)*v^2))^((2:ℝ)/3) := by
    have he : (Q^2*y)/(P*v^2)=K*((Q^2*y)/((K*P)*v^2)) := by field_simp
    rw [he,Real.mul_rpow hKp.le (show 0  ≤  (Q^2*y)/((K*P)*v^2) by positivity)]
    have hp : K^((2:ℝ)/3)  ≤  K := by
      simpa using Real.rpow_le_rpow_of_exponent_le hK (show (2:ℝ)/3  ≤  1 by norm_num)
    exact mul_le_mul_of_nonneg_right hp (by positivity)
  have hinv : 3/(P*v^2)=K*(3/((K*P)*v^2)) := by field_simp
  have hrest : 0  ≤  D^2+comparisonReverseMoment l D Q y := by
    unfold comparisonReverseMoment
    positivity
  have hr := mul_le_mul_of_nonneg_right hK hrest
  have hh : 2*((Q^2*y)/(P*v^2))^((2:ℝ)/3)+3/(P*v^2)+D^2+comparisonReverseMoment l D Q y  ≤ 
      K*(2*((Q^2*y)/((K*P)*v^2))^((2:ℝ)/3)+3/((K*P)*v^2)+D^2+comparisonReverseMoment l D Q y) := by
    rw [hinv]
    nlinarith
  have ht := mul_le_mul_of_nonneg_left hh (mul_pos hlam hvp).le
  have hb := mul_le_mul_of_nonneg_left hbase hKp.le
  nlinarith

theorem actual_native_inner_ordinary_error_with_strength_distortion
    (m : NativeBandModel) {cut C eps K : ℝ} (hcut : 0 < cut)
    (hleft : m.cutRadius  ≤   m.ag) (hupper : m.xs+m.alpha.val.val m.zg  ≤   m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag  ≤   m.bandMass)
    (hlog : Real.log (1/cut)  ≤   m.Lside) (hraw : NativeBandRawMaster m)
    (hUeq : m.U=comparisonSmallMass m.N m.E) (hU1 : m.U  ≤  1)
    (hLU : m.Lcap  ≤   m.U) (hLlower : m.N^(-(1:ℝ))  ≤   m.Lcap)
    (hUA : m.U  ≤  comparisonConditionalScale m.N m.delta m.E m.lam)
    (hvU : m.U  ≤   m.bandMass) (hC : 0  ≤  C)
    (hvA : m.bandMass  ≤  C*comparisonConditionalScale m.N m.delta m.E m.lam)
    (hyA : m.y  ≤  C*comparisonConditionalScale m.N m.delta m.E m.lam)
    (hyN : m.y  ≤   m.N) (hK : 1  ≤  K) (hstrength : m.N*(m.N^(-m.delta)*m.lam)  ≤  K*m.P)
    (horder : (m.delta+2)/((m.l:ℝ)-1)  ≤  eps) :
    (∫u in 0..1,m.ordinaryMask (m.R u)*m.comparisonErrorDensity u)  ≤  
      3*nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*K*
        comparisonInnerPhysicalCore m.N m.delta m.E m.Q C m.capLogFactor eps+
      16*m.capLogFactor^2*C*m.N^(2*m.delta)*m.E+
      54*m.lam*(((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*cut := by
  have hthermal : (∫u in 0..1,m.ordinaryMask (m.R u)*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u)  ≤ 
      nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*K*
        comparisonInnerPhysicalCore m.N m.delta m.E m.Q C m.capLogFactor eps+
      18*m.lam*(((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*cut := by
    have hweighted := native_actual_weighted_thermal_le m _ m.ordinaryMask_composed_measurable
      (fun u _=>by unfold NativeBandModel.ordinaryMask;by_cases h:m.R u ∈ m.ordinarySupport <;> simp [h])
    have hb := actual_master_full_ordinary_band_explicit m hcut hleft hupper hband hlog hraw
    have hratio := comparison_physical_reverse_ratio (delta:=m.delta) m.hN m.hlog m.hU hU1 hLlower m.hy.le hyN
    have hc := comparison_inner_ledger_with_strength_distortion m.hl m.hN m.hE m.hlam m.P_pos hK hstrength
      (hUeq ▸ hvU) hvA m.hy hyA m.D0_pos m.hQ hC m.capLogFactor_nonneg m.hLcap.le
      (hUeq ▸ hLU) (hUeq ▸ hUA) m.D0_eq_capLogFactor.le hratio horder
    change m.lam*m.bandMass*(2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
      3/(m.P*m.bandMass^2)+m.D0^2+m.reverse m.D0)  ≤  _ at hc
    have hF : 0  ≤  nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho := by
      unfold nativeBinScaleLoss
      have hL:=m.hLside;have hAS:=m.AS_nonneg;have hAC:=m.AC_nonneg
      have hv:=m.hbandMass;have hr:=m.rho_pos
      positivity
    have h1 := mul_le_mul_of_nonneg_left hb m.hlam.le
    have h2 := mul_le_mul_of_nonneg_left hc hF
    nlinarith
  have herror := actual_native_ordinary_error_le_thermal m hband
  have hNp : 0  <  m.N := zero_lt_one.trans_le m.hN
  have hlen := comparison_conditional_inner_length_cost hNp m.hE m.hlam hC m.hbandMass.le hvA
    m.hLcap.le (hUeq ▸ hLU)
  have hLA : m.Lcap  ≤  comparisonConditionalScale m.N m.delta m.E m.lam := hLU.trans hUA
  have hs := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLA m.hLcap.le) (sq_nonneg m.capLogFactor)
  have hD : m.D0^2  ≤  m.capLogFactor^2*comparisonConditionalScale m.N m.delta m.E m.lam*m.Lcap := by
    rw [m.D0_eq_capLogFactor]
    nlinarith
  have hsquare : m.lam*m.bandMass*m.D0^2  ≤  m.capLogFactor^2*C*m.N^(2*m.delta)*m.E := by
    have h1 := mul_le_mul_of_nonneg_left hD (mul_pos m.hlam m.hbandMass).le
    have h2 := mul_le_mul_of_nonneg_left hlen (sq_nonneg m.capLogFactor)
    nlinarith
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
