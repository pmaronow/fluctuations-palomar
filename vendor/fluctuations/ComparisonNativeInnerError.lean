module

public import ComparisonNativeOrdinaryError

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

theorem actual_native_inner_ordinary_error_bound
    (m : NativeBandModel) {cut C eps : ℝ} (hcut : 0 < cut)
    (hleft : m.cutRadius ≤  m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤  m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤  m.bandMass)
    (hlog : Real.log (1/cut) ≤  m.Lside) (hraw : NativeBandRawMaster m)
    (hUeq : m.U=comparisonSmallMass m.N m.E) (hU1 : m.U ≤ 1)
    (hLU : m.Lcap ≤  m.U) (hLlower : m.N^(-(1:ℝ)) ≤  m.Lcap)
    (hUA : m.U ≤ comparisonConditionalScale m.N m.delta m.E m.lam)
    (hvU : m.U ≤  m.bandMass) (hC : 0 ≤ C)
    (hvA : m.bandMass ≤ C*comparisonConditionalScale m.N m.delta m.E m.lam)
    (hyA : m.y ≤ C*comparisonConditionalScale m.N m.delta m.E m.lam)
    (hyN : m.y ≤  m.N) (hstrength : m.N*(m.N^(-m.delta)*m.lam) ≤  m.P)
    (horder : (m.delta+2)/((m.l:ℝ)-1) ≤ eps) :
    (∫u in 0..1,m.ordinaryMask (m.R u)*m.comparisonErrorDensity u) ≤ 
      3*nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*
        comparisonInnerPhysicalCore m.N m.delta m.E m.Q C m.capLogFactor eps+
      16*m.capLogFactor^2*C*m.N^(2*m.delta)*m.E+
      54*m.lam*(((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*cut := by
  have hthermal := actual_native_inner_ordinary_physical_bound m hcut hleft hupper hband hlog hraw
    hUeq hU1 hLU hLlower hUA hvU hC hvA hyA hyN hstrength horder
  have herror := actual_native_ordinary_error_le_thermal m hband
  have hNp : 0  <  m.N := zero_lt_one.trans_le m.hN
  have hlen := comparison_conditional_inner_length_cost hNp m.hE m.hlam hC m.hbandMass.le hvA
    m.hLcap.le (hUeq ▸ hLU)
  have hLA : m.Lcap ≤ comparisonConditionalScale m.N m.delta m.E m.lam := hLU.trans hUA
  have hs := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLA m.hLcap.le) (sq_nonneg m.capLogFactor)
  have hD : m.D0^2 ≤ m.capLogFactor^2*comparisonConditionalScale m.N m.delta m.E m.lam*m.Lcap := by
    rw [m.D0_eq_capLogFactor]
    nlinarith
  have hsquare : m.lam*m.bandMass*m.D0^2 ≤ m.capLogFactor^2*C*m.N^(2*m.delta)*m.E := by
    have h1 := mul_le_mul_of_nonneg_left hD (mul_pos m.hlam m.hbandMass).le
    have h2 := mul_le_mul_of_nonneg_left hlen (sq_nonneg m.capLogFactor)
    nlinarith
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
