module

public import ComparisonNativeMasterFullBand
public import ComparisonInnerPhysicalLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

namespace NativeBandModel

def capLogFactor (m : NativeBandModel) : ℝ :=
  9*Real.log m.N*Real.log ((1+m.U)/m.U)/m.N^m.delta

theorem capLogFactor_nonneg (m : NativeBandModel) : 0 ≤ m.capLogFactor := by
  have hlogU : 0<Real.log ((1+m.U)/m.U) := Real.log_pos ((lt_div_iff₀ m.hU).mpr (by linarith))
  unfold capLogFactor
  have hlog := m.hlog
  have hN : 0 < m.N := zero_lt_one.trans_le m.hN
  positivity

theorem D0_eq_capLogFactor (m : NativeBandModel) : m.D0=m.capLogFactor*m.Lcap := by
  unfold D0 capLogFactor
  ring

theorem ordinaryMask_composed_measurable (m : NativeBandModel) :
    Measurable (fun u=>m.ordinaryMask (m.R u)) := by
  let He := fun r=>m.H (projIcc (0:ℝ) 1 zero_le_one r)
  have hHe : Continuous He :=
    (continuousOn_iff_continuous_domRestrict.mp (NativeBandRetainedCaps.continuous_H m)).comp continuous_projIcc
  have hR := comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha
  have heq u : He (m.R u)=m.H (m.R u) := by
    dsimp [He]
    rw [projIcc_of_mem zero_le_one (comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u)]
  have hmask : (fun u=>m.ordinaryMask (m.R u))=
      (fun u=>(Ioo m.ag m.zg∩(m.ordinaryCaps∪{r | He r=0})).indicator (fun _=>(1:ℝ)) (m.R u)) := by
    funext u
    simp only [ordinaryMask,ordinarySupport,indicator_apply,mem_inter_iff,mem_union,mem_setOf_eq,heq]
  rw [hmask]
  exact (measurable_const.indicator
    (measurableSet_Ioo.inter (m.ordinaryCaps_open.measurableSet.union
      (hHe.measurable (measurableSet_singleton 0))))).comp hR.measurable

end NativeBandModel

theorem native_actual_weighted_thermal_le (m : NativeBandModel)
    (v : ℝ→ℝ) (hv : Measurable v) (hvb : ∀u∈Ioc (0:ℝ) 1,v u∈Icc (0:ℝ) 1) :
    (∫u in 0..1,v u*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u)≤
      m.lam*(∫u in 0..1,v u*m.thermal u) := by
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hT := physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
  have hvT := intervalIntegrable_bounded_measurable_mul hv (show (0:ℝ)≤1 by norm_num) hvb hT
  rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one,←integral_const_mul]
  apply integral_mono_of_nonneg _ (((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hvT).const_mul m.lam) _
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hp := orderedPath_SK_bounds (m.n+1) (by omega) m.bf m.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu
    have hTu : 0 ≤ m.thermal u := by dsimp [NativeBandModel.thermal];nlinarith [hp.2.2.1]
    exact mul_nonneg (mul_nonneg (hvb u hu).1 (laplaceComparisonStrength_pos m.d m.hlam _).le) hTu
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hp := orderedPath_SK_bounds (m.n+1) (by omega) m.bf m.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu
    have hTu : 0 ≤ m.thermal u := by dsimp [NativeBandModel.thermal];nlinarith [hp.2.2.1]
    have hh := mul_le_mul_of_nonneg_right (laplaceComparisonStrength_le m.d m.hlam.le (m.R u))
      (mul_nonneg (hvb u hu).1 hTu)
    change v u*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u≤ m.lam*(v u*m.thermal u)
    nlinarith

theorem actual_native_inner_ordinary_physical_bound
    (m : NativeBandModel) {cut C eps : ℝ} (hcut : 0<cut)
    (hleft : m.cutRadius≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg≤ m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag≤ m.bandMass)
    (hlog : Real.log (1/cut)≤ m.Lside) (hraw : NativeBandRawMaster m)
    (hUeq : m.U=comparisonSmallMass m.N m.E) (hU1 : m.U≤1)
    (hLU : m.Lcap≤ m.U) (hLlower : m.N^(-(1:ℝ))≤ m.Lcap)
    (hUA : m.U≤comparisonConditionalScale m.N m.delta m.E m.lam)
    (hvU : m.U≤ m.bandMass) (hC : 0≤C)
    (hvA : m.bandMass≤C*comparisonConditionalScale m.N m.delta m.E m.lam)
    (hyA : m.y≤C*comparisonConditionalScale m.N m.delta m.E m.lam)
    (hyN : m.y≤ m.N) (hstrength : m.N*(m.N^(-m.delta)*m.lam)≤ m.P)
    (horder : (m.delta+2)/((m.l:ℝ)-1)≤eps) :
    (∫u in 0..1,m.ordinaryMask (m.R u)*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u)≤
      nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*
        comparisonInnerPhysicalCore m.N m.delta m.E m.Q C m.capLogFactor eps+
      18*m.lam*(((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*cut := by
  have hweighted := native_actual_weighted_thermal_le m _ m.ordinaryMask_composed_measurable
    (fun u _=>by unfold NativeBandModel.ordinaryMask;by_cases h:m.R u∈m.ordinarySupport <;> simp [h])
  have hb := actual_master_full_ordinary_band_explicit m hcut hleft hupper hband hlog hraw
  have hratio := comparison_physical_reverse_ratio (delta:=m.delta) m.hN m.hlog m.hU hU1 hLlower m.hy.le hyN
  have hc := comparison_inner_ledger_physical_cost m.hl m.hN m.hE m.hlam m.P_pos hstrength
    (hUeq ▸ hvU) hvA m.hy hyA m.D0_pos m.hQ hC m.capLogFactor_nonneg m.hLcap.le
    (hUeq ▸ hLU) (hUeq ▸ hUA) m.D0_eq_capLogFactor.le hratio horder
  change m.lam*m.bandMass*(2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
      3/(m.P*m.bandMass^2)+m.D0^2+m.reverse m.D0)≤_ at hc
  have hF : 0≤nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho := by
    unfold nativeBinScaleLoss
    have hL := m.hLside
    have hAS := m.AS_nonneg
    have hAC := m.AC_nonneg
    have hv := m.hbandMass
    have hr := m.rho_pos
    positivity
  have h1 := mul_le_mul_of_nonneg_left hb m.hlam.le
  have h2 := mul_le_mul_of_nonneg_left hc hF
  nlinarith

end OAI.SKFluctuations.LaplaceWindowFormalization
