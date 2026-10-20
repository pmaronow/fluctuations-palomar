module

public import ComparisonNativeOrdinaryError
public import ComparisonNativeLocalCapOscillation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

namespace NativeBandModel

def groupStrength (m : NativeBandModel) : ℝ := laplaceComparisonStrength m.d m.lam m.ag

theorem groupStrength_pos (m : NativeBandModel) : 0 < m.groupStrength :=
  laplaceComparisonStrength_pos m.d m.hlam m.ag

theorem strength_le_groupStrength (m : NativeBandModel) {r : ℝ}
    (hr : r  ∈  Icc m.ag m.zg) : laplaceComparisonStrength m.d m.lam r  ≤  m.groupStrength :=
  (laplaceComparisonStrength_monotonicities m.hd.ne' m.hlam (r₀:=0) le_rfl).1
    ⟨m.hag.le,m.hagz.trans m.hzg⟩ ⟨m.hag.le.trans hr.1,hr.2.trans m.hzg⟩ hr.1

theorem ordinary_cap_length_le_localDiameter (m : NativeBandModel)
    {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hleftMass : v  ≤  m.lo+m.U) (hspan : m.hi-m.lo  ≤  C*v)
    {r : ℝ} (hr : r  ∈  m.ordinaryCaps) :
    sSup (ordConnectedComponent m.capSet r)-sInf (ordConnectedComponent m.capSet r)  ≤  m.localDiameter v C := by
  obtain ⟨ha,har,hrz,hz,heq,_,_⟩ := wholeCap_component_endpoints m.hopen
    (m.hcapSet.trans Ioo_subset_Icc_self) hr.1
  have hbang : ∀ᵐ t,t  ∈  Icc (0:ℝ) 1  →  m.H t < 0  →  deriv m.alpha.val.val t=
      comparisonCap m.N m.delta m.U m.Lcap m.E m.d (m.alpha.val.val t) := by
    simpa only [←m.hMdef] using m.hbang
  have htravel := potential_comparison_cap_interval_travel (zero_lt_one.trans_le m.hN)
    m.hU m.hLcap m.hE m.hd (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    (inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property)
    (fun t _=>m.alpha.val.property.1 t) hbang ha hz (har.trans hrz).le
    (fun t ht=>m.hnegative t (ordConnectedComponent_subset (heq.symm ▸ ht)))
  have hmasslo := hr.2.2.2.1
  have hmasshi := hr.2.2.2.2
  have hwidth : sSup (ordConnectedComponent m.capSet r)-sInf (ordConnectedComponent m.capSet r)  ≤ 
      C*m.E/(m.N^m.delta*m.d^3*v) := by
    calc
      _  ≤  (m.alpha.val.val (sSup (ordConnectedComponent m.capSet r))-
          m.alpha.val.val (sInf (ordConnectedComponent m.capSet r)))*m.E/(m.N^m.delta*m.d^3*v^2) :=
        htravel.2.2 v hv (by linarith)
      _  ≤  C*v*m.E/(m.N^m.delta*m.d^3*v^2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) m.hE.le)
          (mul_nonneg (mul_nonneg (Real.rpow_nonneg (zero_le_one.trans m.hN) _)
            (pow_nonneg m.hd.le _)) (sq_nonneg _))
      _ = _ := by field_simp
  have hlog : (1:ℝ)  ≤  9*Real.log m.N := by linarith [m.hlog]
  have hpos : 0  ≤  C*m.E/(m.N^m.delta*m.d^3*v) := by
    exact div_nonneg (mul_pos hC m.hE).le (mul_pos (mul_pos
      (Real.rpow_pos_of_pos (zero_lt_one.trans_le m.hN) _) (pow_pos m.hd 3)) hv).le
  have hh := mul_le_mul_of_nonneg_right hlog hpos
  dsimp only [localDiameter]
  nlinarith [show 9*Real.log m.N*(C*m.E/(m.N^m.delta*m.d^3*v))=
    9*Real.log m.N*C*m.E/(m.N^m.delta*m.d^3*v) by ring]

theorem ordinary_mismatch_ae_radius_of_cap_length (m : NativeBandModel) {D : ℝ}
    (hcap : ∀ r  ∈  m.ordinaryCaps,
      sSup (ordConnectedComponent m.capSet r)-sInf (ordConnectedComponent m.capSet r)  ≤  D) :
    ∀ᵐ r,r  ∈  Icc (0:ℝ) 1  →  r  ∈  m.ordinarySupport  →  
      (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r)^2 ≤ 
        16*D^2+2*m.thermal (m.alpha.val.val r) := by
  have hmom := comparisonVariableEndpoint_radius_moments m.hc m.hk m.hkc m.hm m.hM
    (m.n+1) (by omega) m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  filter_upwards [m.hzero,volume.ae_ne (0:ℝ)] with r hz hr0 hr hs
  rcases hs.2 with hc|hcontact
  · obtain ⟨ha,har,hrz,hz,heq,_,_⟩ := wholeCap_component_endpoints m.hopen
      (m.hcapSet.trans Ioo_subset_Icc_self) hc.1
    have hboundary : (m.H (sInf (ordConnectedComponent m.capSet r))=0 ∧
        m.H (sSup (ordConnectedComponent m.capSet r))=0) ∨
        (sInf (ordConnectedComponent m.capSet r)=0 ∧ m.H (sSup (ordConnectedComponent m.capSet r))=0) ∨
        (m.H (sInf (ordConnectedComponent m.capSet r))=0 ∧ sSup (ordConnectedComponent m.capSet r)=1) := by
      rcases (m.hcomponent r hc.1).2 with h|h
      · exact Or.inl ⟨(m.hcomponent r hc.1).1,h⟩
      · exact Or.inr (Or.inr ⟨(m.hcomponent r hc.1).1,h⟩)
    have hm := native_actual_cap_mismatch_endpoint_cases m ha hz ⟨har,hrz⟩ hboundary (m.hnegative r hc.1)
    have hlen := hcap r hc
    have hsquare := pow_le_pow_left₀ (sub_nonneg.mpr (har.trans hrz).le) hlen 2
    nlinarith
  · have hrp : 0<r := lt_of_le_of_ne hr.1 hr0.symm
    have hb := hmom.2.2 r hr
    have hp := laplaceComparisonStrength_logSlope_mem m.hd.ne' m.hlam.ne' r
    have hm := (comparison_gradient_contact_mismatch hrp (laplaceComparisonStrength_pos m.d m.hlam r)
      ⟨hp.1,hp.2.le⟩ hb.1.1 hb.2.1 (hz hr hcontact)).2
    change (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r)^2 ≤ 
      orderedPathB (m.n+1) m.bf m.hf (m.alpha.val.val r)-
        (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r))^2 at hm
    dsimp [thermal]
    nlinarith [sq_nonneg D,sq_nonneg (orderedPathS (m.n+1) m.bf m.hf (m.alpha.val.val r)-r)]

theorem ordinary_mismatch_ae_mass_of_cap_length (m : NativeBandModel) {D : ℝ}
    (hcap : ∀ r  ∈  m.ordinaryCaps,
      sSup (ordConnectedComponent m.capSet r)-sInf (ordConnectedComponent m.capSet r)  ≤  D) :
    ∀ᵐ u,u  ∈  Icc (0:ℝ) 1  →  m.R u  ∈  m.ordinarySupport  →  
      (orderedPathS (m.n+1) m.bf m.hf u-m.R u)^2 ≤ 16*D^2+2*m.thermal u := by
  have hh := ae_inverse_pullback (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    (fun u (_ : u  ∈  Icc (0:ℝ) 1)=>comparisonSweepQuantile_bounds m.hc m.hk m.hkc m.hm m.hM m.alpha u)
    (fun u hu=>comparisonSweepQuantile_mass_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hu)
    (m.ordinary_mismatch_ae_radius_of_cap_length hcap)
  filter_upwards [hh] with u hu hui hs
  have h := hu hui hs
  simpa only [comparisonSweepQuantile_mass_spec m.hc m.hk m.hkc m.hm m.hM m.alpha hui] using h

end NativeBandModel

theorem actual_native_ordinary_error_le_local_thermal
    (m : NativeBandModel) {D : ℝ}
    (hcap : ∀ r  ∈  m.ordinaryCaps,
      sSup (ordConnectedComponent m.capSet r)-sInf (ordConnectedComponent m.capSet r)  ≤  D) (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤  m.bandMass) :
    (∫u in 0..1,m.ordinaryMask (m.R u)*m.comparisonErrorDensity u) ≤ 
      3*(∫u in 0..1,m.ordinaryMask (m.R u)*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u)+
      16*m.groupStrength*D^2*m.bandMass := by
  have hR := (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable
  have he := ((laplaceComparisonStrength_contDiff m.d m.lam).continuous.measurable).comp hR
  have hm := m.ordinaryMask_composed_measurable
  have hmb u : m.ordinaryMask (m.R u)  ∈  Icc (0:ℝ) 1 := by
    unfold NativeBandModel.ordinaryMask
    by_cases h:m.R u  ∈  m.ordinarySupport <;> simp [h]
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hT := physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
  have hiW : IntervalIntegrable (fun u=>m.ordinaryMask (m.R u)*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u) volume 0 1 := intervalIntegrable_bounded_measurable_mul (hm.mul he) m.hlam.le
    (fun u _=>⟨mul_nonneg (hmb u).1 (laplaceComparisonStrength_pos m.d m.hlam _).le,
      (mul_le_mul_of_nonneg_right (hmb u).2 (laplaceComparisonStrength_pos m.d m.hlam _).le).trans
        (by simpa only [one_mul] using laplaceComparisonStrength_le m.d m.hlam.le (m.R u))⟩) hT
  have hiM : IntervalIntegrable (fun u=>m.ordinaryMask (m.R u)) volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hm
      (show (0:ℝ) ≤ 1 by norm_num) (fun u _=>hmb u) (intervalIntegrable_const (c:=(1:ℝ)))
  have hiUpper : IntervalIntegrable (fun u=>3*(m.ordinaryMask (m.R u)*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u)+(16*m.groupStrength*D^2)*m.ordinaryMask (m.R u)) volume 0 1 := (hiW.const_mul 3).add (hiM.const_mul (16*m.groupStrength*D^2))
  have hle : (∫u in 0..1,m.ordinaryMask (m.R u)*m.comparisonErrorDensity u) ≤ 
      ∫u in 0..1,3*(m.ordinaryMask (m.R u)*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u)+
        (16*m.groupStrength*D^2)*m.ordinaryMask (m.R u) := by
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one]
    apply integral_mono_of_nonneg _ ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hiUpper) _
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hp := orderedPath_SK_bounds (m.n+1) (by omega) m.bf m.hf
        (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu
      have ht : 0  ≤  m.thermal u := sub_nonneg.mpr hp.2.2.1
      exact mul_nonneg (hmb u).1 (mul_nonneg (laplaceComparisonStrength_pos m.d m.hlam _).le
        (add_nonneg ht (sq_nonneg _)))
    · filter_upwards [ae_restrict_mem measurableSet_Ioc,ae_restrict_of_ae (m.ordinary_mismatch_ae_mass_of_cap_length hcap)] with u hu hmis
      by_cases hs:m.R u  ∈  m.ordinarySupport
      · have hh := hmis (Ioc_subset_Icc_self hu) hs
        have hmul := mul_le_mul_of_nonneg_left hh (laplaceComparisonStrength_pos m.d m.hlam (m.R u)).le
        have hstr := mul_le_mul_of_nonneg_right (m.strength_le_groupStrength (Ioo_subset_Icc_self hs.1)) (sq_nonneg D)
        simp only [NativeBandModel.ordinaryMask,indicator_of_mem hs,one_mul,NativeBandModel.comparisonErrorDensity]
        nlinarith
      · simp only [NativeBandModel.ordinaryMask,indicator_of_notMem hs,zero_mul,mul_zero,zero_add,le_refl]
  have hmass := mul_le_mul_of_nonneg_left (m.ordinary_mask_mass_le hband)
    (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 16) m.groupStrength_pos.le) (sq_nonneg D))
  rw [intervalIntegral.integral_add (hiW.const_mul 3) (hiM.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hle
  nlinarith

theorem native_actual_ordinary_weighted_thermal_le (m : NativeBandModel) :
    (∫u in 0..1,m.ordinaryMask (m.R u)*laplaceComparisonStrength m.d m.lam (m.R u)*m.thermal u)  ≤ 
      m.groupStrength*(∫u in 0..1,m.ordinaryMask (m.R u)*m.thermal u) := by
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  have hT := physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
  have hmb u : m.ordinaryMask (m.R u)  ∈  Icc (0:ℝ) 1 := by
    unfold NativeBandModel.ordinaryMask
    by_cases h:m.R u  ∈  m.ordinarySupport <;> simp [h]
  have hi := intervalIntegrable_bounded_measurable_mul m.ordinaryMask_composed_measurable
    (show (0:ℝ)  ≤  1 by norm_num) (fun u _=>hmb u) hT
  rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one,←integral_const_mul]
  apply integral_mono_of_nonneg _ (((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hi).const_mul m.groupStrength) _
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hp := orderedPath_SK_bounds (m.n+1) (by omega) m.bf m.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu
    have ht : 0  ≤  m.thermal u := sub_nonneg.mpr hp.2.2.1
    exact mul_nonneg (mul_nonneg (hmb u).1 (laplaceComparisonStrength_pos m.d m.hlam _).le) ht
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    by_cases hs:m.R u  ∈  m.ordinarySupport
    · have hp := orderedPath_SK_bounds (m.n+1) (by omega) m.bf m.hf
        (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) hu
      have ht : 0  ≤  m.thermal u := sub_nonneg.mpr hp.2.2.1
      have hh := mul_le_mul_of_nonneg_right (m.strength_le_groupStrength (Ioo_subset_Icc_self hs.1)) ht
      simpa only [NativeBandModel.ordinaryMask,indicator_of_mem hs,one_mul,NativeBandModel.thermal] using hh
    · simp only [NativeBandModel.ordinaryMask,indicator_of_notMem hs,zero_mul,mul_zero,le_refl]

end OAI.SKFluctuations.LaplaceWindowFormalization
