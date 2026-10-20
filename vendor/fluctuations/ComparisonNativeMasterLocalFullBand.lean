module

public import ComparisonNativeMasterLocalBand

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

theorem actual_master_full_ordinary_local_band_budget
    (m : NativeBandModel) (bins : ℕ) (hbins : 0 < bins)
    {cut w : ℝ} (hcut : 0 < cut) (hw : 0 < w) (hRange : m.Q^2*m.y  ≤  (bins:ℝ)*w)
    (hleft : m.cutRadius  ≤  m.ag) (hupper : m.xs+m.alpha.val.val m.zg  ≤  m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag  ≤  m.bandMass)
    (hlog : Real.log (1/cut)  ≤  m.Lside)
    (hraw : NativeBandRawMaster m)
    {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hleftMass : v ≤  m.lo+m.U) (hspan : m.hi-m.lo ≤ C*v) :
    (∫v in 0..1,m.ordinaryMask (m.R v)*m.thermal v)  ≤ 
      nativeConditionalLedgerBudget bins m.bandMass cut (w+(m.localDiameter v C))
        (m.AS*(bins:ℝ)*m.Lside/(m.P*m.rho))
        (m.AC*m.bandMass/(m.P*m.rho^2)) (m.reverse (m.localDiameter v C)) m.Lside+2*(bins:ℝ)*cut := by
  have hb : m.ordinaryCaps⊆Icc (0:ℝ) 1 := fun r hr=>
    ⟨m.hag.le.trans (m.ordinaryCaps_band hr).1,(m.ordinaryCaps_band hr).2.trans m.hzg⟩
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  apply NativeCapExhaustion.actual_local_full_thermal_le_of_finite_caps
    m.hc m.hk m.hkc m.hm m.hM m.alpha m.ordinaryCaps_open hb m.H
    (NativeBandRetainedCaps.continuous_H m) (Ioo m.ag m.zg) measurableSet_Ioo
    m.thermal m.thermal_integrable
  intro F
  obtain ⟨g,hg⟩ := exists_nativeOrdinaryRetainedCaps m F
  obtain ⟨grid⟩ := exists_nativeBandMasterGrid m g hraw
  have h := actual_master_retained_local_band_budget m g grid bins hbins hcut hw hRange
    hleft hupper hband hlog hv hC
    (fun t=>by linarith [g.hamass t]) (fun t=>by linarith [g.hamass t,g.hzmass t])
  simpa only [NativeBandRetainedCaps.fullMask,hg,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one] using h

theorem actual_master_full_ordinary_local_band_optimized
    (m : NativeBandModel) {cut : ℝ} (hcut : 0 < cut)
    (hleft : m.cutRadius  ≤  m.ag) (hupper : m.xs+m.alpha.val.val m.zg  ≤  m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag  ≤  m.bandMass)
    (hlog : Real.log (1/cut)  ≤  m.Lside)
    (hraw : NativeBandRawMaster m)
    {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hleftMass : v ≤  m.lo+m.U) (hspan : m.hi-m.lo ≤ C*v) :
    ∃bins : ℕ,1  ≤  bins ∧
      (bins:ℝ)  ≤  ((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2 ∧
      (∫v in 0..1,m.ordinaryMask (m.R v)*m.thermal v)  ≤ 
      nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*m.bandMass*
        (2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
          3/(m.P*m.bandMass^2)+(m.localDiameter v C)^2+m.reverse (m.localDiameter v C))+18*(bins:ℝ)*cut := by
  obtain ⟨bins,hbins,hsize,hbudget⟩ := exists_integer_native_bin_scale m.hLside m.AS_nonneg m.AC_nonneg
    m.hbandMass m.rho_pos m.P_pos (m.localDiameter_pos hv hC).le (zero_le_one.trans m.hQ) m.hy.le
    (m.reverse_nonneg (m.localDiameter_pos hv hC).le) cut
  rw [mul_right_comm m.AS m.Lside (bins:ℝ)] at hbudget
  have hcover := native_bin_width_coverage (zero_lt_one.trans_le m.hQ) m.hy hbins
  have hfull := actual_master_full_ordinary_local_band_budget m bins (by omega) hcut hcover.1 hcover.2
    hleft hupper hband hlog hraw hv hC hleftMass hspan
  exact ⟨bins,hbins,hsize,by linarith⟩

theorem actual_master_full_ordinary_local_band_explicit
    (m : NativeBandModel) {cut : ℝ} (hcut : 0 < cut)
    (hleft : m.cutRadius  ≤  m.ag) (hupper : m.xs+m.alpha.val.val m.zg  ≤  m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag  ≤  m.bandMass)
    (hlog : Real.log (1/cut)  ≤  m.Lside)
    (hraw : NativeBandRawMaster m)
    {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hleftMass : v ≤  m.lo+m.U) (hspan : m.hi-m.lo ≤ C*v) :
    (∫v in 0..1,m.ordinaryMask (m.R v)*m.thermal v)  ≤ 
      nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*m.bandMass*
        (2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
          3/(m.P*m.bandMass^2)+(m.localDiameter v C)^2+m.reverse (m.localDiameter v C))+
      18*(((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*cut := by
  obtain ⟨bins,_,hbins,hbound⟩ := actual_master_full_ordinary_local_band_optimized m hcut hleft hupper hband hlog hraw hv hC hleftMass hspan
  have hcost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbins (show (0:ℝ) ≤ 18 by norm_num)) hcut.le
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
