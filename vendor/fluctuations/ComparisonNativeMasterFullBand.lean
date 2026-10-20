module

public import ComparisonNativeMasterBandConstruction

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

def NativeBandRawMaster (m : NativeBandModel) : Prop :=
  ∀extra : List PositiveMass,(∀u∈extra,u.val≤1)→
    ∃nodes : List PositiveMass,(∀u∈nodes,u.val≤1) ∧ (∀u∈extra,u∈nodes) ∧
      ∀ᶠ j in atTop,physicalRawRatio (m.n+1) m.l
        (sampleClockSteps m.q 0 (finiteCutMasses nodes j)) 0 m.xs
        (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id ≤ m.Q

theorem exists_nativeBandMasterGrid (m : NativeBandModel) (g : NativeBandRetainedCaps m)
    (hraw : NativeBandRawMaster m) : Nonempty (NativeBandMasterGrid m g) := by
  have hnodes := finiteBoundaryMassNodes_bound (g.D.image m.alpha.val.val) (fun d hd=>by
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hd
    exact (m.alpha.val.property.1 r).2)
  obtain ⟨nodes,hbound,hretain,hQ⟩ := hraw (finiteBoundaryMassNodes (g.D.image m.alpha.val.val)) hnodes
  refine ⟨⟨nodes,hbound,?_,hQ⟩⟩
  intro d hd hpos
  exact hretain _ (finiteBoundaryMassNodes_mem (g.D.image m.alpha.val.val)
    (Finset.mem_image.mpr ⟨d,hd,rfl⟩) hpos)

theorem actual_master_full_ordinary_band_budget
    (m : NativeBandModel) (bins : ℕ) (hbins : 0<bins)
    {cut w : ℝ} (hcut : 0<cut) (hw : 0<w) (hRange : m.Q^2*m.y ≤ (bins:ℝ)*w)
    (hleft : m.cutRadius ≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤ m.bandMass)
    (hlog : Real.log (1/cut) ≤ m.Lside)
    (hraw : NativeBandRawMaster m) :
    (∫v in 0..1,m.ordinaryMask (m.R v)*m.thermal v) ≤
      nativeConditionalLedgerBudget bins m.bandMass cut (w+m.D0)
        (m.AS*(bins:ℝ)*m.Lside/(m.P*m.rho))
        (m.AC*m.bandMass/(m.P*m.rho^2)) (m.reverse m.D0) m.Lside+2*(bins:ℝ)*cut := by
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
  have h := actual_master_retained_band_budget m g grid bins hbins hcut hw hRange
    hleft hupper hband hlog
  simpa only [NativeBandRetainedCaps.fullMask,hg,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one] using h

theorem actual_master_full_ordinary_band_optimized
    (m : NativeBandModel) {cut : ℝ} (hcut : 0<cut)
    (hleft : m.cutRadius ≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤ m.bandMass)
    (hlog : Real.log (1/cut) ≤ m.Lside)
    (hraw : NativeBandRawMaster m) :
    ∃bins : ℕ,1 ≤ bins ∧
      (bins:ℝ) ≤ ((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2 ∧
      (∫v in 0..1,m.ordinaryMask (m.R v)*m.thermal v) ≤
      nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*m.bandMass*
        (2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
          3/(m.P*m.bandMass^2)+m.D0^2+m.reverse m.D0)+18*(bins:ℝ)*cut := by
  obtain ⟨bins,hbins,hsize,hbudget⟩ := exists_integer_native_bin_scale m.hLside m.AS_nonneg m.AC_nonneg
    m.hbandMass m.rho_pos m.P_pos m.D0_pos.le (zero_le_one.trans m.hQ) m.hy.le
    (m.reverse_nonneg m.D0_pos.le) cut
  rw [mul_right_comm m.AS m.Lside (bins:ℝ)] at hbudget
  have hcover := native_bin_width_coverage (zero_lt_one.trans_le m.hQ) m.hy hbins
  have hfull := actual_master_full_ordinary_band_budget m bins (by omega) hcut hcover.1 hcover.2
    hleft hupper hband hlog hraw
  exact ⟨bins,hbins,hsize,by linarith⟩

theorem actual_master_full_ordinary_band_explicit
    (m : NativeBandModel) {cut : ℝ} (hcut : 0<cut)
    (hleft : m.cutRadius ≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤ m.bandMass)
    (hlog : Real.log (1/cut) ≤ m.Lside)
    (hraw : NativeBandRawMaster m) :
    (∫v in 0..1,m.ordinaryMask (m.R v)*m.thermal v) ≤
      nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*m.bandMass*
        (2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
          3/(m.P*m.bandMass^2)+m.D0^2+m.reverse m.D0)+
      18*(((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*cut := by
  obtain ⟨bins,_,hbins,hbound⟩ := actual_master_full_ordinary_band_optimized m hcut hleft hupper hband hlog hraw
  have hcost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbins (show (0:ℝ)≤18 by norm_num)) hcut.le
  linarith

theorem actual_master_full_ordinary_band_polynomial_cut
    (m : NativeBandModel) (C : ℝ)
    (hleft : m.cutRadius ≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤ m.bandMass)
    (hlog : C*Real.log m.N ≤ m.Lside)
    (hraw : NativeBandRawMaster m) :
    (∫v in 0..1,m.ordinaryMask (m.R v)*m.thermal v) ≤
      nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*m.bandMass*
        (2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
          3/(m.P*m.bandMass^2)+m.D0^2+m.reverse m.D0)+
      18*(((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*m.N^(-C) := by
  have hN : 0< m.N := zero_lt_one.trans_le m.hN
  apply actual_master_full_ordinary_band_explicit m (Real.rpow_pos_of_pos hN _) hleft hupper hband _ hraw
  calc
    Real.log (1/m.N^(-C))=C*Real.log m.N := by
      rw [one_div,Real.log_inv,Real.log_rpow hN]
      ring
    _ ≤ m.Lside := hlog

end OAI.SKFluctuations.LaplaceWindowFormalization
