module

public import ComparisonNativePositiveCells

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 5000000
attribute [local instance] Classical.propDecidable

theorem exists_actual_native_positive_broad_slice_frame
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBroadSliceGeometry m)
    {cut : ℝ} (hcut : 0< cut) (hmargin : 2*cut<∫r in Ioo g.a g.b,deriv m.alpha.val.val r)
    (hleft : m.cutRadius≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg≤ m.y)
    (hlog : Real.log (1/cut)≤ m.Lside)
    (hraw : ∀j,physicalRawRatio (m.n+1) m.l (s.steps j) 0 m.xs
      (Measure.pi fun a=>ProbabilityTheory.gaussianReal 0 (m.q 0 a)) id measurable_id≤ m.Q) :
    ∃N : ℕ,∃frame : NativeBroadFrame m (s.tail N) cut,
      frame.slice=Ioo g.a g.b ∧ frame.capA=g.capA ∧ frame.capZ=g.capZ ∧
      frame.scale=g.scale ∧ frame.width=∫r in Ioo g.a g.b,deriv m.alpha.val.val r := by
  have ha0 : 0≤ g.a := m.hag.le.trans g.haGroup
  have hb1 : g.b≤1 := g.hbGroup.trans m.hzg
  have hmasslim := comparisonNativeSliceRows_mass_tendsto m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha s.as s.mesh s.ho s.he s.hm s.hmesh ha0 hb1
  obtain ⟨N,hN⟩ := eventually_atTop.mp ((tendsto_order.mp hmasslim).1 (2*cut) hmargin)
  let st := s.tail N
  let J0 := fun j=>comparisonNativeSliceRows m.hc m.hk m.hkc m.hm m.hM m.q m.alpha
    (st.as j) g.a g.b
  let J := fun j=>positiveSelectedCells (st.steps j) (J0 j)
  let widths := fun j=>physicalWindowMass (st.steps j) 0 (J0 j)
  let width := ∫r in Ioo g.a g.b,deriv m.alpha.val.val r
  have hwidths j : 2*cut≤ widths j := (hN (j+N) (by omega)).le
  have hwidthlim : Tendsto widths atTop (𝓝 width) := hmasslim.comp (tendsto_add_atTop_nat N)
  have hmemb j i (hi : i∈J j) :=
    (comparisonNativeSliceRows_mem m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (st.as j) g.a g.b i).mp (Finset.mem_filter.mp hi).1
  have hleftRows j : ∀i∈J j,m.cutRadius≤ m.R (partitionPoint 0 (st.as j) i.val) := by
    intro i hi
    exact hleft.trans (g.haGroup.trans (hmemb j i hi).2.1.1.le)
  have hupperRows j : ∀i∈J j,m.xs+physicalCutMass 0 (st.steps j) i.val≤ m.y := by
    intro i hi
    have hil := (hmemb j i hi).1
    have hrad : m.R (partitionPoint 0 (st.as j) i.val)≤ m.zg :=
      (hmemb j i hi).2.1.2.le.trans g.hbGroup
    have hm := m.alpha.val.property.2 hrad
    rw [comparisonSweepQuantile_mass_spec m.hc m.hk m.hkc m.hm m.hM m.alpha
      (partitionPoint_mem (st.as j) (st.ho j) i.val)] at hm
    rw [physicalCutMass_sampleClockSteps m.q 0 (st.as j) i.val hil.le]
    linarith
  have hsideColumns := comparisonNativeSlice_side_L1 m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha st.as st.mesh st.ho st.he st.hm st.hmesh ha0 hb1 m.hag.le m.hzg hcut hmargin.le hwidths
  have hmaskColumns := comparisonNativeSlice_mask_group_L1 m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha st.as st.mesh st.ho st.he st.hm st.hmesh g.a g.b m.ag m.zg m.hag.le m.hzg
  have hmaskPoint := comparisonNativeSliceRows_mask_ae m.hc m.hk m.hkc m.hm m.hM
    m.q m.alpha st.as st.mesh st.ho st.he st.hm st.hmesh g.a g.b
  rw [restrict_Ioo_eq_restrict_Icc] at hmaskPoint
  have hmassSum j : (∑i,physicalSelectedCellMass (st.steps j) (J j) i)=widths j := by
    calc
      (∑i,physicalSelectedCellMass (st.steps j) (J j) i)=
          ∑i,physicalSelectedCellMass (st.steps j) (J0 j) i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact physicalSelectedCellMass_positiveSelectedCells (st.steps j)
          (sampleClockSteps_ordered m.q _ (st.ho j)) (J0 j) i
      _=widths j := by simp [widths,physicalWindowMass,physicalSelectedCellMass]
  have hcolEq (j:ℕ) {K:ℕ}
      (unit:Fin ((st.steps j).length+1)→Fin K) (col:Fin K→ℝ) :
      comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (st.as j)
        (J j) unit col=
      comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (st.as j)
        (J0 j) unit col :=
    comparisonNativeUnitColumnWeight_positiveSelectedCells m.hc m.hk m.hkc m.hm m.hM
      m.q m.alpha (st.as j) (st.ho j) (J0 j) unit col
  let frame : NativeBroadFrame m st cut := {
    capA := g.capA
    capZ := g.capZ
    ha := g.ha
    haz := g.haz
    hz := g.hz
    hboundary := g.hboundary
    hnegative := g.hnegative
    slice := Ioo g.a g.b
    hsliceMeas := measurableSet_Ioo
    hsliceCap := Ioo_subset_Ioo g.haCap g.hbCap
    hsliceGroup := Ioo_subset_Ioo g.haGroup g.hbGroup
    hoverlap := by
      have hc : max g.capA m.ag< g.b := max_lt (g.haCap.trans_lt g.hab) (g.haGroup.trans_lt g.hab)
      have hl : max g.capA m.ag≤ g.a := max_le g.haCap g.haGroup
      exact lt_min (hl.trans_lt (g.hab.trans_le g.hbCap)) (hc.trans_le g.hbGroup)
    scale := g.scale
    ceiling := g.ceiling
    hscale := g.hscale
    hceiling := g.hceiling
    hcomparable := g.hcomparable
    hsliceCeiling := fun r hr=>(m.alpha.val.property.2 hr.2.le).trans g.hceilingMass
    hsliceMass := g.hmass
    hcal := g.hcal
    selected := J
    widths := widths
    width := width
    hwidth := hmargin.le
    hwidths := hwidths
    hwidthlim := hwidthlim
    hmass := by
      intro j
      rw [physicalSelectedUnitMass_fin_one]
      exact positiveSelectedCells_mass (st.steps j) (sampleClockSteps_ordered m.q _ (st.ho j)) (J0 j)
    hmasslim := by simpa only [hmassSum] using hwidthlim
    hwidthMass := rfl
    hpos := fun j i hi=>(Finset.mem_filter.mp hi).2
    hleft := hleftRows
    hcapRows := fun j i hi=>⟨g.haCap.trans_lt (hmemb j i hi).2.1.1,
      (hmemb j i hi).2.1.2.trans_le g.hbCap⟩
    hmassUpper := hupperRows
    rawUpper := fun j=>hraw (j+N)
    hsideLog := by
      intro j
      have hp : 0< widths j := by linarith [hwidths j]
      exact (Real.log_le_log (div_pos hp hcut)
        (div_le_div_of_nonneg_right (physicalWindowMass_mem_Icc_one _
          (sampleClockSteps_ordered m.q (st.as j) (st.ho j)) _).2 hcut.le)).trans hlog
    hsupportSide := by
      intro j
      have heq : (fun u:Fin 1=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) u.val)=
          fun _=>sideSquareColumn (nativeBroadPoints (widths j)) cut (widths j) 0 := by
        funext u
        rw [Fin.eq_zero u]
        rfl
      rw [heq,hcolEq]
      exact comparisonNativeSliceColumn_group_support m.hc m.hk m.hkc m.hm m.hM
        m.q m.alpha (st.as j) g.a g.b _ m.ag m.zg g.haGroup g.hbGroup
    hsupportMask := by
      intro j
      rw [hcolEq]
      exact comparisonNativeSliceColumn_group_support m.hc m.hk m.hkc m.hm m.hM
        m.q m.alpha (st.as j) g.a g.b 1 m.ag m.zg g.haGroup g.hbGroup
    hsideColumns := by
      simp_rw [hcolEq]
      simpa only [fixedSliceContactWeight,Fin.sum_univ_one,indicator_zero,add_zero] using hsideColumns
    hmaskColumns := by
      simp_rw [hcolEq]
      simpa only [fixedSliceContactWeight,Fin.sum_univ_one,indicator_zero,add_zero] using hmaskColumns
    hmaskPoint := by
      filter_upwards [hmaskPoint] with r hr
      apply tendsto_const_nhds.congr'
      filter_upwards [hr] with j hj
      rw [hcolEq]
      exact hj.symm }
  exact ⟨N,frame,rfl,rfl,rfl,rfl,rfl⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
