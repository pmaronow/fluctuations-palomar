module

public import ComparisonNativeMasterFullBand
public import ComparisonNativeLocalDiameterContinuum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

structure NativeConstructedBandRowsResult (m : NativeBandModel) (g : NativeBandRetainedCaps m)
    (bins : ℕ) (cut w : ℝ) where
  refinement : NativeBandRefinement m
  mask : ℝ  →  ℝ
  hmask : Measurable mask
  hbound : ∀r,mask r  ∈  Icc (0:ℝ) (g.fullMask r)
  omittedMass : (∫v in Icc (0:ℝ) 1,g.fullMask (m.R v))-
    (∫v in Icc (0:ℝ) 1,mask (m.R v))  ≤  2*(bins:ℝ)*cut
  frame_or_empty : (∃frame : NativeBandFrame m refinement bins cut w,
    frame.mask=mask ∧ (∀j,frame.A j=g.rows (refinement.as j))) ∨ mask=0

theorem exists_nativeMasterConstructedBandRowsResult
    (m : NativeBandModel) (g : NativeBandRetainedCaps m) (grid : NativeBandMasterGrid m g) (bins : ℕ) (hbins : 0 < bins)
    {cut w : ℝ} (hcut : 0 < cut) (hw : 0 < w) (hleft : m.cutRadius  ≤  m.ag)
    (hupper : m.xs+m.alpha.val.val m.zg  ≤  m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag  ≤  m.bandMass)
    (hlog : Real.log (1/cut)  ≤  m.Lside) :
    Nonempty (NativeConstructedBandRowsResult m g bins cut w) := by
  obtain ⟨start,hraw⟩ := eventually_atTop.mp grid.raw
  obtain ⟨ms,hms,hstart,C,l,u,f,labels,keep,hlabels,hkeep,hloss,hbinslim,hunionL1,hunionMass⟩ :=
    comparisonConstructedBins_exists_full_limits_master m.hc m.hk m.hkc m.hm m.hM (m.n+1) bins hbins m.q m.alpha
      g.a g.z m.H (NativeBandRetainedCaps.continuous_H m) g.D grid.nodes grid.bound grid.retains start m.hag m.hzg hcut g.hD g.haD g.hzD g.haz g.hinterior
      g.hga g.hgz m.capSet m.hopen m.hcapSet m.hnegative g.hnegative g.hwhole g.hdisjoint
      (fun _=>w) (fun _=>hw)
  have hnodes := grid.bound
  let s : NativeBandRefinement m := {
    as := fun j=>finiteCutMasses grid.nodes (ms j)
    mesh := fun j=>((ms j+1:ℕ):ℝ)⁻¹
    ho := fun j=>finiteCutMasses_ordered _ hnodes (ms j)
    he := fun j=>finiteCutMasses_end _ hnodes (ms j)
    hm := fun j=>finiteCutMasses_mesh _ hnodes (ms j)
    hm0 := fun _=>by positivity
    hmesh := uniformMasses_mesh_tendsto.comp hms.tendsto_atTop }
  let F := fun b : Fin bins=>g.fullSupport ∩ Ioo (l b).val (u b).val
  let mask : ℝ  →  ℝ := (nativeKeptSupport F keep).indicator (fun _=>1)
  have hF b : MeasurableSet (F b) := g.fullSupport_measurable.inter measurableSet_Ioo
  have hgeom : ∀b,∀ᵐ r ∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r ∈ NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (s.as j) i))
        (g.bin (s.as j) bins w b) ↔ r ∈ F b) := fun b=>(hbinslim b).2.1
  let side : ∀b,keep b=true  →  NativeConstructedBandSideData m s g bins cut w b (f b ⟨1,by simp⟩) :=
    fun b hb=>Classical.choice (exists_nativeConstructedBandSideData m s g bins hcut hleft b labels
      (l b).val (u b).val (f b) (fun j=>C j b) (fun j=>(hkeep j b).mpr hb) ((hbinslim b).1 hb))
  have hmasslim := constructedBandSides_mass_tendsto m s g bins cut w keep (fun b=>f b ⟨1,by simp⟩) side
  let unionGeometry := Classical.choice (exists_nativeConstructedUnionGeometry m s g bins hbins w hleft
    labels hlabels keep (fun b=>(l b).val) (fun b=>(u b).val) hgeom _ hmasslim)
  have hmask : Measurable mask := measurable_const.indicator (nativeKeptSupport_measurable F keep hF)
  have hbound r : mask r ∈ Icc (0:ℝ) (g.fullMask r) := by
    by_cases hr : r ∈ nativeKeptSupport F keep
    · have hrkeep := hr
      obtain ⟨b,_,hb⟩ := hr
      have hrF : r ∈ g.fullSupport := hb.1
      simp only [mask,indicator_of_mem hrkeep,NativeBandRetainedCaps.fullMask,indicator_of_mem hrF]
      norm_num
    · simp only [mask,indicator_of_notMem hr]
      exact ⟨le_rfl,(g.fullMask_bounds r).1⟩
  have hmassloss : (∫v in Icc (0:ℝ) 1,g.fullMask (m.R v))-
      (∫v in Icc (0:ℝ) 1,mask (m.R v))  ≤  2*(bins:ℝ)*cut := by
    apply le_of_tendsto ((g.full_mass_tendsto s).sub hunionMass)
    apply Eventually.of_forall
    intro j
    have hmass := native_height_bins_coordinate_mass (s.steps j)
      (fun i=>physicalPathSecondMoment (m.n+1) (s.steps j) (m.q 0) i.val) (g.rows (s.as j))
      (firstWholeUnitCell m.capSet
        (comparisonConstructedRowRadius m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (s.as j)))
      w hbins keep _ m.capSet (C j)
    exact hmass.2.2.trans_le (hloss j)
  refine ⟨⟨s,mask,hmask,hbound,hmassloss,?_⟩⟩
  by_cases hn : ∃b,keep b=true
  · obtain ⟨frame,hframe,_,hA⟩ := exists_nativeBandFrame_of_constructed_sides_with_rows m s g bins hcut hleft
      hupper hband hlog (fun j=>hraw (ms j) (hstart j)) keep hn (fun b=>f b ⟨1,by simp⟩) side F hF hgeom unionGeometry
    exact Or.inl ⟨frame,hframe,hA⟩
  · right
    funext r
    apply indicator_of_notMem
    rintro ⟨b,hb,_⟩
    exact hn ⟨b,hb⟩

theorem actual_master_retained_local_band_budget
    (m : NativeBandModel) (g : NativeBandRetainedCaps m) (grid : NativeBandMasterGrid m g) (bins : ℕ) (hbins : 0 < bins)
    {cut w : ℝ} (hcut : 0 < cut) (hw : 0 < w) (hRange : m.Q^2*m.y  ≤  (bins:ℝ)*w)
    (hleft : m.cutRadius  ≤  m.ag) (hupper : m.xs+m.alpha.val.val m.zg  ≤  m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag  ≤  m.bandMass)
    (hlog : Real.log (1/cut)  ≤  m.Lside)
    {v C : ℝ} (hv : 0 < v) (hC : 0 < C)
    (hleftMass : ∀t,v ≤  m.alpha.val.val (g.a t)+m.U)
    (hspan : ∀t,m.alpha.val.val (g.z t)-m.alpha.val.val (g.a t) ≤ C*v) :
    (∫v in 0..1,g.fullMask (m.R v)*m.thermal v)  ≤ 
      nativeConditionalLedgerBudget bins m.bandMass cut (w+(m.localDiameter v C))
        (m.AS*(bins:ℝ)*m.Lside/(m.P*m.rho))
        (m.AC*m.bandMass/(m.P*m.rho^2)) (m.reverse (m.localDiameter v C)) m.Lside+2*(bins:ℝ)*cut := by
  let B := nativeConditionalLedgerBudget bins m.bandMass cut (w+(m.localDiameter v C))
    (m.AS*(bins:ℝ)*m.Lside/(m.P*m.rho))
    (m.AC*m.bandMass/(m.P*m.rho^2)) (m.reverse (m.localDiameter v C)) m.Lside
  obtain ⟨result⟩ := exists_nativeMasterConstructedBandRowsResult m g grid bins hbins hcut hw hleft hupper hband hlog
  have hbudget : (∫v in 0..1,result.mask (m.R v)*m.thermal v)  ≤  B := by
    rcases result.frame_or_empty with ⟨frame,hframe,hA⟩ | he
    · rw [←hframe]
      exact frame.thermal_le_local_band_budget (m.localDiameter_pos hv hC)
        (frame_unit_oscillation_of_constructed_rows result.refinement g frame hA hv hC hleftMass hspan) hcut hw hRange
    · rw [he]
      simp only [Pi.zero_apply,zero_mul,intervalIntegral.integral_zero]
      have hAS := m.AS_nonneg
      have hAC := m.AC_nonneg
      have hP := m.P_pos
      have hR := m.rho_pos
      have hL := m.hLside
      have hV := m.hbandMass
      have hReverse := m.reverse_nonneg (m.localDiameter_pos hv hC).le
      dsimp [B,nativeConditionalLedgerBudget]
      positivity
  have hRmeas := (comparisonSweepQuantile_continuous m.hc m.hk m.hkc m.hm m.hM m.alpha).measurable
  have hthermal := actual_comparison_thermal_removed_mask_budget m.hc m.hk m.hkc m.hm m.hM
    m.n m.hd.ne' m.hlam.le m.b m.h m.hb m.hlb m.hh m.hh0 m.alpha
    (fun v=>g.fullMask (m.R v)) (fun v=>result.mask (m.R v))
    (g.fullMask_measurable.comp hRmeas) (result.hmask.comp hRmeas)
    (fun v _=>g.fullMask_bounds (m.R v))
    (fun v _=>⟨(result.hbound (m.R v)).1,(result.hbound (m.R v)).2.trans (g.fullMask_bounds (m.R v)).2⟩)
    (fun v _=>(result.hbound (m.R v)).2)
  have hloss : (∫v in 0..1,g.fullMask (m.R v))-(∫v in 0..1,result.mask (m.R v))  ≤  2*(bins:ℝ)*cut := by
    simpa only [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le zero_le_one] using result.omittedMass
  change ((∫v in 0..1,g.fullMask (m.R v)*m.thermal v)-
    (∫v in 0..1,result.mask (m.R v)*m.thermal v)) ∈ Icc (0:ℝ)
      ((∫v in 0..1,g.fullMask (m.R v))-(∫v in 0..1,result.mask (m.R v))) at hthermal
  change (∫v in 0..1,g.fullMask (m.R v)*m.thermal v)  ≤  B+2*(bins:ℝ)*cut
  linarith [hthermal.2]

end OAI.SKFluctuations.LaplaceWindowFormalization
