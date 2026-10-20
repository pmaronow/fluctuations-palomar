module

public import ComparisonNativeConstructedColumnAssembly
public import ComparisonNativeBandAssembly
public import ComparisonCapContactReindex

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 3600000
attribute [local instance] Classical.propDecidable

structure NativeBandRetainedCaps (m : NativeBandModel) where
  count : ℕ
  a : Fin count → ℝ
  z : Fin count → ℝ
  hga : ∀t,m.ag ≤ a t
  haz : ∀t,a t<z t
  hgz : ∀t,z t ≤ m.zg
  haH : ∀t,m.H (a t)=0
  hzH : ∀t,m.H (z t)=0 ∨ z t=1
  hnegative : ∀t,∀r∈Ioo (a t) (z t),m.H r<0
  hamass : ∀t,m.lo ≤ m.alpha.val.val (a t)
  hzmass : ∀t,m.alpha.val.val (z t) ≤ m.hi
  hwhole : ∀t,∀r∈Ioo (a t) (z t),wholeUnit m.capSet r=Ioo (a t) (z t)
  hdisjoint : Pairwise (fun s t=>Disjoint (Ioo (a s) (z s)) (Ioo (a t) (z t)))
  D : Finset ℝ
  hD : ∀d∈D,d∈Icc (0:ℝ) 1
  haD : ∀t,a t∈D
  hzD : ∀t,z t∈D
  hinterior : ∀t,∀d∈D,d∉Ioo (a t) (z t)

namespace NativeBandRetainedCaps

abbrev rows {m : NativeBandModel} (g : NativeBandRetainedCaps m) (as : List PositiveMass) :=
  comparisonConstructedRows m.hc m.hk m.hkc m.hm m.hM m.q m.alpha as g.a g.z m.H g.D m.ag m.zg

abbrev bin {m : NativeBandModel} (g : NativeBandRetainedCaps m) (as : List PositiveMass)
    (bins : ℕ) (w : ℝ) (b : Fin bins) :=
  comparisonConstructedBin m.hc m.hk m.hkc m.hm m.hM (m.n+1) bins m.q m.alpha as
    g.a g.z m.H g.D m.ag m.zg w m.capSet b

theorem row_nonterminal {m : NativeBandModel} (g : NativeBandRetainedCaps m)
    (as : List PositiveMass) (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi : i∈g.rows as) :
    i.val<as.length := by
  exact ((comparisonNativeSelectedRows_mem m.hc m.hk m.hkc m.hm m.hM m.q m.alpha as
    g.a g.z m.H g.D i).mp (Finset.mem_filter.mp hi).1).1

theorem row_positive {m : NativeBandModel} (g : NativeBandRetainedCaps m)
    (as : List PositiveMass) (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi : i∈g.rows as) :
    0<pathMassDifferences (sampleClockSteps m.q 0 as) 0 i := (Finset.mem_filter.mp hi).2.1

theorem row_radius_bounds {m : NativeBandModel} (g : NativeBandRetainedCaps m)
    (as : List PositiveMass) (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi : i∈g.rows as) :
    m.ag ≤ m.R (partitionPoint 0 as i.val) ∧ m.R (partitionPoint 0 as (i.val+1)) ≤ m.zg :=
  (Finset.mem_filter.mp hi).2.2

theorem row_mass_bounds {m : NativeBandModel} (g : NativeBandRetainedCaps m)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi : i∈g.rows as) :
    m.alpha.val.val m.ag ≤ physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val ∧
      physicalCutMass 0 (sampleClockSteps m.q 0 as) (i.val+1) ≤ m.alpha.val.val m.zg := by
  have hs := sampleClockSteps_ordered m.q as ho
  have hindex := g.row_nonterminal as i hi
  have hr := g.row_radius_bounds as i hi
  rw [←physicalCutMass_sampleClockSteps m.q 0 as i.val hindex.le,
    ←physicalCutMass_sampleClockSteps m.q 0 as (i.val+1) (by omega)] at hr
  constructor
  · have hh := m.alpha.val.property.2 hr.1
    simpa only [NativeBandModel.R,comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha
      (physicalCutMass_mem _ hs i.val)] using hh
  · have hh := m.alpha.val.property.2 hr.2
    simpa only [NativeBandModel.R,comparisonSweepQuantile_spec m.hc m.hk m.hkc m.hm m.hM m.alpha
      (physicalCutMass_mem _ hs (i.val+1))] using hh

theorem rows_massUpper {m : NativeBandModel} (g : NativeBandRetainedCaps m)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (hy : m.xs+m.alpha.val.val m.zg ≤ m.y) :
    ∀i∈g.rows as,m.xs+physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val ≤ m.y := by
  intro i hi
  have hs := sampleClockSteps_ordered m.q as ho
  have hcut := physicalCutMass_monotone _ hs (Nat.le_succ i.val)
  linarith [(g.row_mass_bounds as ho i hi).2]

theorem rows_lower {m : NativeBandModel} (g : NativeBandRetainedCaps m)
    (as : List PositiveMass) (hcut : m.cutRadius ≤ m.ag) :
    ∀i∈g.rows as,m.cutRadius ≤ m.R (partitionPoint 0 as i.val) :=
  fun i hi=>hcut.trans (g.row_radius_bounds as i hi).1

theorem column_support {m : NativeBandModel} (g : NativeBandRetainedCaps m)
    (as : List PositiveMass) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) (hJ : J⊆g.rows as)
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1) → Fin K) (col : Fin K → ℝ) :
    ∀ᵐ r,r∉Ioo m.ag m.zg → comparisonNativeUnitColumnWeight m.hc m.hk m.hkc m.hm m.hM
      m.q m.alpha as J unit col r=0 := by
  filter_upwards [volume.ae_ne m.zg] with r hrz
  intro hr
  rw [comparisonNativeUnitColumnWeight,radiusCellEnergyDensity_eq_finite_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hil : i<as.length := Finset.mem_range.mp hi
  let ii : Fin ((sampleClockSteps m.q 0 as).length+1) := ⟨i,by rw [sampleClockSteps_length];omega⟩
  by_cases hij : ii∈J
  · have hb := g.row_radius_bounds as ii (hJ hij)
    apply indicator_of_notMem
    intro hri
    have hright : r < m.zg := lt_of_le_of_ne (hri.2.trans hb.2) hrz
    exact hr ⟨hb.1.trans_lt hri.1,hright⟩
  · have hz : nativeSelectedColumn J unit col i=0 := by
      change nativeSelectedColumn J unit col ii.val=0
      rw [nativeSelectedColumn_atIndex,ite_eq_right hij]
    simp only [hz,indicator_zero]

end NativeBandRetainedCaps

theorem physicalWindowMass_le_selected_cut_span {ι : Type}
    (steps : List (GaussianStep ι)) (hs : OrderedSteps 0 steps)
    (J : Finset (Fin (steps.length+1))) {a z : ℝ} (haz : a ≤ z)
    (hJ : ∀i∈J,a ≤ physicalCutMass 0 steps i.val ∧ physicalCutMass 0 steps (i.val+1) ≤ z) :
    physicalWindowMass steps 0 J ≤ z-a := by
  by_cases hn : J.Nonempty
  · let p := J.min' hn
    let q := J.max' hn
    have hp : p∈J := Finset.min'_mem J hn
    have hq : q∈J := Finset.max'_mem J hn
    have hspan := physicalSelectedUnitMass_le_endpoint_span steps hs J (fun _=>(0:Fin 1)) p q
      hp hq rfl (fun i hi _=>Finset.min'_le J i hi) (fun i hi _=>Finset.le_max' J i hi)
    have he : physicalSelectedUnitMass steps J (fun _=>(0:Fin 1)) 0=physicalWindowMass steps 0 J := by
      simp [physicalSelectedUnitMass,physicalWindowMass]
    rw [he] at hspan
    exact hspan.trans (sub_le_sub (hJ q hq).2 (hJ p hp).1)
  · have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [he,physicalWindowMass,Finset.sum_empty]
    exact sub_nonneg.mpr haz

theorem NativeBandRetainedCaps.selected_mass_le {m : NativeBandModel} (g : NativeBandRetainedCaps m)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) (hJ : J⊆g.rows as) :
    physicalWindowMass (sampleClockSteps m.q 0 as) 0 J ≤ m.alpha.val.val m.zg-m.alpha.val.val m.ag := by
  exact physicalWindowMass_le_selected_cut_span _ (sampleClockSteps_ordered m.q as ho) J
    (m.alpha.val.property.2 m.hagz) (fun i hi=>g.row_mass_bounds as ho i (hJ hi))

theorem sideSquareColumnLR_nonneg {δ width : ℝ} (hwidth : 2*δ ≤ width) (l r : ℝ) :
    0 ≤ sideSquareColumnLR δ width l r := by
  apply intervalIntegral.integral_nonneg_of_forall (by linarith : δ ≤ width-δ)
  intro t
  exact add_nonneg (sq_nonneg _) (sq_nonneg _)

structure NativeConstructedBandSideData (m : NativeBandModel) (s : NativeBandRefinement m)
    (g : NativeBandRetainedCaps m) (bins : ℕ) (cut w : ℝ) (b : Fin bins) (width : ℝ) where
  side : NativeBandSideGeometry m s cut
  selected_eq : ∀j,side.selected j=g.bin (s.as j) bins w b
  width_eq : side.width=width
  widths_le_one : ∀j,side.widths j ≤ 1
  widths_eq_mass : ∀j,side.widths j=physicalWindowMass (s.steps j) 0 (g.bin (s.as j) bins w b)
  classes : ∀j,∀i∈side.selected j,∀t∈side.selected j,
    side.unit j i=side.unit j t ↔ wholeUnit m.capSet (m.R (physicalCutMass 0 (s.steps j) i.val))=
      wholeUnit m.capSet (m.R (physicalCutMass 0 (s.steps j) t.val))
  order : ∀j,MonotoneOn (side.unit j) (side.selected j:Set _)

theorem exists_nativeConstructedBandSideData
    (m : NativeBandModel) (s : NativeBandRefinement m) (g : NativeBandRetainedCaps m)
    (bins : ℕ) {cut w : ℝ} (hcut : 0<cut) (hleft : m.cutRadius ≤ m.ag)
    (b : Fin bins) (labels : Fin g.count → Fin bins) (l u : ℝ) (f : Icc (0:ℝ) 1 →ᵇ ℝ)
    (C : ∀j,NativeConstructedCoordinates (s.steps j) (g.bin (s.as j) bins w b)
      (comparisonConstructedRowRadius m.hc m.hk m.hkc m.hm m.hM m.q m.alpha (s.as j)) m.capSet)
    (hwidths : ∀j,2*cut ≤ (C j).x (C j).K)
    (hlimit : NativeConstructedBinLimit m.hc m.hk m.hkc m.hm m.hM (m.n+1) bins m.q m.alpha
      s.as g.a g.z m.H g.D m.ag m.zg cut (fun _=>w) m.capSet b C labels l u f) :
    Nonempty (NativeConstructedBandSideData m s g bins cut w b (f ⟨1,by simp⟩)) := by
  obtain ⟨cl,cr,hcap,hwlim,hwidth,hpoint,hL1,hderiv,hlog⟩ := hlimit
  let B := {t : Fin g.count // labels t=b}
  let e : Fin (Fintype.card B)≃B := (Fintype.equivFin B).symm
  let width := f ⟨1,by simp⟩
  let wcontact := fun r=>pointSideColumn cut width (comparisonContactLimitCoordinate f r)
  let contact := (Ioo l u).indicator wcontact
  let bound := 2*(cut⁻¹)^2*(width-2*cut)
  have hbound0 : 0 ≤ bound := by dsimp [bound];exact mul_nonneg (by positivity) (sub_nonneg.mpr hwidth)
  have hbound r : ‖contact r‖ ≤ bound := by
    by_cases hr : r∈Ioo l u
    · rw [show contact r=wcontact r from indicator_of_mem hr wcontact]
      exact pointSideColumn_coarse_norm_bound hcut hwidth _
    · rw [show contact r=0 from indicator_of_notMem hr wcontact,norm_zero]
      exact hbound0
  have hcontactNonneg r : 0 ≤ contact r :=
    indicator_nonneg (fun t _=>pointSideColumn_nonneg hwidth _) r
  have hcontactMeas : Measurable contact :=
    (((pointSideColumn_continuous hcut hwidth).comp
      (comparisonContactLimitCoordinate_continuous f)).measurable).indicator measurableSet_Ioo
  let caps : NativeBandFixedCapGeometry m := {
    count := Fintype.card B
    a := fun i=>g.a (e i).val
    z := fun i=>g.z (e i).val
    weight := fun i=>sideSquareColumnLR cut width (cl (e i)) (cr (e i))
    hga := fun i=>g.hga (e i).val
    haz := fun i=>g.haz (e i).val
    hgz := fun i=>g.hgz (e i).val
    haH := fun i=>g.haH (e i).val
    hzH := fun i=>g.hzH (e i).val
    hnegative := fun i=>g.hnegative (e i).val
    hamass := fun i=>g.hamass (e i).val
    hzmass := fun i=>g.hzmass (e i).val
    hweight := fun i=>sideSquareColumnLR_nonneg hwidth _ _
    contact := contact
    hmeas := hcontactMeas
    bound := bound
    hb0 := hbound0
    hbound := hbound
    hnonneg := hcontactNonneg }
  have hfixed : caps.fixed=fixedCapContactWeight (fun t : B=>g.a t.val) (fun t=>g.z t.val)
      (fun t=>sideSquareColumnLR cut width (cl t) (cr t))
      ((Ioo m.ag m.zg ∩ {r | m.H r=0}) ∩ Ioo l u) wcontact := by
    exact fixedCapContactWeight_equiv_contact_restrict e (fun t : B=>g.a t.val) (fun t=>g.z t.val)
      (fun t=>sideSquareColumnLR cut width (cl t) (cr t))
      {r | r∈Ioo m.ag m.zg ∧ m.H r=0} (Ioo l u) wcontact
  let side : NativeBandSideGeometry m s cut := {
    fixedCaps := caps
    K := fun j=>(C j).K
    selected := fun j=>g.bin (s.as j) bins w b
    unit := fun j=>(C j).unit
    x := fun j=>(C j).x
    widths := fun j=>(C j).x (C j).K
    width := width
    hwidth := hwidth
    hwidths := hwidths
    hwidthlim := hwlim
    hstart := fun j=>(C j).start
    hend := fun _=>rfl
    hx := fun j=>(C j).strict_of_width hcut (hwidths j)
    hmass := fun j=>(C j).mass
    hleft := fun j i hi=>g.rows_lower (s.as j) hleft i
      (comparisonConstructedBin_subset m.hc m.hk m.hkc m.hm m.hM (m.n+1) bins m.q m.alpha
        (s.as j) g.a g.z m.H g.D m.ag m.zg w m.capSet b hi)
    hsupport := fun j=>g.column_support (s.as j) (g.bin (s.as j) bins w b)
      (comparisonConstructedBin_subset m.hc m.hk m.hkc m.hm m.hM (m.n+1) bins m.q m.alpha
        (s.as j) g.a g.z m.H g.D m.ag m.zg w m.capSet b)
      (C j).unit (fun v=>sideSquareColumn (C j).x cut ((C j).x (C j).K) v.val)
    hcolumns := by simpa only [hfixed] using hL1 }
  refine ⟨⟨side,fun _=>rfl,rfl,?_,fun j=>(C j).width,fun j=>(C j).classes,fun j=>(C j).order⟩⟩
  intro j
  change (C j).x (C j).K ≤ 1
  rw [(C j).width]
  exact (physicalWindowMass_mem_Icc_one _ (sampleClockSteps_ordered m.q (s.as j) (s.ho j)) _).2

end OAI.SKFluctuations.LaplaceWindowFormalization
