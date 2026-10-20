module

public import ComparisonNativeActualBandConstruction
public import ComparisonNativeCapExhaustionLocal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 7200000
attribute [local instance] Classical.propDecidable

namespace NativeBandModel

def ordinaryCapAdmissible (m : NativeBandModel) (C : Set ℝ) : Prop :=
  m.ag ≤ sInf C ∧ sSup C ≤ m.zg ∧
    m.lo ≤ m.alpha.val.val (sInf C) ∧ m.alpha.val.val (sSup C) ≤ m.hi

def ordinaryCaps (m : NativeBandModel) : Set ℝ :=
  {r | r∈m.capSet ∧ m.ordinaryCapAdmissible (ordConnectedComponent m.capSet r)}

def ordinarySupport (m : NativeBandModel) : Set ℝ :=
  Ioo m.ag m.zg ∩ (m.ordinaryCaps ∪ {r | m.H r=0})

def ordinaryMask (m : NativeBandModel) : ℝ→ℝ :=
  m.ordinarySupport.indicator (fun _=>1)

theorem ordinaryCaps_subset (m : NativeBandModel) : m.ordinaryCaps⊆m.capSet := fun _ h=>h.1

theorem component_subset_ordinaryCaps (m : NativeBandModel) {r : ℝ} (hr : r∈m.ordinaryCaps) :
    ordConnectedComponent m.capSet r⊆m.ordinaryCaps := by
  intro t ht
  refine ⟨ordConnectedComponent_subset ht,?_⟩
  rw [←ordConnectedComponent_eq ht]
  exact hr.2

theorem ordinaryCaps_component (m : NativeBandModel) {r : ℝ} (hr : r∈m.ordinaryCaps) :
    ordConnectedComponent m.ordinaryCaps r=ordConnectedComponent m.capSet r := by
  apply Subset.antisymm
  · intro t ht
    exact (mem_ordConnectedComponent.mp ht).trans m.ordinaryCaps_subset
  · exact subset_ordConnectedComponent (self_mem_ordConnectedComponent.mpr hr.1)
      (m.component_subset_ordinaryCaps hr)

theorem ordinaryCaps_open (m : NativeBandModel) : IsOpen m.ordinaryCaps := by
  rw [isOpen_iff_forall_mem_open]
  intro r hr
  exact ⟨ordConnectedComponent m.capSet r,m.component_subset_ordinaryCaps hr,
    wholeCap_component_isOpen m.hopen r,self_mem_ordConnectedComponent.mpr hr.1⟩

theorem ordinaryCaps_band (m : NativeBandModel) : m.ordinaryCaps⊆Icc m.ag m.zg := by
  intro r hr
  have hp := wholeCap_component_endpoints m.hopen
    (fun r hr=>(m.hcapSet hr).1.le |> fun h=>⟨h,(m.hcapSet hr).2.le⟩) hr.1
  exact ⟨hr.2.1.trans hp.2.1.le,hp.2.2.1.le.trans hr.2.2.1⟩

theorem ordinaryCaps_unit (m : NativeBandModel) {r : ℝ} (hr : r∈m.ordinaryCaps) :
    wholeUnit m.capSet r=ordConnectedComponent m.ordinaryCaps r := by
  rw [m.ordinaryCaps_component hr]
  simp only [wholeUnit,ite_eq_left hr.1]

theorem thermal_integrable (m : NativeBandModel) : IntegrableOn m.thermal (Icc (0:ℝ) 1) := by
  have had := comparisonVariableEndpoint_clocks_admissible m.hc m.hk m.hkc m.hm m.hM
    m.b m.h m.hd.ne' m.hlam.le m.hlb m.hb m.hh m.hh0 m.alpha
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
    (physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1))

end NativeBandModel

namespace NativeBandRetainedCaps

theorem canonical_ordered {m : NativeBandModel} (g : NativeBandRetainedCaps m) (j : ℕ) :
    MassOrdered 0 (g.canonical j) := by
  apply finiteCutMasses_ordered
  apply finiteBoundaryMassNodes_bound
  intro d hd
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hd
  exact (m.alpha.val.property.1 r).2

theorem canonical_end {m : NativeBandModel} (g : NativeBandRetainedCaps m) (j : ℕ) :
    partitionEnd 0 (g.canonical j)=1 := by
  apply finiteCutMasses_end
  apply finiteBoundaryMassNodes_bound
  intro d hd
  obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hd
  exact (m.alpha.val.property.1 r).2

end NativeBandRetainedCaps

theorem exists_nativeOrdinaryRetainedCaps (m : NativeBandModel)
    (F : Finset (ordConnectedSection m.ordinaryCaps)) :
    ∃g : NativeBandRetainedCaps m,g.fullSupport=
      Ioo m.ag m.zg ∩ NativeSelectedMask.fixedSupport
        (NativeCapExhaustion.left m.ordinaryCaps F) (NativeCapExhaustion.right m.ordinaryCaps F) m.H := by
  let e : Fin (Fintype.card F)≃F := (Fintype.equivFin F).symm
  let a := fun i=>NativeCapExhaustion.left m.ordinaryCaps F (e i)
  let z := fun i=>NativeCapExhaustion.right m.ordinaryCaps F (e i)
  have hrep i : (e i).val.val∈m.ordinaryCaps := ordConnectedSection_subset (e i).val.property
  have hp i := wholeCap_component_endpoints m.ordinaryCaps_open m.ordinaryCaps_band (hrep i)
  have hcomp i : ordConnectedComponent m.ordinaryCaps (e i).val.val=Ioo (a i) (z i) :=
    (hp i).2.2.2.2.1
  have hmem i {r : ℝ} (hr : r∈Ioo (a i) (z i)) : r∈m.ordinaryCaps :=
    ordConnectedComponent_subset ((hcomp i).symm ▸ hr)
  have hends i : m.H (a i)=0 ∧ (m.H (z i)=0 ∨ z i=1) := by
    have hh := m.hcomponent _ (hrep i).1
    simpa only [a,z,NativeCapExhaustion.left,NativeCapExhaustion.right,
      m.ordinaryCaps_component (hrep i)] using hh
  have hmass i : m.lo≤ m.alpha.val.val (a i) ∧ m.alpha.val.val (z i)≤ m.hi := by
    have hh := (hrep i).2.2.2
    simpa only [a,z,NativeCapExhaustion.left,NativeCapExhaustion.right,
      m.ordinaryCaps_component (hrep i)] using hh
  let D : Finset ℝ := Finset.univ.image a ∪ Finset.univ.image z
  have hD d (hd : d∈D) : d∈Icc (0:ℝ) 1 := by
    rcases Finset.mem_union.mp hd with hd|hd
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
      exact ⟨m.hag.le.trans (hp i).1,((hp i).2.1.trans (hp i).2.2.1).le.trans ((hp i).2.2.2.1.trans m.hzg)⟩
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
      exact ⟨m.hag.le.trans ((hp i).1.trans ((hp i).2.1.trans (hp i).2.2.1).le),
        (hp i).2.2.2.1.trans m.hzg⟩
  have hDout d (hd : d∈D) : d∉m.ordinaryCaps := by
    rcases Finset.mem_union.mp hd with hd|hd
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
      exact (hp i).2.2.2.2.2.1
    · obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
      exact (hp i).2.2.2.2.2.2
  let g : NativeBandRetainedCaps m := {
    count := Fintype.card F
    a := a
    z := z
    hga := fun i=>(hp i).1
    haz := fun i=>(hp i).2.1.trans (hp i).2.2.1
    hgz := fun i=>(hp i).2.2.2.1
    haH := fun i=>(hends i).1
    hzH := fun i=>(hends i).2
    hnegative := fun i r hr=>m.hnegative r (hmem i hr).1
    hamass := fun i=>(hmass i).1
    hzmass := fun i=>(hmass i).2
    hwhole := fun i r hr=>by
      rw [m.ordinaryCaps_unit (hmem i hr),←hcomp i]
      have hrc : r∈ordConnectedComponent m.ordinaryCaps (e i).val.val := (hcomp i).symm ▸ hr
      exact (ordConnectedComponent_eq hrc).symm
    hdisjoint := fun i j hij=>(NativeCapExhaustion.endpoints m.ordinaryCaps_open m.ordinaryCaps_band F).2
      (fun he=>hij (e.injective he))
    D := D
    hD := hD
    haD := fun i=>Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    hzD := fun i=>Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    hinterior := fun i d hd hr=>hDout d hd (hmem i hr) }
  refine ⟨g,?_⟩
  apply congrArg (fun A : Set ℝ=>Ioo m.ag m.zg ∩ A)
  ext r
  change ((∃i,r∈Ioo (a i) (z i)) ∨ m.H r=0) ↔
    ((∃t:F,r∈Ioo (NativeCapExhaustion.left m.ordinaryCaps F t)
      (NativeCapExhaustion.right m.ordinaryCaps F t)) ∨ m.H r=0)
  constructor
  · rintro (⟨i,hi⟩|hH)
    · exact Or.inl ⟨e i,hi⟩
    · exact Or.inr hH
  · rintro (⟨t,ht⟩|hH)
    · exact Or.inl ⟨e.symm t,by simpa only [a,z,e.apply_symm_apply] using ht⟩
    · exact Or.inr hH

theorem actual_full_ordinary_band_budget
    (m : NativeBandModel) (bins : ℕ) (hbins : 0<bins)
    {cut w : ℝ} (hcut : 0<cut) (hw : 0<w) (hRange : m.Q^2*m.y ≤ (bins:ℝ)*w)
    (hleft : m.cutRadius ≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤ m.bandMass)
    (hlog : Real.log (1/cut) ≤ m.Lside)
    (hraw : ∀as,MassOrdered 0 as→partitionEnd 0 as=1→
      physicalRawRatio (m.n+1) m.l (sampleClockSteps m.q 0 as) 0 m.xs
        (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id ≤ m.Q) :
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
  have h := actual_constructed_retained_band_budget m g bins hbins hcut hw hRange
    hleft hupper hband hlog (fun j=>hraw _ (g.canonical_ordered j) (g.canonical_end j))
  simpa only [NativeBandRetainedCaps.fullMask,hg,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le zero_le_one] using h

theorem actual_full_ordinary_band_optimized
    (m : NativeBandModel) {cut : ℝ} (hcut : 0<cut)
    (hleft : m.cutRadius ≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤ m.bandMass)
    (hlog : Real.log (1/cut) ≤ m.Lside)
    (hraw : ∀as,MassOrdered 0 as→partitionEnd 0 as=1→
      physicalRawRatio (m.n+1) m.l (sampleClockSteps m.q 0 as) 0 m.xs
        (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id ≤ m.Q) :
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
  have hfull := actual_full_ordinary_band_budget m bins (by omega) hcut hcover.1 hcover.2
    hleft hupper hband hlog hraw
  exact ⟨bins,hbins,hsize,by linarith⟩

theorem actual_full_ordinary_band_explicit
    (m : NativeBandModel) {cut : ℝ} (hcut : 0<cut)
    (hleft : m.cutRadius ≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤ m.bandMass)
    (hlog : Real.log (1/cut) ≤ m.Lside)
    (hraw : ∀as,MassOrdered 0 as→partitionEnd 0 as=1→
      physicalRawRatio (m.n+1) m.l (sampleClockSteps m.q 0 as) 0 m.xs
        (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id ≤ m.Q) :
    (∫v in 0..1,m.ordinaryMask (m.R v)*m.thermal v) ≤
      nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*m.bandMass*
        (2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
          3/(m.P*m.bandMass^2)+m.D0^2+m.reverse m.D0)+
      18*(((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*cut := by
  obtain ⟨bins,_,hbins,hbound⟩ := actual_full_ordinary_band_optimized m hcut hleft hupper hband hlog hraw
  have hcost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbins (show (0:ℝ)≤18 by norm_num)) hcut.le
  linarith

theorem actual_full_ordinary_band_polynomial_cut
    (m : NativeBandModel) (C : ℝ)
    (hleft : m.cutRadius ≤ m.ag) (hupper : m.xs+m.alpha.val.val m.zg ≤ m.y)
    (hband : m.alpha.val.val m.zg-m.alpha.val.val m.ag ≤ m.bandMass)
    (hlog : C*Real.log m.N ≤ m.Lside)
    (hraw : ∀as,MassOrdered 0 as→partitionEnd 0 as=1→
      physicalRawRatio (m.n+1) m.l (sampleClockSteps m.q 0 as) 0 m.xs
        (Measure.pi fun a=>gaussianReal 0 (m.q 0 a)) id measurable_id ≤ m.Q) :
    (∫v in 0..1,m.ordinaryMask (m.R v)*m.thermal v) ≤
      nativeBinScaleLoss m.Lside m.AS m.AC m.bandMass m.rho*m.bandMass*
        (2*((m.Q^2*m.y)/(m.P*m.bandMass^2))^((2:ℝ)/3)+
          3/(m.P*m.bandMass^2)+m.D0^2+m.reverse m.D0)+
      18*(((m.Q^2*m.y)^2*m.P*m.bandMass^2)^((1:ℝ)/3)+2)*m.N^(-C) := by
  have hN : 0< m.N := zero_lt_one.trans_le m.hN
  apply actual_full_ordinary_band_explicit m (Real.rpow_pos_of_pos hN _) hleft hupper hband _ hraw
  calc
    Real.log (1/m.N^(-C))=C*Real.log m.N := by
      rw [one_div,Real.log_inv,Real.log_rpow hN]
      ring
    _ ≤ m.Lside := hlog

end OAI.SKFluctuations.LaplaceWindowFormalization
