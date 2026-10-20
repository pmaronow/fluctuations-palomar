module

public import ComparisonShiftedNativeMaskColumns
public import ComparisonShiftedNativeRadiusWeights
public import ComparisonShiftedNativeThermalGeometry
public import ComparisonNativeWeightedDefectLimit
public import ComparisonActualHighWallSelectedLedger

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem radiusCellEnergyDensity_comp_high_coefficients {start : ℝ}
    (as : List PositiveMass) (ho : MassOrdered start as) (C : ℕ→ℝ)
    (hhigh : ∀i,C i≠0→m.u0 ≤ partitionPoint start as i)
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    radiusCellEnergyDensity m.R start as C (m.R u)=radiusCellEnergyDensity id start as C u := by
  induction as generalizing start C with
  | nil=>rfl
  | cons a as ih=>
    have htail:=ih ho.2.2 (fun i=>C (i+1)) (fun i hi=>by
      simpa only [partitionPoint,partitionValues] using hhigh (i+1) hi)
    by_cases hC:C 0=0
    · simp only [radiusCellEnergyDensity,hC,indicator_zero,zero_add,htail]
    have hstart : m.u0 ≤ start:=by
      simpa only [partitionPoint,partitionValues_zero,id_eq] using hhigh 0 hC
    have hs : start∈Icc m.u0 1:=⟨hstart,(massOrdered_bounds ho).2⟩
    have ha : a.val∈Icc m.u0 1:=⟨hstart.trans ho.2.1,(massOrdered_bounds ho.2.2).2⟩
    have hmem : m.R u∈Ioc (m.R start) (m.R a.val) ↔ u∈Ioc (id start) (id a.val) := by
      by_cases huu:m.u0 ≤ u
      · exact and_congr (m.R_strictMonoOn.lt_iff_lt hs ⟨huu,hu.2⟩)
          (m.R_strictMonoOn.le_iff_le ⟨huu,hu.2⟩ ha)
      · have hu0 : u < m.u0:=lt_of_not_ge huu
        have hnot : u∉Ioc (id start) (id a.val):=fun h=>not_lt_of_ge (hstart.trans h.1.le) hu0
        have hnotR : m.R u∉Ioc (m.R start) (m.R a.val) := by
          rw [m.R_before hu0.le]
          exact fun h=>not_lt_of_ge (m.R_bounds start).1 h.1
        simp only [hnot,hnotR]
    simp only [radiusCellEnergyDensity,htail]
    by_cases hr:u∈Ioc (id start) (id a.val)
    · rw [indicator_of_mem hr,indicator_of_mem (hmem.mpr hr)]
    · rw [indicator_of_notMem hr,indicator_of_notMem (fun h=>hr (hmem.mp h))]

theorem mass_mask_radius_ae
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ)
    (hhigh : ∀i∈J,m.u0 ≤ partitionPoint 0 as i.val) :
    ∀ᵐu∂volume.restrict (Icc (0:ℝ) 1),
      massStepFunction as (nativeSelectedColumn J unit col) u=m.unitColumn as J unit col (m.R u) := by
  have hid:=massStepFunction_eq_radiusCellEnergyDensity_ae as ho he (nativeSelectedColumn J unit col)
  filter_upwards [ae_restrict_of_ae hid,ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne (0:ℝ)),ae_restrict_of_ae (volume.ae_ne (1:ℝ))]
    with u hdu hu hu0 hu1
  rw [hdu ⟨lt_of_le_of_ne hu.1 hu0.symm,lt_of_le_of_ne hu.2 hu1⟩]
  exact (m.radiusCellEnergyDensity_comp_high_coefficients as ho _
    (m.nativeColumn_high_support as J unit col hhigh) hu).symm

theorem binary_mass_radius_L1_eq
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0 ≤ partitionPoint 0 as i.val)
    {ag zg : ℝ} (hag : m.rmin<ag) (F : Set ℝ) (hF : MeasurableSet F) (hFD : F⊆Ioo ag zg) :
    (∫u in 0..1,|nativeSelectedMassMask m.q as J u-F.indicator (fun _=>1) (m.R u)|)=
      ∫r in Icc m.rmin 1,|deriv m.alpha.val.val r*m.unitColumn as J (fun _=>(0:Fin 1)) (fun _=>1) r-
        deriv m.alpha.val.val r*F.indicator (fun _=>1) r| := by
  let col:=m.unitColumn as J (fun _=>(0:Fin 1)) (fun _=>1)
  let fixed:=F.indicator (fun _ : ℝ=>(1:ℝ))
  let G:=fun r=>|col r-fixed r|
  have hmask : (∫u in 0..1,|nativeSelectedMassMask m.q as J u-fixed (m.R u)|)=
      ∫u in 0..1,G (m.R u) := by
    rw [intervalIntegral.integral_of_le zero_le_one,intervalIntegral.integral_of_le zero_le_one]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self
      (m.mass_mask_radius_ae as ho he J (fun _=>(0:Fin 1)) (fun _=>1) hhigh)] with u hu
    change |massStepFunction as (nativeSelectedColumn J (fun _=>(0:Fin 1)) (fun _=>1)) u-fixed (m.R u)|=_
    rw [hu]
  have hcolB r : col r∈Icc (0:ℝ) 1:=by
    apply radiusCellEnergyDensity_mem_Icc_bound _ m.R_monotone as ho _ (by norm_num)
    intro i
    unfold nativeSelectedColumn
    split_ifs <;> norm_num
  have hfixB r : fixed r∈Icc (0:ℝ) 1:=by
    simp only [fixed,Set.indicator_apply]
    split_ifs <;> norm_num
  have hGmeas : Measurable (fun u=>G (m.R u)):=
    (((m.unitColumn_measurable as J _ _).sub (measurable_const.indicator hF)).abs).comp m.R_continuous.measurable
  have hGb u : ‖G (m.R u)‖ ≤ (1:ℝ):=by
    rw [Real.norm_eq_abs,abs_abs]
    exact (abs_sub_le_iff.mpr ⟨by linarith [(hcolB (m.R u)).2,(hfixB (m.R u)).1],
      by linarith [(hfixB (m.R u)).2,(hcolB (m.R u)).1]⟩)
  have hGi : IntervalIntegrable (fun u=>G (m.R u)) volume 0 1 := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr
    have hone : IntegrableOn (fun _ : ℝ=>(1:ℝ)) (Icc (0:ℝ) 1):=integrableOn_const (by simp)
    simpa only [IntegrableOn,mul_one] using hone.bdd_mul
      hGmeas.stronglyMeasurable.aestronglyMeasurable.restrict (ae_of_all _ hGb)
  have hi0 : IntervalIntegrable (fun u=>G (m.R u)) volume 0 m.u0:=hGi.mono_set (by rw [uIcc_of_le zero_le_one,uIcc_of_le m.hu.1];exact Icc_subset_Icc le_rfl m.hu.2)
  have hi1 : IntervalIntegrable (fun u=>G (m.R u)) volume m.u0 1:=hGi.mono_set (by rw [uIcc_of_le zero_le_one,uIcc_of_le m.hu.2];exact Icc_subset_Icc m.hu.1 le_rfl)
  have hcol0 : col m.rmin=0:=radiusCellEnergyDensity_eq_zero_of_le m.R m.R_monotone as ho _ (m.R_bounds 0).1
  have hF0 : m.rmin∉F:=fun hr=>not_lt_of_ge hag.le (hFD hr).1
  have hlow : (∫u in (0:ℝ)..m.u0,G (m.R u))=0 := by
    have heq : (∫u in (0:ℝ)..m.u0,G (m.R u))=∫u in (0:ℝ)..m.u0,(0:ℝ):=
      intervalIntegral.integral_congr_Ioo_of_le m.hu.1 (fun u hu=>by
        rw [m.R_before hu.2.le]
        simp only [G,hcol0,fixed,indicator_of_notMem hF0,sub_zero,abs_zero])
    rw [heq]
    simp
  rw [hmask,←intervalIntegral.integral_add_adjacent_intervals hi0 hi1,hlow,zero_add,
    m.mass_radius_substitution]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  dsimp only [G]
  rw [m.R_inverse hr,←mul_sub,abs_mul,abs_of_nonneg m.alpha.val.property.2.deriv_nonneg]

theorem binary_mass_L1_of_support_eventually
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (hJ : ∀j,∀i∈J j,i.val<(as j).length)
    (hhigh : ∀j,∀i∈J j,m.u0 ≤ partitionPoint 0 (as j) i.val)
    {ag zg : ℝ} (hag : m.rmin<ag) (hzg : zg ≤ 1)
    (hleft : ∀j,∀i∈J j,ag ≤ m.R (partitionPoint 0 (as j) i.val))
    (hright : ∀j,∀i∈J j,m.R (partitionPoint 0 (as j) (i.val+1)) ≤ zg)
    (F : Set ℝ) (hF : MeasurableSet F) (hFD : F⊆Ioo ag zg)
    (hmem : ∀ᵐr∂volume.restrict (Ioo ag zg),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i)) (J j) ↔r∈F)) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask m.q (as j) (J j) u-
      F.indicator (fun _=>1) (m.R u)|) atTop (𝓝 0) := by
  have ht:=m.binary_density_L1_of_support_eventually as ho (fun _=>1) J (fun _ _=>(0:Fin 1))
    hJ hag hzg F hF hmem
  have heq j : (∫r in Icc m.rmin 1,
      |deriv m.alpha.val.val r*m.unitColumn (as j) (J j) (fun _=>(0:Fin 1)) (fun _=>1) r-
        deriv m.alpha.val.val r*F.indicator (fun _=>1) r|)=
      ∫r in Ioo ag zg,
      |deriv m.alpha.val.val r*m.unitColumn (as j) (J j) (fun _=>(0:Fin 1)) (fun _=>1) r-
        deriv m.alpha.val.val r*F.indicator (fun _=>1) r| := by
    let g:=fun r=>|deriv m.alpha.val.val r*m.unitColumn (as j) (J j) (fun _=>(0:Fin 1)) (fun _=>1) r-
      deriv m.alpha.val.val r*F.indicator (fun _=>1) r|
    have hge : g=ᵐ[volume](Ioo ag zg).indicator g:=by
      filter_upwards [m.unitColumn_support_band (as j) (J j) (fun _=>(0:Fin 1)) (fun _=>1)
        (hleft j) (hright j)] with r hr
      by_cases hri:r∈Ioo ag zg
      · rw [indicator_of_mem hri]
      · have hrF:r∉F:=fun hh=>hri (hFD hh)
        rw [indicator_of_notMem hri]
        simp only [g,hr hri,indicator_of_notMem hrF,mul_zero,sub_self,abs_zero]
    change (∫r in Icc m.rmin 1,g r)=∫r in Ioo ag zg,g r
    have hEq : (∫r in Icc m.rmin 1,g r)=∫r in Icc m.rmin 1,(Ioo ag zg).indicator g r:=
      integral_congr_ae (ae_restrict_of_ae hge)
    rw [hEq,integral_indicator measurableSet_Ioo,
      Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr
        (Ioo_subset_Icc_self.trans (Icc_subset_Icc hag.le hzg))]
  simp_rw [m.binary_mass_radius_L1_eq _ (ho _) (he _) _ (hhigh _) hag F hF hFD,heq]
  exact ht

theorem binary_thermal_pullback {ag zg : ℝ} (hag : m.rmin<ag) (hzg : zg ≤ 1)
    (F : Set ℝ) (hF : MeasurableSet F) (hFD : F⊆Ioo ag zg) (G : ℝ→ℝ)
    (hGi : IntervalIntegrable (fun u=>F.indicator (fun _=>1) (m.R u)*G u) volume 0 1) :
    (∫u in 0..1,F.indicator (fun _=>1) (m.R u)*G u)=
      ∫r in F,deriv m.alpha.val.val r*G (m.alpha.val.val r) := by
  let integrand:=fun u=>F.indicator (fun _ : ℝ=>(1:ℝ)) (m.R u)*G u
  have hi0 : IntervalIntegrable integrand volume 0 m.u0:=hGi.mono_set (by
    rw [uIcc_of_le zero_le_one,uIcc_of_le m.hu.1];exact Icc_subset_Icc le_rfl m.hu.2)
  have hi1 : IntervalIntegrable integrand volume m.u0 1:=hGi.mono_set (by
    rw [uIcc_of_le zero_le_one,uIcc_of_le m.hu.2];exact Icc_subset_Icc m.hu.1 le_rfl)
  have hF0 : m.rmin∉F:=fun hr=>not_lt_of_ge hag.le (hFD hr).1
  have hlow : (∫u in (0:ℝ)..m.u0,integrand u)=0 := by
    have heq : (∫u in (0:ℝ)..m.u0,integrand u)=∫u in (0:ℝ)..m.u0,(0:ℝ):=
      intervalIntegral.integral_congr_Ioo_of_le m.hu.1 (fun u hu=>by
        dsimp only [integrand]
        rw [m.R_before hu.2.le,indicator_of_notMem hF0,zero_mul])
    rw [heq]
    simp
  change (∫u in (0:ℝ)..1,integrand u)=_
  rw [←intervalIntegral.integral_add_adjacent_intervals hi0 hi1,hlow,zero_add,m.mass_radius_substitution]
  calc
    _=∫r in Icc m.rmin 1,F.indicator (fun r=>deriv m.alpha.val.val r*G (m.alpha.val.val r)) r := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      dsimp only [integrand]
      rw [m.R_inverse hr]
      by_cases hrF:r∈F <;> simp [hrF]
    _=_:=by
      rw [integral_indicator hF,Measure.restrict_restrict hF,
        inter_eq_left.mpr (hFD.trans (Ioo_subset_Icc_self.trans (Icc_subset_Icc hag.le hzg)))]

def selectedDefect (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) : ℝ :=
  let steps:=sampleClockSteps m.q 0 as
  ∑i,physicalSelectedCellMass steps J i*actualCutReplicaDefect (m.n+1) steps (m.q 0) i.val
    (physicalPathSecondMoment (m.n+1) steps (m.q 0) i.val)

theorem selectedDefect_tendsto_radius
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (hJ : ∀j,∀i∈J j,i.val<(as j).length)
    (hhigh : ∀j,∀i∈J j,m.u0 ≤ partitionPoint 0 (as j) i.val)
    {ag zg : ℝ} (hag : m.rmin<ag) (hzg : zg ≤ 1)
    (hleft : ∀j,∀i∈J j,ag ≤ m.R (partitionPoint 0 (as j) i.val))
    (hright : ∀j,∀i∈J j,m.R (partitionPoint 0 (as j) (i.val+1)) ≤ zg)
    (F : Set ℝ) (hF : MeasurableSet F) (hFD : F⊆Ioo ag zg)
    (hmem : ∀ᵐr∂volume.restrict (Ioo ag zg),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i)) (J j) ↔r∈F)) :
    Tendsto (fun j=>m.selectedDefect (as j) (J j)) atTop
      (𝓝 (∫r in F,deriv m.alpha.val.val r*m.thermal (m.alpha.val.val r))) := by
  let fixed:=fun u=>F.indicator (fun _ : ℝ=>(1:ℝ)) (m.R u)
  have hfixed : Measurable fixed:=(measurable_const.indicator hF).comp m.R_continuous.measurable
  have hfb u (_hu : u∈Ioc (0:ℝ) 1) : fixed u∈Icc (0:ℝ) 1:=by
    simp only [fixed,Set.indicator_apply]
    split_ifs <;> norm_num
  have hL1:=m.binary_mass_L1_of_support_eventually as ho he J hJ hhigh hag hzg
    hleft hright F hF hFD hmem
  have ht:=actual_selected_centered_defect_tendsto_native_path m.n m.bf m.hf m.hbf m.hhf
    as mesh ho he hmesh hlim J fixed hfixed hfb hL1
  have hGi:=intervalIntegrable_bounded_measurable_mul hfixed (by norm_num : (0:ℝ) ≤ 1) hfb
    (physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf m.hbf m.hhf)
  rw [m.binary_thermal_pullback hag hzg F hF hFD _ hGi] at ht
  exact ht

end ShiftedNativeBandModel

namespace ActualHighWallOverlapMinimum.SelectedMasterFamily
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential} {ι : Type*} [Fintype ι] {c : ι→ShiftedCapInterval a P}
variable {Dcuts : Finset ℝ} {ag zg w cut Q : ℝ} {bins ell : ℕ} {hbins : 0<bins}
variable (M : SelectedMasterFamily a P c Dcuts ag zg bins hbins w cut ell Q)

abbrev fullRows (j : ℕ):=P.retainedRows c Dcuts ag zg (M.as j)
abbrev fullLimitSupport : Set ℝ:=let _:=M;P.retainedSupport c ag zg
def binLimitSupport (b : Fin bins) : Set ℝ:=M.fullLimitSupport∩Ioo (M.l b).val (M.u b).val
def keptRows (j : ℕ):=nativeKeptRows (M.bin j) M.keep
def keptLimitSupport : Set ℝ:=nativeKeptSupport M.binLimitSupport M.keep
def selectedLimitSupport {B : ℕ} (label : Fin B→Fin bins) : Set ℝ:=
  nativeKeptSupport (fun b=>M.binLimitSupport (label b)) (fun _=>true)
def limitThermal (F : Set ℝ) : ℝ:=let _:=M;∫u in 0..1,F.indicator (fun _=>1)
  (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u
def fullDefect (j : ℕ) : ℝ:=a.shiftedNativeModel.selectedDefect (M.as j) (M.fullRows j)
def keptDefect (j : ℕ) : ℝ:=a.shiftedNativeModel.selectedDefect (M.as j) (M.keptRows j)

theorem binLimitSupport_measurable (hag : a.data.rmin<ag) (hzg : zg ≤ 1) (b : Fin bins) :
    MeasurableSet (M.binLimitSupport b):=
  (P.retainedSupport_measurable c hag.le hzg).inter measurableSet_Ioo

theorem keptLimitSupport_measurable (hag : a.data.rmin<ag) (hzg : zg ≤ 1) :
    MeasurableSet M.keptLimitSupport:=
  nativeKeptSupport_measurable _ _ (M.binLimitSupport_measurable hag hzg)

omit [Fintype ι] in
theorem selectedLimitSupport_eq_iUnion {B : ℕ} (label : Fin B→Fin bins) :
    M.selectedLimitSupport label=⋃b,M.fullLimitSupport∩Ioo (M.l (label b)).val (M.u (label b)).val := by
  ext r
  simp [selectedLimitSupport,nativeKeptSupport,binLimitSupport]

omit [Fintype ι] in
private theorem original_selection_convergence
    (hag : a.data.rmin<ag) (hzg : zg ≤ 1)
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)).length+1)))
    (hsub : ∀j,J j⊆M.fullRows j)
    (F : Set ℝ) (hF : MeasurableSet F) (hFD : F⊆Ioo ag zg)
    (hgeom : ∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>a.shiftedNativeModel.R
        (partitionPoint 0 (M.as j) i)) (J j) ↔r∈F)) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask a.shiftedNativeModel.q (M.as j) (J j) u-
      F.indicator (fun _=>1) (a.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto (fun j=>a.shiftedNativeModel.selectedDefect (M.as j) (J j)) atTop (𝓝 (M.limitThermal F)) := by
  let m:=a.shiftedNativeModel
  have hdata j i (hi:i∈J j):=(P.retainedRows_mem c Dcuts ag zg (M.as j) i).mp (hsub j hi)
  have hmem:=ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo (a.data.hrbounds.1.le.trans hag.le) hzg) hgeom
  have hJ j i (hi:i∈J j):=(hdata j i hi).1
  have hhigh j i (hi:i∈J j):=(hdata j i hi).2.2.2.1
  have hleft j i (hi:i∈J j):=(hdata j i hi).2.2.2.2.1
  have hright j i (hi:i∈J j):=(hdata j i hi).2.2.2.2.2
  refine ⟨m.binary_mass_L1_of_support_eventually M.as M.ho M.he J hJ hhigh hag hzg
    hleft hright F hF hFD hmem,?_⟩
  have ht:=m.selectedDefect_tendsto_radius M.as M.mesh M.ho M.he M.hmesh M.mesh_tendsto
    J hJ hhigh hag hzg hleft hright F hF hFD hmem
  have hw : Measurable (fun u=>F.indicator (fun _ : ℝ=>(1:ℝ)) (m.R u)):=
    (measurable_const.indicator hF).comp m.R_continuous.measurable
  have hb u (_hu:u∈Ioc (0:ℝ) 1) : F.indicator (fun _ : ℝ=>(1:ℝ)) (m.R u)∈Icc (0:ℝ) 1:=by
    simp only [Set.indicator_apply]
    split_ifs <;> norm_num
  have hi:=intervalIntegrable_bounded_measurable_mul hw (by norm_num : (0:ℝ) ≤ 1) hb
    (physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf m.hbf m.hhf)
  unfold limitThermal
  rw [m.binary_thermal_pullback hag hzg F hF hFD _ hi]
  exact ht

theorem full_selection_convergence (hag : a.data.rmin<ag) (hzg : zg ≤ 1) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask a.shiftedNativeModel.q (M.as j) (M.fullRows j) u-
      M.fullLimitSupport.indicator (fun _=>1) (a.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto M.fullDefect atTop (𝓝 (M.limitThermal M.fullLimitSupport)) :=
  M.original_selection_convergence hag hzg M.fullRows (fun _=>Subset.refl _)
    M.fullLimitSupport (P.retainedSupport_measurable c hag.le hzg) (fun _ h=>h.1)
    (P.retainedRows_support_ae c Dcuts M.as M.mesh M.ho M.he M.hmesh M.mesh_nonneg M.mesh_tendsto hag hzg)

theorem bin_selection_convergence (hag : a.data.rmin<ag) (hzg : zg ≤ 1) (b : Fin bins) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask a.shiftedNativeModel.q (M.as j) (M.bin j b) u-
      (M.binLimitSupport b).indicator (fun _=>1) (a.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto (fun j=>a.shiftedNativeModel.selectedDefect (M.as j) (M.bin j b)) atTop
      (𝓝 (M.limitThermal (M.binLimitSupport b))) :=
  M.original_selection_convergence hag hzg (fun j=>M.bin j b)
    (fun j=>P.retainedBin_subset c Dcuts ag zg (M.as j) bins w b)
    (M.binLimitSupport b) (M.binLimitSupport_measurable hag hzg b) (fun _ h=>h.1.1) (M.geometry b)

theorem kept_selection_convergence (hag : a.data.rmin<ag) (hzg : zg ≤ 1) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask a.shiftedNativeModel.q (M.as j) (M.keptRows j) u-
      M.keptLimitSupport.indicator (fun _=>1) (a.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto M.keptDefect atTop (𝓝 (M.limitThermal M.keptLimitSupport)) := by
  apply M.original_selection_convergence hag hzg M.keptRows _ M.keptLimitSupport
    (M.keptLimitSupport_measurable hag hzg) _ _
  · intro j i hi
    obtain ⟨b,_,hb⟩:=(nativeKeptRows_mem (M.bin j) M.keep i).mp hi
    exact P.retainedBin_subset c Dcuts ag zg (M.as j) bins w b hb
  · rintro r ⟨b,_,hr⟩
    exact hr.1.1
  · filter_upwards [ae_all_iff.mpr M.geometry] with r hr
    filter_upwards [Filter.eventually_all.mpr hr] with j hj
    dsimp only [keptRows,keptLimitSupport]
    rw [nativeKeptRows_support]
    exact exists_congr (fun b=>and_congr_right (fun _=>hj b))

theorem selected_selection_convergence (hag : a.data.rmin<ag) (hzg : zg ≤ 1)
    {B : ℕ} (label : Fin B→Fin bins) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask a.shiftedNativeModel.q (M.as j) (M.selected label j) u-
      (M.selectedLimitSupport label).indicator (fun _=>1) (a.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto (M.defect label) atTop (𝓝 (M.limitThermal (M.selectedLimitSupport label))) := by
  apply M.original_selection_convergence hag hzg (M.selected label) _ (M.selectedLimitSupport label)
    (nativeKeptSupport_measurable _ _ (fun b=>M.binLimitSupport_measurable hag hzg (label b))) _ _
  · intro j i hi
    obtain ⟨b,_,hb⟩:=Finset.mem_biUnion.mp hi
    exact P.retainedBin_subset c Dcuts ag zg (M.as j) bins w (label b) hb
  · rintro r ⟨b,_,hr⟩
    exact hr.1.1
  · filter_upwards [ae_all_iff.mpr (fun b : Fin B=>M.geometry (label b))] with r hr
    filter_upwards [Filter.eventually_all.mpr hr] with j hj
    change (r∈NativeSelectedMask.finiteSupport (fun i=>a.shiftedNativeModel.R (partitionPoint 0 (M.as j) i))
      (Finset.univ.biUnion (fun b=>M.bin j (label b))) ↔r∈M.selectedLimitSupport label)
    have he : Finset.univ.biUnion (fun b=>M.bin j (label b))=
        nativeKeptRows (fun b=>M.bin j (label b)) (fun _=>true):=by simp [nativeKeptRows]
    rw [he,nativeKeptRows_support]
    exact exists_congr (fun b=>and_congr_right (fun _=>hj b))

theorem defect_tendsto (hag : a.data.rmin<ag) (hzg : zg ≤ 1)
    {B : ℕ} (label : Fin B→Fin bins) :
    Tendsto (M.defect label) atTop (𝓝 (M.limitThermal (M.selectedLimitSupport label))) :=
  (M.selected_selection_convergence hag hzg label).2

omit [Fintype ι] in
theorem discarded_mass_le (hcut : 0 ≤ cut) (j : ℕ) :
    physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)) 0 (M.fullRows j)-
      physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)) 0 (M.keptRows j) ≤
        2*(bins:ℝ)*cut := by
  have H:=native_height_bins_coordinate_mass (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j))
    (fun i=>physicalPathSecondMoment (n+1) (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j))
      (a.shiftedNativeModel.q 0) i.val) (M.fullRows j)
    (firstWholeUnitCell P.negativeSet (a.shiftedNativeModel.rowRadius (M.as j))) w hbins M.keep
    (a.shiftedNativeModel.rowRadius (M.as j)) P.negativeSet (M.co j)
  have HE:=H.2.2
  change physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)) 0 (M.fullRows j)-
    physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)) 0 (M.keptRows j)=
      ∑b,if M.keep b then 0 else M.width j b at HE
  rw [HE]
  exact constructed_stable_small_bin_ledger M.width M.keep hcut M.cutoffs j

omit [Fintype ι] in
theorem fullDefect_le_kept_add (hcut : 0 ≤ cut) (j : ℕ) :
    M.fullDefect j ≤ M.keptDefect j+2*(bins:ℝ)*cut := by
  let steps:=sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)
  have hs:=sampleClockSteps_ordered a.shiftedNativeModel.q _ (M.ho j)
  have hsub : M.keptRows j⊆M.fullRows j:=by
    intro i hi
    obtain ⟨b,_,hb⟩:=(nativeKeptRows_mem (M.bin j) M.keep i).mp hi
    exact P.retainedBin_subset c Dcuts ag zg (M.as j) bins w b hb
  have H:=(actual_selected_centered_defect_mass_exhaustion (n+1) steps hs
    (a.shiftedNativeModel.q 0) (M.keptRows j) (M.fullRows j) hsub).2
  dsimp only at H
  rw [sum_physicalSelectedCellMass_eq_window,sum_physicalSelectedCellMass_eq_window] at H
  have Hd:=M.discarded_mass_le hcut j
  change M.fullDefect j-M.keptDefect j ≤ _ at H
  linarith

theorem full_thermal_le_kept_add_2_bins_cut (hag : a.data.rmin<ag) (hzg : zg ≤ 1)
    (hcut : 0 ≤ cut) :
    M.limitThermal M.fullLimitSupport ≤ M.limitThermal M.keptLimitSupport+2*(bins:ℝ)*cut :=
  le_of_tendsto_of_tendsto (M.full_selection_convergence hag hzg).2
    ((M.kept_selection_convergence hag hzg).2.add_const (2*(bins:ℝ)*cut))
    (Eventually.of_forall (M.fullDefect_le_kept_add hcut))

omit [Fintype ι] in
theorem keptLimitSupport_eq_selected {B : ℕ} (label : Fin B→Fin bins)
    (hkept : ∀b,M.keep (label b)=true)
    (hcover : ∀b,M.keep b=true→∃i,label i=b) :
    M.keptLimitSupport=M.selectedLimitSupport label := by
  ext r
  constructor
  · rintro ⟨b,hb,hr⟩
    obtain ⟨i,rfl⟩:=hcover b hb
    exact ⟨i,rfl,hr⟩
  · rintro ⟨i,_,hr⟩
    exact ⟨label i,hkept i,hr⟩

theorem full_thermal_le_selected_add_2_bins_cut (hag : a.data.rmin<ag) (hzg : zg ≤ 1)
    (hcut : 0 ≤ cut) {B : ℕ} (label : Fin B→Fin bins)
    (hkept : ∀b,M.keep (label b)=true)
    (hcover : ∀b,M.keep b=true→∃i,label i=b) :
    M.limitThermal M.fullLimitSupport ≤ M.limitThermal (M.selectedLimitSupport label)+2*(bins:ℝ)*cut := by
  rw [←M.keptLimitSupport_eq_selected label hkept hcover]
  exact M.full_thermal_le_kept_add_2_bins_cut hag hzg hcut

omit [Fintype ι] in
theorem row_mass_bounds (j : ℕ)
    (i : Fin ((sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)).length+1)) (hi:i∈M.fullRows j) :
    a.alpha.val.val ag ≤ physicalCutMass 0 (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)) i.val ∧
      physicalCutMass 0 (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)) (i.val+1) ≤ a.alpha.val.val zg := by
  let m:=a.shiftedNativeModel
  have hd:=(P.retainedRows_mem c Dcuts ag zg (M.as j) i).mp hi
  have hiU : partitionPoint 0 (M.as j) i.val∈Icc m.u0 1:=
    ⟨hd.2.2.2.1,(partitionPoint_mem (M.as j) (M.ho j) i.val).2⟩
  have hinU : partitionPoint 0 (M.as j) (i.val+1)∈Icc m.u0 1:=
    ⟨hiU.1.trans (partitionPoint_mono (M.as j) (M.ho j) (Nat.le_succ _)),
      (partitionPoint_mem (M.as j) (M.ho j) (i.val+1)).2⟩
  have hl:=a.alpha.val.property.2 hd.2.2.2.2.1
  have hr:=a.alpha.val.property.2 hd.2.2.2.2.2
  rw [m.R_spec hiU] at hl
  rw [m.R_spec hinU] at hr
  rw [physicalCutMass_sampleClockSteps m.q 0 (M.as j) i.val hd.1.le,
    physicalCutMass_sampleClockSteps m.q 0 (M.as j) (i.val+1) (by omega)]
  exact ⟨hl,hr⟩

omit [Fintype ι] in
theorem selected_mass_le_band {B : ℕ} (label : Fin B→Fin bins) (hagz : ag ≤ zg) (j : ℕ) :
    physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)) 0 (M.selected label j) ≤
      a.alpha.val.val zg-a.alpha.val.val ag := by
  apply physicalWindowMass_le_selected_cut_span _
    (sampleClockSteps_ordered _ _ (M.ho j)) _ (a.alpha.val.property.2 hagz)
  intro i hi
  obtain ⟨b,_,hb⟩:=Finset.mem_biUnion.mp hi
  exact M.row_mass_bounds j i (P.retainedBin_subset c Dcuts ag zg (M.as j) bins w (label b) hb)

omit [Fintype ι] in
theorem total_width_le_band {B : ℕ} (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    (hagz : ag ≤ zg) (j : ℕ) :
    (∑b,M.width j (label b)) ≤ a.alpha.val.val zg-a.alpha.val.val ag := by
  have HS:=native_kept_disjoint_mass (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j))
    (fun b=>M.bin j (label b)) (fun _=>true) (M.bin_disjoint label hlabel j)
  simp only [nativeKeptRows,ite_true] at HS
  calc
    _=∑b,physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)) 0 (M.bin j (label b)) := by
      apply Finset.sum_congr rfl
      intro b _
      exact (M.co j (label b)).width
    _=physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)) 0 (M.selected label j):=HS.symm
    _ ≤ _:=M.selected_mass_le_band label hagz j

omit [Fintype ι] in
theorem total_width_limit_le_band {B : ℕ} (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    (hagz : ag ≤ zg) :
    (∑b,M.f (label b) ⟨1,by simp⟩) ≤ a.alpha.val.val zg-a.alpha.val.val ag :=
  le_of_tendsto (M.total_width_tendsto label) (Eventually.of_forall (M.total_width_le_band label hlabel hagz))

end ActualHighWallOverlapMinimum.SelectedMasterFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
