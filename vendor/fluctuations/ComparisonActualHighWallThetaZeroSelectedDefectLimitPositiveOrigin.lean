module

public import ComparisonActualHighWallSelectedDefectLimit
public import ComparisonActualHighWallThetaZeroSelectedDefectLimit
public import ComparisonShiftedNativePositiveOriginSelectedDefectLimit
public import ComparisonActualHighWallThetaZeroSelectedRowsGeometryPositiveOrigin

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 28000000
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum.SelectedMasterFamily
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {W : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : W.Potential} {ι : Type*} [Fintype ι] {c : ι→ShiftedCapInterval W P}
variable {Dcuts : Finset ℝ} {ag zg w cut Q : ℝ} {bins ell : ℕ} {hbins : 0<bins}
variable (M : SelectedMasterFamily W P c Dcuts ag zg bins hbins w cut ell Q)

theorem binLimitSupport_measurable_positive_origin (hag : W.data.rmin≤ag) (hzg : zg ≤ 1) (b : Fin bins) :
    MeasurableSet (M.binLimitSupport b):=
  (P.retainedSupport_measurable c hag hzg).inter measurableSet_Ioo

theorem keptLimitSupport_measurable_positive_origin (hag : W.data.rmin≤ag) (hzg : zg ≤ 1) :
    MeasurableSet M.keptLimitSupport:=
  nativeKeptSupport_measurable _ _ (M.binLimitSupport_measurable_positive_origin hag hzg)

omit [Fintype ι] in
private theorem original_selection_convergence_positive_origin
    (hag : W.data.rmin≤ag) (hzg : zg ≤ 1)
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)).length+1)))
    (hsub : ∀j,J j⊆M.fullRows j)
    (F : Set ℝ) (hF : MeasurableSet F) (hFD : F⊆Ioo ag zg)
    (hgeom : ∀ᵐr∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>W.shiftedNativeModel.R
        (partitionPoint 0 (M.as j) i)) (J j) ↔r∈F)) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask W.shiftedNativeModel.q (M.as j) (J j) u-
      F.indicator (fun _=>1) (W.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto (fun j=>W.shiftedNativeModel.selectedDefect (M.as j) (J j)) atTop (𝓝 (M.limitThermal F)) := by
  let m:=W.shiftedNativeModel
  have hdata j i (hi:i∈J j):=(P.retainedRows_mem c Dcuts ag zg (M.as j) i).mp (hsub j hi)
  have hmem:=ae_restrict_of_ae_restrict_of_subset
    (Ioo_subset_Ioo (W.data.hrbounds.1.le.trans hag) hzg) hgeom
  have hJ j i (hi:i∈J j):=(hdata j i hi).1
  have hhigh j i (hi:i∈J j):=(hdata j i hi).2.2.2.1
  have hleft j i (hi:i∈J j):=(hdata j i hi).2.2.2.2.1
  have hright j i (hi:i∈J j):=(hdata j i hi).2.2.2.2.2
  refine ⟨m.binary_mass_L1_of_support_eventually_positive_origin M.as M.ho M.he J hJ hhigh hag hzg
    hleft hright F hF hFD hmem,?_⟩
  have ht:=m.selectedDefect_tendsto_radius_positive_origin M.as M.mesh M.ho M.he M.hmesh M.mesh_tendsto
    J hJ hhigh hag hzg hleft hright F hF hFD hmem
  have hw : Measurable (fun u=>F.indicator (fun _ : ℝ=>(1:ℝ)) (m.R u)):=
    (measurable_const.indicator hF).comp m.R_continuous.measurable
  have hb u (_hu:u∈Ioc (0:ℝ) 1) : F.indicator (fun _ : ℝ=>(1:ℝ)) (m.R u)∈Icc (0:ℝ) 1:=by
    simp only [Set.indicator_apply]
    split_ifs <;> norm_num
  have hi:=intervalIntegrable_bounded_measurable_mul hw (by norm_num : (0:ℝ) ≤ 1) hb
    (physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf m.hbf m.hhf)
  unfold limitThermal
  rw [m.binary_thermal_pullback_positive_origin hag hzg F hF hFD _ hi]
  exact ht

theorem full_selection_convergence_positive_origin (hag : W.data.rmin≤ag) (hzg : zg ≤ 1) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask W.shiftedNativeModel.q (M.as j) (M.fullRows j) u-
      M.fullLimitSupport.indicator (fun _=>1) (W.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto M.fullDefect atTop (𝓝 (M.limitThermal M.fullLimitSupport)) :=
  M.original_selection_convergence_positive_origin hag hzg M.fullRows (fun _=>Subset.refl _)
    M.fullLimitSupport (P.retainedSupport_measurable c hag hzg) (fun _ h=>h.1)
    (P.retainedRows_support_ae_positive_origin c Dcuts M.as M.mesh M.ho M.he M.hmesh M.mesh_nonneg M.mesh_tendsto hag hzg)

theorem bin_selection_convergence_positive_origin (hag : W.data.rmin≤ag) (hzg : zg ≤ 1) (b : Fin bins) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask W.shiftedNativeModel.q (M.as j) (M.bin j b) u-
      (M.binLimitSupport b).indicator (fun _=>1) (W.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto (fun j=>W.shiftedNativeModel.selectedDefect (M.as j) (M.bin j b)) atTop
      (𝓝 (M.limitThermal (M.binLimitSupport b))) :=
  M.original_selection_convergence_positive_origin hag hzg (fun j=>M.bin j b)
    (fun j=>P.retainedBin_subset c Dcuts ag zg (M.as j) bins w b)
    (M.binLimitSupport b) (M.binLimitSupport_measurable_positive_origin hag hzg b) (fun _ h=>h.1.1) (M.geometry b)

theorem kept_selection_convergence_positive_origin (hag : W.data.rmin≤ag) (hzg : zg ≤ 1) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask W.shiftedNativeModel.q (M.as j) (M.keptRows j) u-
      M.keptLimitSupport.indicator (fun _=>1) (W.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto M.keptDefect atTop (𝓝 (M.limitThermal M.keptLimitSupport)) := by
  apply M.original_selection_convergence_positive_origin hag hzg M.keptRows _ M.keptLimitSupport
    (M.keptLimitSupport_measurable_positive_origin hag hzg) _ _
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

theorem selected_selection_convergence_positive_origin (hag : W.data.rmin≤ag) (hzg : zg ≤ 1)
    {B : ℕ} (label : Fin B→Fin bins) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask W.shiftedNativeModel.q (M.as j) (M.selected label j) u-
      (M.selectedLimitSupport label).indicator (fun _=>1) (W.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto (M.defect label) atTop (𝓝 (M.limitThermal (M.selectedLimitSupport label))) := by
  apply M.original_selection_convergence_positive_origin hag hzg (M.selected label) _ (M.selectedLimitSupport label)
    (nativeKeptSupport_measurable _ _ (fun b=>M.binLimitSupport_measurable_positive_origin hag hzg (label b))) _ _
  · intro j i hi
    obtain ⟨b,_,hb⟩:=Finset.mem_biUnion.mp hi
    exact P.retainedBin_subset c Dcuts ag zg (M.as j) bins w (label b) hb
  · rintro r ⟨b,_,hr⟩
    exact hr.1.1
  · filter_upwards [ae_all_iff.mpr (fun b : Fin B=>M.geometry (label b))] with r hr
    filter_upwards [Filter.eventually_all.mpr hr] with j hj
    change (r∈NativeSelectedMask.finiteSupport (fun i=>W.shiftedNativeModel.R (partitionPoint 0 (M.as j) i))
      (Finset.univ.biUnion (fun b=>M.bin j (label b))) ↔r∈M.selectedLimitSupport label)
    have he : Finset.univ.biUnion (fun b=>M.bin j (label b))=
        nativeKeptRows (fun b=>M.bin j (label b)) (fun _=>true):=by simp [nativeKeptRows]
    rw [he,nativeKeptRows_support]
    exact exists_congr (fun b=>and_congr_right (fun _=>hj b))

theorem defect_tendsto_positive_origin (hag : W.data.rmin≤ag) (hzg : zg ≤ 1)
    {B : ℕ} (label : Fin B→Fin bins) :
    Tendsto (M.defect label) atTop (𝓝 (M.limitThermal (M.selectedLimitSupport label))) :=
  (M.selected_selection_convergence_positive_origin hag hzg label).2

theorem full_thermal_le_kept_add_2_bins_cut_positive_origin (hag : W.data.rmin≤ag) (hzg : zg ≤ 1)
    (hcut : 0 ≤ cut) :
    M.limitThermal M.fullLimitSupport ≤ M.limitThermal M.keptLimitSupport+2*(bins:ℝ)*cut :=
  le_of_tendsto_of_tendsto (M.full_selection_convergence_positive_origin hag hzg).2
    ((M.kept_selection_convergence_positive_origin hag hzg).2.add_const (2*(bins:ℝ)*cut))
    (Eventually.of_forall (M.fullDefect_le_kept_add hcut))

theorem full_thermal_le_selected_add_2_bins_cut_positive_origin (hag : W.data.rmin≤ag) (hzg : zg ≤ 1)
    (hcut : 0 ≤ cut) {B : ℕ} (label : Fin B→Fin bins)
    (hkept : ∀b,M.keep (label b)=true)
    (hcover : ∀b,M.keep b=true→∃i,label i=b) :
    M.limitThermal M.fullLimitSupport ≤ M.limitThermal (M.selectedLimitSupport label)+2*(bins:ℝ)*cut := by
  rw [←M.keptLimitSupport_eq_selected label hkept hcover]
  exact M.full_thermal_le_kept_add_2_bins_cut_positive_origin hag hzg hcut

end ActualThetaZeroOverlapMinimum.SelectedMasterFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
