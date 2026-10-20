module

public import ComparisonActualHighWallSelectedDefectLimit
public import ComparisonActualHighWallThetaZeroSelectedLedger

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

abbrev fullRows (j : ℕ):=P.retainedRows c Dcuts ag zg (M.as j)
abbrev fullLimitSupport : Set ℝ:=let _:=M;P.retainedSupport c ag zg
def binLimitSupport (b : Fin bins) : Set ℝ:=M.fullLimitSupport∩Ioo (M.l b).val (M.u b).val
def keptRows (j : ℕ):=nativeKeptRows (M.bin j) M.keep
def keptLimitSupport : Set ℝ:=nativeKeptSupport M.binLimitSupport M.keep
def selectedLimitSupport {B : ℕ} (label : Fin B→Fin bins) : Set ℝ:=
  nativeKeptSupport (fun b=>M.binLimitSupport (label b)) (fun _=>true)
def limitThermal (F : Set ℝ) : ℝ:=let _:=M;∫u in 0..1,F.indicator (fun _=>1)
  (W.shiftedNativeModel.R u)*W.shiftedNativeModel.thermal u
def fullDefect (j : ℕ) : ℝ:=W.shiftedNativeModel.selectedDefect (M.as j) (M.fullRows j)
def keptDefect (j : ℕ) : ℝ:=W.shiftedNativeModel.selectedDefect (M.as j) (M.keptRows j)

theorem binLimitSupport_measurable (hag : W.data.rmin<ag) (hzg : zg ≤ 1) (b : Fin bins) :
    MeasurableSet (M.binLimitSupport b):=
  (P.retainedSupport_measurable c hag.le hzg).inter measurableSet_Ioo

theorem keptLimitSupport_measurable (hag : W.data.rmin<ag) (hzg : zg ≤ 1) :
    MeasurableSet M.keptLimitSupport:=
  nativeKeptSupport_measurable _ _ (M.binLimitSupport_measurable hag hzg)

omit [Fintype ι] in
theorem selectedLimitSupport_eq_iUnion {B : ℕ} (label : Fin B→Fin bins) :
    M.selectedLimitSupport label=⋃b,M.fullLimitSupport∩Ioo (M.l (label b)).val (M.u (label b)).val := by
  ext r
  simp [selectedLimitSupport,nativeKeptSupport,binLimitSupport]

omit [Fintype ι] in
private theorem original_selection_convergence
    (hag : W.data.rmin<ag) (hzg : zg ≤ 1)
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
    (Ioo_subset_Ioo (W.data.hrbounds.1.le.trans hag.le) hzg) hgeom
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

theorem full_selection_convergence (hag : W.data.rmin<ag) (hzg : zg ≤ 1) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask W.shiftedNativeModel.q (M.as j) (M.fullRows j) u-
      M.fullLimitSupport.indicator (fun _=>1) (W.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto M.fullDefect atTop (𝓝 (M.limitThermal M.fullLimitSupport)) :=
  M.original_selection_convergence hag hzg M.fullRows (fun _=>Subset.refl _)
    M.fullLimitSupport (P.retainedSupport_measurable c hag.le hzg) (fun _ h=>h.1)
    (P.retainedRows_support_ae c Dcuts M.as M.mesh M.ho M.he M.hmesh M.mesh_nonneg M.mesh_tendsto hag hzg)

theorem bin_selection_convergence (hag : W.data.rmin<ag) (hzg : zg ≤ 1) (b : Fin bins) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask W.shiftedNativeModel.q (M.as j) (M.bin j b) u-
      (M.binLimitSupport b).indicator (fun _=>1) (W.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
    Tendsto (fun j=>W.shiftedNativeModel.selectedDefect (M.as j) (M.bin j b)) atTop
      (𝓝 (M.limitThermal (M.binLimitSupport b))) :=
  M.original_selection_convergence hag hzg (fun j=>M.bin j b)
    (fun j=>P.retainedBin_subset c Dcuts ag zg (M.as j) bins w b)
    (M.binLimitSupport b) (M.binLimitSupport_measurable hag hzg b) (fun _ h=>h.1.1) (M.geometry b)

theorem kept_selection_convergence (hag : W.data.rmin<ag) (hzg : zg ≤ 1) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask W.shiftedNativeModel.q (M.as j) (M.keptRows j) u-
      M.keptLimitSupport.indicator (fun _=>1) (W.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
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

theorem selected_selection_convergence (hag : W.data.rmin<ag) (hzg : zg ≤ 1)
    {B : ℕ} (label : Fin B→Fin bins) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask W.shiftedNativeModel.q (M.as j) (M.selected label j) u-
      (M.selectedLimitSupport label).indicator (fun _=>1) (W.shiftedNativeModel.R u)|) atTop (𝓝 0) ∧
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
    change (r∈NativeSelectedMask.finiteSupport (fun i=>W.shiftedNativeModel.R (partitionPoint 0 (M.as j) i))
      (Finset.univ.biUnion (fun b=>M.bin j (label b))) ↔r∈M.selectedLimitSupport label)
    have he : Finset.univ.biUnion (fun b=>M.bin j (label b))=
        nativeKeptRows (fun b=>M.bin j (label b)) (fun _=>true):=by simp [nativeKeptRows]
    rw [he,nativeKeptRows_support]
    exact exists_congr (fun b=>and_congr_right (fun _=>hj b))

theorem defect_tendsto (hag : W.data.rmin<ag) (hzg : zg ≤ 1)
    {B : ℕ} (label : Fin B→Fin bins) :
    Tendsto (M.defect label) atTop (𝓝 (M.limitThermal (M.selectedLimitSupport label))) :=
  (M.selected_selection_convergence hag hzg label).2

omit [Fintype ι] in
theorem discarded_mass_le (hcut : 0 ≤ cut) (j : ℕ) :
    physicalWindowMass (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)) 0 (M.fullRows j)-
      physicalWindowMass (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)) 0 (M.keptRows j) ≤
        2*(bins:ℝ)*cut := by
  have H:=native_height_bins_coordinate_mass (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j))
    (fun i=>physicalPathSecondMoment (n+1) (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j))
      (W.shiftedNativeModel.q 0) i.val) (M.fullRows j)
    (firstWholeUnitCell P.negativeSet (W.shiftedNativeModel.rowRadius (M.as j))) w hbins M.keep
    (W.shiftedNativeModel.rowRadius (M.as j)) P.negativeSet (M.co j)
  have HE:=H.2.2
  change physicalWindowMass (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)) 0 (M.fullRows j)-
    physicalWindowMass (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)) 0 (M.keptRows j)=
      ∑b,if M.keep b then 0 else M.width j b at HE
  rw [HE]
  exact constructed_stable_small_bin_ledger M.width M.keep hcut M.cutoffs j

omit [Fintype ι] in
theorem fullDefect_le_kept_add (hcut : 0 ≤ cut) (j : ℕ) :
    M.fullDefect j ≤ M.keptDefect j+2*(bins:ℝ)*cut := by
  let steps:=sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)
  have hs:=sampleClockSteps_ordered W.shiftedNativeModel.q _ (M.ho j)
  have hsub : M.keptRows j⊆M.fullRows j:=by
    intro i hi
    obtain ⟨b,_,hb⟩:=(nativeKeptRows_mem (M.bin j) M.keep i).mp hi
    exact P.retainedBin_subset c Dcuts ag zg (M.as j) bins w b hb
  have H:=(actual_selected_centered_defect_mass_exhaustion (n+1) steps hs
    (W.shiftedNativeModel.q 0) (M.keptRows j) (M.fullRows j) hsub).2
  dsimp only at H
  rw [sum_physicalSelectedCellMass_eq_window,sum_physicalSelectedCellMass_eq_window] at H
  have Hd:=M.discarded_mass_le hcut j
  change M.fullDefect j-M.keptDefect j ≤ _ at H
  linarith

theorem full_thermal_le_kept_add_2_bins_cut (hag : W.data.rmin<ag) (hzg : zg ≤ 1)
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

theorem full_thermal_le_selected_add_2_bins_cut (hag : W.data.rmin<ag) (hzg : zg ≤ 1)
    (hcut : 0 ≤ cut) {B : ℕ} (label : Fin B→Fin bins)
    (hkept : ∀b,M.keep (label b)=true)
    (hcover : ∀b,M.keep b=true→∃i,label i=b) :
    M.limitThermal M.fullLimitSupport ≤ M.limitThermal (M.selectedLimitSupport label)+2*(bins:ℝ)*cut := by
  rw [←M.keptLimitSupport_eq_selected label hkept hcover]
  exact M.full_thermal_le_kept_add_2_bins_cut hag hzg hcut

omit [Fintype ι] in
theorem row_mass_bounds (j : ℕ)
    (i : Fin ((sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)).length+1)) (hi:i∈M.fullRows j) :
    W.alpha.val.val ag ≤ physicalCutMass 0 (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)) i.val ∧
      physicalCutMass 0 (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)) (i.val+1) ≤ W.alpha.val.val zg := by
  let m:=W.shiftedNativeModel
  have hd:=(P.retainedRows_mem c Dcuts ag zg (M.as j) i).mp hi
  have hiU : partitionPoint 0 (M.as j) i.val∈Icc m.u0 1:=
    ⟨hd.2.2.2.1,(partitionPoint_mem (M.as j) (M.ho j) i.val).2⟩
  have hinU : partitionPoint 0 (M.as j) (i.val+1)∈Icc m.u0 1:=
    ⟨hiU.1.trans (partitionPoint_mono (M.as j) (M.ho j) (Nat.le_succ _)),
      (partitionPoint_mem (M.as j) (M.ho j) (i.val+1)).2⟩
  have hl:=W.alpha.val.property.2 hd.2.2.2.2.1
  have hr:=W.alpha.val.property.2 hd.2.2.2.2.2
  rw [m.R_spec hiU] at hl
  rw [m.R_spec hinU] at hr
  rw [physicalCutMass_sampleClockSteps m.q 0 (M.as j) i.val hd.1.le,
    physicalCutMass_sampleClockSteps m.q 0 (M.as j) (i.val+1) (by omega)]
  exact ⟨hl,hr⟩

omit [Fintype ι] in
theorem selected_mass_le_band {B : ℕ} (label : Fin B→Fin bins) (hagz : ag ≤ zg) (j : ℕ) :
    physicalWindowMass (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)) 0 (M.selected label j) ≤
      W.alpha.val.val zg-W.alpha.val.val ag := by
  apply physicalWindowMass_le_selected_cut_span _
    (sampleClockSteps_ordered _ _ (M.ho j)) _ (W.alpha.val.property.2 hagz)
  intro i hi
  obtain ⟨b,_,hb⟩:=Finset.mem_biUnion.mp hi
  exact M.row_mass_bounds j i (P.retainedBin_subset c Dcuts ag zg (M.as j) bins w (label b) hb)

omit [Fintype ι] in
theorem total_width_le_band {B : ℕ} (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    (hagz : ag ≤ zg) (j : ℕ) :
    (∑b,M.width j (label b)) ≤ W.alpha.val.val zg-W.alpha.val.val ag := by
  have HS:=native_kept_disjoint_mass (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j))
    (fun b=>M.bin j (label b)) (fun _=>true) (M.bin_disjoint label hlabel j)
  simp only [nativeKeptRows,ite_true] at HS
  calc
    _=∑b,physicalWindowMass (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)) 0 (M.bin j (label b)) := by
      apply Finset.sum_congr rfl
      intro b _
      exact (M.co j (label b)).width
    _=physicalWindowMass (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)) 0 (M.selected label j):=HS.symm
    _ ≤ _:=M.selected_mass_le_band label hagz j

omit [Fintype ι] in
theorem total_width_limit_le_band {B : ℕ} (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    (hagz : ag ≤ zg) :
    (∑b,M.f (label b) ⟨1,by simp⟩) ≤ W.alpha.val.val zg-W.alpha.val.val ag :=
  le_of_tendsto (M.total_width_tendsto label) (Eventually.of_forall (M.total_width_le_band label hlabel hagz))

end ActualThetaZeroOverlapMinimum.SelectedMasterFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
