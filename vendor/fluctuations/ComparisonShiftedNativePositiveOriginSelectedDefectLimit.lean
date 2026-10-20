module

public import ComparisonActualHighWallSelectedDefectLimit
public import ComparisonShiftedNativePositiveOriginMaskColumns

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem binary_mass_radius_L1_eq_positive_origin
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0 ≤ partitionPoint 0 as i.val)
    {ag zg : ℝ} (hag : m.rmin≤ag) (F : Set ℝ) (hF : MeasurableSet F) (hFD : F⊆Ioo ag zg) :
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
  have hF0 : m.rmin∉F:=fun hr=>not_lt_of_ge hag (hFD hr).1
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

theorem binary_mass_L1_of_support_eventually_positive_origin
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (hJ : ∀j,∀i∈J j,i.val<(as j).length)
    (hhigh : ∀j,∀i∈J j,m.u0 ≤ partitionPoint 0 (as j) i.val)
    {ag zg : ℝ} (hag : m.rmin≤ag) (hzg : zg ≤ 1)
    (hleft : ∀j,∀i∈J j,ag ≤ m.R (partitionPoint 0 (as j) i.val))
    (hright : ∀j,∀i∈J j,m.R (partitionPoint 0 (as j) (i.val+1)) ≤ zg)
    (F : Set ℝ) (hF : MeasurableSet F) (hFD : F⊆Ioo ag zg)
    (hmem : ∀ᵐr∂volume.restrict (Ioo ag zg),∀ᶠj in atTop,
      (r∈NativeSelectedMask.finiteSupport (fun i=>m.R (partitionPoint 0 (as j) i)) (J j) ↔r∈F)) :
    Tendsto (fun j=>∫u in 0..1,|nativeSelectedMassMask m.q (as j) (J j) u-
      F.indicator (fun _=>1) (m.R u)|) atTop (𝓝 0) := by
  have ht:=m.binary_density_L1_of_support_eventually_positive_origin as ho (fun _=>1) J (fun _ _=>(0:Fin 1))
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
        (Ioo_subset_Icc_self.trans (Icc_subset_Icc hag hzg))]
  simp_rw [m.binary_mass_radius_L1_eq_positive_origin _ (ho _) (he _) _ (hhigh _) hag F hF hFD,heq]
  exact ht

theorem binary_thermal_pullback_positive_origin {ag zg : ℝ} (hag : m.rmin≤ag) (hzg : zg ≤ 1)
    (F : Set ℝ) (hF : MeasurableSet F) (hFD : F⊆Ioo ag zg) (G : ℝ→ℝ)
    (hGi : IntervalIntegrable (fun u=>F.indicator (fun _=>1) (m.R u)*G u) volume 0 1) :
    (∫u in 0..1,F.indicator (fun _=>1) (m.R u)*G u)=
      ∫r in F,deriv m.alpha.val.val r*G (m.alpha.val.val r) := by
  let integrand:=fun u=>F.indicator (fun _ : ℝ=>(1:ℝ)) (m.R u)*G u
  have hi0 : IntervalIntegrable integrand volume 0 m.u0:=hGi.mono_set (by
    rw [uIcc_of_le zero_le_one,uIcc_of_le m.hu.1];exact Icc_subset_Icc le_rfl m.hu.2)
  have hi1 : IntervalIntegrable integrand volume m.u0 1:=hGi.mono_set (by
    rw [uIcc_of_le zero_le_one,uIcc_of_le m.hu.2];exact Icc_subset_Icc m.hu.1 le_rfl)
  have hF0 : m.rmin∉F:=fun hr=>not_lt_of_ge hag (hFD hr).1
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
        inter_eq_left.mpr (hFD.trans (Ioo_subset_Icc_self.trans (Icc_subset_Icc hag hzg)))]

theorem selectedDefect_tendsto_radius_positive_origin
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (he : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0))
    (J : (j : ℕ)→Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (hJ : ∀j,∀i∈J j,i.val<(as j).length)
    (hhigh : ∀j,∀i∈J j,m.u0 ≤ partitionPoint 0 (as j) i.val)
    {ag zg : ℝ} (hag : m.rmin≤ag) (hzg : zg ≤ 1)
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
  have hL1:=m.binary_mass_L1_of_support_eventually_positive_origin as ho he J hJ hhigh hag hzg
    hleft hright F hF hFD hmem
  have ht:=actual_selected_centered_defect_tendsto_native_path m.n m.bf m.hf m.hbf m.hhf
    as mesh ho he hmesh hlim J fixed hfixed hfb hL1
  have hGi:=intervalIntegrable_bounded_measurable_mul hfixed (by norm_num : (0:ℝ) ≤ 1) hfb
    (physicalOrderedThermal_intervalIntegrable m.n m.bf m.hf m.hbf m.hhf)
  rw [m.binary_thermal_pullback_positive_origin hag hzg F hF hFD _ hGi] at ht
  exact ht

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
