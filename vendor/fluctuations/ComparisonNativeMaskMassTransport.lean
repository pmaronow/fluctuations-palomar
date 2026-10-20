module

public import ComparisonNativeSideColumnLimit
public import ComparisonPhysicalWeightedGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2400000

theorem massStepFunction_eq_radiusCellEnergyDensity_ae
    {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as)
    (he : partitionEnd u as=1) (C : ℕ → ℝ) :
    ∀ᵐ t∂volume,t∈Ioo u 1 →
      massStepFunction as C t=radiusCellEnergyDensity id u as C t := by
  induction as generalizing u C with
  | nil=>
    have hu : u=1 := he
    simp [hu]
  | cons a as ih=>
    have ht := ih ho.2.2 he (fun j=>C (j+1))
    filter_upwards [ht,volume.ae_ne a.val] with t ht hta htu
    by_cases hlt : t<a.val
    · have hr : t∈Ioc (id u) (id a.val) := ⟨htu.1,hlt.le⟩
      rw [massStepFunction,ite_eq_left hlt,radiusCellEnergyDensity,indicator_of_mem hr,
        radiusCellEnergyDensity_eq_zero_of_le id monotone_id as ho.2.2 _ hlt.le,add_zero]
    · have hat : a.val<t := lt_of_le_of_ne (le_of_not_gt hlt) hta.symm
      have hr : t∉Ioc (id u) (id a.val) := fun hh=>not_le.mpr hat hh.2
      rw [massStepFunction,ite_eq_right hlt,radiusCellEnergyDensity,indicator_of_notMem hr,zero_add]
      exact ht ⟨hat,htu.2⟩

theorem radiusCellEnergyDensity_comp_strictMonoOn
    (R : ℝ → ℝ) (hR : StrictMonoOn R (Icc (0:ℝ) 1))
    {u : ℝ} (hu : u∈Icc (0:ℝ) 1) (as : List PositiveMass)
    (ho : MassOrdered u as) (C : ℕ → ℝ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    radiusCellEnergyDensity R u as C (R t)=radiusCellEnergyDensity id u as C t := by
  induction as generalizing u C with
  | nil=>rfl
  | cons a as ih=>
    have ha : a.val∈Icc (0:ℝ) 1 := massOrdered_bounds ho.2.2
    have hmem : R t∈Ioc (R u) (R a.val) ↔ t∈Ioc (id u) (id a.val) :=
      and_congr (hR.lt_iff_lt hu ht) (hR.le_iff_le ht ha)
    simp only [radiusCellEnergyDensity]
    rw [ih ha ho.2.2]
    by_cases hr : t∈Ioc (id u) (id a.val)
    · rw [indicator_of_mem hr,indicator_of_mem (hmem.mpr hr)]
    · rw [indicator_of_notMem hr,indicator_of_notMem (fun h=>hr (hmem.mp h))]

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

include hc hk hkc hm hM in
theorem comparison_inverse_image_unit_interval
    (α : inverseIntegralConstraints 0 0 k M) :
    α.val.val '' Icc (0:ℝ) 1=Icc (0:ℝ) 1 := by
  ext u
  constructor
  · rintro ⟨r,hr,rfl⟩
    exact ⟨by simpa only [α.property.1] using
      α.val.property.2 (show (0:ℝ)≤r from hr.1),
      by simpa only [α.property.2.1] using α.val.property.2 hr.2⟩
  · intro hu
    exact ⟨comparisonSweepQuantile hc hk hkc hm hM α u,
      comparisonSweepQuantile_bounds hc hk hkc hm hM α u,
      comparisonSweepQuantile_mass_spec hc hk hkc hm hM α hu⟩

include hc hk hkc hm hM in
theorem comparison_mass_radius_integral
    (α : inverseIntegralConstraints 0 0 k M) (G : ℝ → ℝ) :
    (∫u in Icc (0:ℝ) 1,G u)=
      ∫r in Icc (0:ℝ) 1,deriv α.val.val r*G (α.val.val r) := by
  simpa only [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]
    using comparisonSweep_mass_substitution hc hk hkc hm hM α G

theorem comparison_quantile_weighted_integral
    (α : inverseIntegralConstraints 0 0 k M) (G : ℝ → ℝ) :
    (∫u in Icc (0:ℝ) 1,G (comparisonSweepQuantile hc hk hkc hm hM α u))=
      ∫r in Icc (0:ℝ) 1,deriv α.val.val r*G r := by
  rw [comparison_mass_radius_integral hc hk hkc hm hM α]
  apply setIntegral_congr_fun measurableSet_Icc
  intro r hr
  dsimp only
  rw [comparisonSweepQuantile_inverse hc hk hkc hm hM α hr]

theorem comparisonNativeMask_mass_radius_ae {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1) → Fin K) (col : Fin K → ℝ) :
    ∀ᵐ u∂volume.restrict (Icc (0:ℝ) 1),
      massStepFunction as (nativeSelectedColumn J unit col) u=
        comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit col
          (comparisonSweepQuantile hc hk hkc hm hM α u) := by
  have hid := massStepFunction_eq_radiusCellEnergyDensity_ae as ho he
    (nativeSelectedColumn J unit col)
  filter_upwards [ae_restrict_of_ae hid,ae_restrict_mem measurableSet_Icc,
    ae_restrict_of_ae (volume.ae_ne (0:ℝ)),ae_restrict_of_ae (volume.ae_ne (1:ℝ))]
    with u hdu hu hu0 hu1
  rw [hdu ⟨lt_of_le_of_ne hu.1 hu0.symm,lt_of_le_of_ne hu.2 hu1⟩]
  exact (radiusCellEnergyDensity_comp_strictMonoOn _
    (comparisonSweepQuantile_strictMono_native_geometry hc hk hkc hm hM α)
    (show (0:ℝ)∈Icc (0:ℝ) 1 by simp) as ho _ hu).symm

theorem comparisonNativeMask_mass_radius_L1_eq {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1) → Fin K)
    (col : Fin K → ℝ) (w : ℝ → ℝ) :
    (∫u in Icc (0:ℝ) 1,
      |massStepFunction as (nativeSelectedColumn J unit col) u-
        w (comparisonSweepQuantile hc hk hkc hm hM α u)|)=
      ∫r in Icc (0:ℝ) 1,|deriv α.val.val r*
        comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit col r-
        deriv α.val.val r*w r| := by
  calc
    _=(∫u in Icc (0:ℝ) 1,
        |comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit col
          (comparisonSweepQuantile hc hk hkc hm hM α u)-
          w (comparisonSweepQuantile hc hk hkc hm hM α u)|) := by
      apply integral_congr_ae
      filter_upwards [comparisonNativeMask_mass_radius_ae hc hk hkc hm hM q α as ho he J unit col]
        with u hu
      rw [hu]
    _=∫r in Icc (0:ℝ) 1,deriv α.val.val r*
        |comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit col r-w r| :=
      comparison_quantile_weighted_integral hc hk hkc hm hM α
        (fun r=>|comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J unit col r-w r|)
    _=_ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun r=>by
        dsimp only
        rw [←mul_sub,abs_mul,abs_of_nonneg α.val.property.2.deriv_nonneg])

theorem comparisonNativeMask_mass_L1_tendsto_of_radius_ae {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ → List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (K : ℕ → ℕ)
    (J : ∀j,Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1) → Fin (K j))
    (w : ℝ → ℝ)
    (hpoint : ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
      Tendsto (fun j=>comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (J j) (unit j) (fun _=>1) r) atTop (𝓝 (w r))) :
    Tendsto (fun j=>∫u in Icc (0:ℝ) 1,
      |massStepFunction (as j) (nativeSelectedColumn (J j) (unit j) (fun _=>1)) u-
        w (comparisonSweepQuantile hc hk hkc hm hM α u)|) atTop (𝓝 0) := by
  let moving := fun j r=>deriv α.val.val r*
    comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j) (J j) (unit j) (fun _=>1) r
  have hmeas j : AEStronglyMeasurable (moving j) (volume.restrict (Icc (0:ℝ) 1)) :=
    ((stronglyMeasurable_deriv α.val.val).mul
      (comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α (as j)
        (J j) (unit j) (fun _=>1)).stronglyMeasurable).aestronglyMeasurable.restrict
  have hb j : ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),‖moving j r‖≤M 1 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0:ℝ)),ae_restrict_of_ae (volume.ae_ne (1:ℝ))]
      with r hr hr0 hr1
    have hri : r∈Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne hr.1 hr0.symm,lt_of_le_of_ne hr.2 hr1⟩
    have hd := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hri.1 hri.2)
      (inverseIntegralConstraints_lipschitz hm hM α.property)
    have hmcol : comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (J j) (unit j) (fun _=>1) r∈Icc (0:ℝ) 1 :=
      radiusCellEnergyDensity_mem_Icc _ (comparisonSweepQuantile_monotone hc hk hkc hm hM α)
        (as j) (ho j) _ (fun i=>by unfold nativeSelectedColumn;split_ifs <;> norm_num) r
    have hcolnorm : ‖comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        (J j) (unit j) (fun _=>1) r‖≤1 := by
      simpa only [Real.norm_eq_abs,abs_of_nonneg hmcol.1] using hmcol.2
    dsimp only [moving]
    rw [norm_mul]
    calc
      _ ≤ ‖deriv α.val.val r‖*1 := mul_le_mul_of_nonneg_left hcolnorm (norm_nonneg _)
      _ = ‖deriv α.val.val r‖ := mul_one _
      _ ≤ M 1 := hd
  have hL1 := bounded_contact_weights_tendsto_L1 (Icc (0:ℝ) 1) (by simp)
    moving (fun r=>deriv α.val.val r*w r) hmeas hb
    (hpoint.mono (fun r hr=>hr.const_mul (deriv α.val.val r)))
  have heq j := comparisonNativeMask_mass_radius_L1_eq hc hk hkc hm hM q α (as j)
    (ho j) (he j) (J j) (unit j) (fun _=>1) w
  simpa only [heq] using hL1

end
end OAI.SKFluctuations.LaplaceWindowFormalization
