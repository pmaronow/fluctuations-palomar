module

public import ComparisonShiftedNativeColumns
public import ComparisonNativeRadiusLinearConvergence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem R_before {u : ℝ} (hu : u≤ m.u0) : m.R u=m.rmin := by
  apply le_antisymm
  · simpa only [m.R_left] using m.R_monotone hu
  · exact (m.R_bounds u).1

theorem R_high_mass {u : ℝ} (hu : m.rmin< m.R u) : m.u0<u := by
  by_contra hn
  rw [m.R_before (le_of_not_gt hn)] at hu
  exact lt_irrefl _ hu

theorem mass_radius_substitution (f : ℝ→ℝ) :
    (∫u in m.u0..1,f u)=∫r in Icc m.rmin 1,deriv m.alpha.val.val r*f (m.alpha.val.val r) := by
  have h := m.mass_radius_cell_substitution f ⟨le_rfl,m.hu.2⟩ ⟨m.hu.2,le_rfl⟩ m.hu.2
  simpa only [m.R_left,m.R_one] using h

theorem radiusMassWeight_zero_before_lower_radius
    {A : Set ℝ} {a z : ℝ} (ha : a∈Icc m.rmin 1) (hAD : A⊆Ioo a z)
    (x kmin : ℝ) {u : ℝ} (hu : u≤ m.alpha.val.val a) :
    comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin u=0 := by
  have hr := m.R_monotone hu
  rw [m.R_inverse ha] at hr
  unfold comparisonRadiusMassWeight
  exact ite_eq_right (fun h=>not_lt_of_ge hr (hAD h).1)

theorem originalWeights_native_cut_floor
    {A : Set ℝ} {a z : ℝ} (ha : a∈Icc m.rmin 1) (hAD : A⊆Ioo a z)
    (x kmin : ℝ) (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    (i : Fin ((sampleClockSteps m.q 0 as).length+1))
    (hnz : comparisonOriginalRadiusWeights m.q as
      (comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin) i≠0) :
    m.alpha.val.val a-mesh≤physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val := by
  have hi : i.val≤as.length := by
    have hit := i.isLt
    simp only [sampleClockSteps_length] at hit
    omega
  rw [physicalCutMass_sampleClockSteps m.q 0 as i.val hi]
  exact MassCellAveraging.originalCoefficient_support_floor _ as ho hmesh
    (fun u hu=>m.radiusMassWeight_zero_before_lower_radius ha hAD x kmin hu) hnz

theorem radiusMassWeight_square_pullback
    {A : Set ℝ} {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin)
    (hfloor : ∀r∈A,kmin≤ m.k r) :
    ∀ᵐ r∂volume.restrict (Icc m.rmin 1),
      deriv m.alpha.val.val r*(comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
        (m.alpha.val.val r))^2=
      A.indicator (comparisonReciprocalDensityWeight m.alpha.val.val x kmin) r := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae m.density_floor_ae] with r hr hd
  unfold comparisonRadiusMassWeight
  rw [m.R_inverse hr]
  by_cases hrA : r∈A
  · rw [ite_eq_left hrA,indicator_of_mem hrA]
    have hder : kmin≤deriv m.alpha.val.val r := (hfloor r hrA).trans (hd hr)
    have hp : 0<deriv m.alpha.val.val r := hkmin.trans_le hder
    unfold comparisonReciprocalDensityWeight
    rw [max_eq_right hder]
    field_simp [ne_of_gt hp,hx.ne']
  · simp only [hrA,ite_false,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,indicator_of_notMem hrA]

theorem radiusMassWeight_linear_pullback
    {A : Set ℝ} {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin)
    (hfloor : ∀r∈A,kmin≤ m.k r) :
    ∀ᵐ r∂volume.restrict (Icc m.rmin 1),
      deriv m.alpha.val.val r*comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
        (m.alpha.val.val r)=A.indicator (fun _ : ℝ=>1/x) r := by
  filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae m.density_floor_ae] with r hr hd
  unfold comparisonRadiusMassWeight
  rw [m.R_inverse hr]
  by_cases hrA : r∈A
  · rw [ite_eq_left hrA,indicator_of_mem hrA]
    have hder : kmin≤deriv m.alpha.val.val r := (hfloor r hrA).trans (hd hr)
    have hp : 0<deriv m.alpha.val.val r := hkmin.trans_le hder
    rw [max_eq_right hder]
    field_simp [ne_of_gt hp,hx.ne']
  · simp only [hrA,ite_false,mul_zero,indicator_of_notMem hrA]

theorem originalAverage_comp_radius_density_ae (f Φ : ℝ→ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) :
    ∀ᵐ r∂volume.restrict (Icc m.rmin 1),
      radiusCellEnergyDensity m.R 0 as
        (fun i=>Φ (MassCellAveraging.originalCoefficient f 0 as i)) r=
      Φ (MassCellAveraging.sample f 0 as (m.alpha.val.val r)) := by
  have hR0 : m.R 0=m.rmin := m.R_before m.hu.1
  have hcut : ∀ᵐ r∂volume,∀v∈as,r≠m.R v.val := by
    clear ho he
    induction as with
    | nil=>exact Eventually.of_forall (fun _ _ h=>by simp at h)
    | cons b bs ih=>
      filter_upwards [volume.ae_ne (m.R b.val),ih] with r hr hi v hv
      rcases List.mem_cons.mp hv with heq|hm
      · subst v;exact hr
      · exact hi v hm
  have hpoint {a : ℝ} (bs : List PositiveMass) (hord : MassOrdered a bs)
      (hend : partitionEnd a bs=1) (r : ℝ) (hr : r∈Ioo (m.R a) 1)
      (hcuts : ∀v∈bs,r≠m.R v.val) :
      radiusCellEnergyDensity m.R a bs
        (fun i=>Φ (MassCellAveraging.originalCoefficient f a bs i)) r=
      Φ (MassCellAveraging.sample f a bs (m.alpha.val.val r)) := by
    induction bs generalizing a with
    | nil=>
      simp only [partitionEnd] at hend
      subst a
      rw [m.R_one] at hr
      exact False.elim (not_lt_of_ge hr.1.le hr.2)
    | cons b bs ih=>
      have hrI : r∈Icc m.rmin 1 := ⟨(m.R_bounds a).1.trans hr.1.le,hr.2.le⟩
      have hbI := m.R_bounds b.val
      have hmass (hbhigh : m.u0≤b.val) : m.alpha.val.val (m.R b.val)=b.val :=
        m.R_spec ⟨hbhigh,(massOrdered_bounds hord.2.2).2⟩
      by_cases hrb : r< m.R b.val
      · have hbhigh : m.u0≤b.val :=
          (m.R_high_mass ((m.R_bounds a).1.trans_lt (hr.1.trans hrb))).le
        have hum : m.alpha.val.val r<b.val := by
          have hs := inverseConstraint_strictMonoOn m.hc m.hk m.hkc m.alpha.property hrI hbI hrb
          rwa [hmass hbhigh] at hs
        have hcell : r∈Ioc (m.R a) (m.R b.val) := ⟨hr.1,hrb.le⟩
        rw [radiusCellEnergyDensity,indicator_of_mem hcell,
          radiusCellEnergyDensity_eq_zero_of_le m.R m.R_monotone bs hord.2.2 _ hrb.le,add_zero,
          MassCellAveraging.sample,ite_eq_left hum]
        simp only [MassCellAveraging.originalCoefficient,partitionPoint,partitionValues,partitionValues_zero,id_eq]
      · have hneq := hcuts b (List.mem_cons_self)
        have hlt : m.R b.val<r := lt_of_le_of_ne (le_of_not_gt hrb) hneq.symm
        have hum : b.val≤ m.alpha.val.val r := by
          by_cases hbhigh : m.u0≤b.val
          · have hs := m.alpha.val.property.2 hlt.le
            rwa [hmass hbhigh] at hs
          · exact (le_of_not_ge hbhigh).trans
              (inverseConstraint_mass_mem m.hr m.hc m.hk m.hkc m.alpha hrI).1
        have hnot : r∉Ioc (m.R a) (m.R b.val) := fun hc=>not_le_of_gt hlt hc.2
        rw [radiusCellEnergyDensity,indicator_of_notMem hnot,zero_add,
          MassCellAveraging.sample,ite_eq_right (not_lt.mpr hum)]
        exact ih hord.2.2 hend ⟨hlt,hr.2⟩ (fun v hv=>hcuts v (List.mem_cons_of_mem _ hv))
  filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hcut,
    ae_restrict_of_ae (volume.ae_ne m.rmin),ae_restrict_of_ae (volume.ae_ne (1:ℝ))]
    with r hr hcuts hr0 hr1
  exact hpoint as ho he r
    (by rw [hR0];exact ⟨lt_of_le_of_ne hr.1 hr0.symm,lt_of_le_of_ne hr.2 hr1⟩) hcuts

theorem originalRadiusWeights_comp_column_ae (f Φ : ℝ→ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) :
    ∀ᵐ r∂volume.restrict (Icc m.rmin 1),
      m.unitColumn as Finset.univ id (fun i=>Φ (comparisonOriginalRadiusWeights m.q as f i)) r=
      Φ (MassCellAveraging.sample f 0 as (m.alpha.val.val r)) := by
  have heq (r : ℝ) : m.unitColumn as Finset.univ id
        (fun i=>Φ (comparisonOriginalRadiusWeights m.q as f i)) r=
      radiusCellEnergyDensity m.R 0 as
        (fun i=>Φ (MassCellAveraging.originalCoefficient f 0 as i)) r := by
    unfold unitColumn
    rw [radiusCellEnergyDensity_eq_finite_sum,radiusCellEnergyDensity_eq_finite_sum]
    unfold finiteRadiusCellDensity
    apply Finset.sum_congr rfl
    intro i hi
    have hiFin : i<(sampleClockSteps m.q 0 as).length+1 := by
      simp only [sampleClockSteps_length]
      have := Finset.mem_range.mp hi
      omega
    simp only [nativeSelectedColumn,dite_eq_left hiFin,Finset.mem_univ,ite_true,id_eq,
      comparisonOriginalRadiusWeights]
  filter_upwards [m.originalAverage_comp_radius_density_ae f Φ as ho he] with r hr
  rw [heq r]
  exact hr

theorem sample_linear_sweep_tendsto_L1 (f : ℝ→ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hm : ∀j,PartitionMesh (mesh j) 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>∫r in Icc m.rmin 1,
      |deriv m.alpha.val.val r*MassCellAveraging.sample f 0 (as j) (m.alpha.val.val r)-
        deriv m.alpha.val.val r*f (m.alpha.val.val r)|) atTop (𝓝 0) := by
  have hiF : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hf.integrable (by norm_num))
  have heq (j : ℕ) : (∫r in Icc m.rmin 1,
      |deriv m.alpha.val.val r*MassCellAveraging.sample f 0 (as j) (m.alpha.val.val r)-
        deriv m.alpha.val.val r*f (m.alpha.val.val r)|)=
      ∫u in m.u0..1,|MassCellAveraging.sample f 0 (as j) u-f u| := by
    rw [m.mass_radius_substitution]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r _
    dsimp only
    rw [←mul_sub,abs_mul,abs_of_nonneg m.alpha.val.property.2.deriv_nonneg]
  have hbound (j : ℕ) : (∫r in Icc m.rmin 1,
      |deriv m.alpha.val.val r*MassCellAveraging.sample f 0 (as j) (m.alpha.val.val r)-
        deriv m.alpha.val.val r*f (m.alpha.val.val r)|)≤
      ∫u in (0:ℝ)..1,|MassCellAveraging.sample f 0 (as j) u-f u| := by
    rw [heq]
    exact intervalIntegral.integral_mono_interval m.hu.1 m.hu.2 le_rfl
      (Eventually.of_forall (fun _=>abs_nonneg _))
      ((MassCellAveraging.sample_integrable_comp f 0 (as j) id 0 1).sub hiF).abs
  exact squeeze_zero (fun j=>integral_nonneg (fun _=>abs_nonneg _)) hbound
    (MassCellAveraging.sample_tendsto_L1 f hf as mesh ho hm he hlim)

theorem sample_square_sweep_tendsto_L1 (f : ℝ→ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hm : ∀j,PartitionMesh (mesh j) 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>∫r in Icc m.rmin 1,
      |deriv m.alpha.val.val r*(MassCellAveraging.sample f 0 (as j) (m.alpha.val.val r))^2-
        deriv m.alpha.val.val r*(f (m.alpha.val.val r))^2|) atTop (𝓝 0) := by
  have hiFs : IntervalIntegrable (fun u=>(f u)^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr hf.integrable_sq
  have heq (j : ℕ) : (∫r in Icc m.rmin 1,
      |deriv m.alpha.val.val r*(MassCellAveraging.sample f 0 (as j) (m.alpha.val.val r))^2-
        deriv m.alpha.val.val r*(f (m.alpha.val.val r))^2|)=
      ∫u in m.u0..1,|(MassCellAveraging.sample f 0 (as j) u)^2-(f u)^2| := by
    rw [m.mass_radius_substitution]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r _
    dsimp only
    rw [←mul_sub,abs_mul,abs_of_nonneg m.alpha.val.property.2.deriv_nonneg]
  have hbound (j : ℕ) : (∫r in Icc m.rmin 1,
      |deriv m.alpha.val.val r*(MassCellAveraging.sample f 0 (as j) (m.alpha.val.val r))^2-
        deriv m.alpha.val.val r*(f (m.alpha.val.val r))^2|)≤
      ∫u in (0:ℝ)..1,|(MassCellAveraging.sample f 0 (as j) u)^2-(f u)^2| := by
    rw [heq]
    exact intervalIntegral.integral_mono_interval m.hu.1 m.hu.2 le_rfl
      (Eventually.of_forall (fun _=>abs_nonneg _))
      ((MassCellAveraging.sample_integrable_comp f 0 (as j) (fun z=>z^2) 0 1).sub hiFs).abs
  exact squeeze_zero (fun j=>integral_nonneg (fun _=>abs_nonneg _)) hbound
    (MassCellAveraging.sample_square_tendsto_L1 f hf as mesh ho hm he hlim)

theorem originalRadiusWeights_linear_tendsto_L1
    {A : Set ℝ} (hA : MeasurableSet A)
    {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin) (hfloor : ∀r∈A,kmin≤ m.k r)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0)) :
    let f := comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
    Tendsto (fun j=>∫r in Icc m.rmin 1,
      |deriv m.alpha.val.val r*m.unitColumn (as j) Finset.univ id
        (fun i=>comparisonOriginalRadiusWeights m.q (as j) f i) r-
        A.indicator (fun _=>1/x) r|) atTop (𝓝 0) := by
  dsimp only
  let f := comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
  have hf := comparisonRadiusMassWeight_memLp_two m.R m.alpha.val.val
    m.R_monotone.measurable hA hx hkmin
  have hl := m.sample_linear_sweep_tendsto_L1 f hf as mesh ho hmesh hend hlim
  have heq (j : ℕ) : (∫r in Icc m.rmin 1,
      |deriv m.alpha.val.val r*m.unitColumn (as j) Finset.univ id
        (fun i=>comparisonOriginalRadiusWeights m.q (as j) f i) r-
        A.indicator (fun _=>1/x) r|)=
      ∫r in Icc m.rmin 1,
        |deriv m.alpha.val.val r*MassCellAveraging.sample f 0 (as j) (m.alpha.val.val r)-
          deriv m.alpha.val.val r*f (m.alpha.val.val r)| := by
    apply integral_congr_ae
    filter_upwards [m.originalRadiusWeights_comp_column_ae f id (as j) (ho j) (hend j),
      m.radiusMassWeight_linear_pullback hx hkmin hfloor] with r hcol hfixed
    simp only [id_eq] at hcol
    rw [hcol,←hfixed]
  convert hl using 1
  funext j
  exact heq j

theorem originalRadiusWeights_square_tendsto_L1
    {A : Set ℝ} (hA : MeasurableSet A)
    {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin) (hfloor : ∀r∈A,kmin≤ m.k r)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0)) :
    let f := comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
    Tendsto (fun j=>∫r in Icc m.rmin 1,
      |deriv m.alpha.val.val r*m.unitColumn (as j) Finset.univ id
        (fun i=>(comparisonOriginalRadiusWeights m.q (as j) f i)^2) r-
        A.indicator (comparisonReciprocalDensityWeight m.alpha.val.val x kmin) r|) atTop (𝓝 0) := by
  dsimp only
  let f := comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
  have hf := comparisonRadiusMassWeight_memLp_two m.R m.alpha.val.val
    m.R_monotone.measurable hA hx hkmin
  have hl := m.sample_square_sweep_tendsto_L1 f hf as mesh ho hmesh hend hlim
  have heq (j : ℕ) : (∫r in Icc m.rmin 1,
      |deriv m.alpha.val.val r*m.unitColumn (as j) Finset.univ id
        (fun i=>(comparisonOriginalRadiusWeights m.q (as j) f i)^2) r-
        A.indicator (comparisonReciprocalDensityWeight m.alpha.val.val x kmin) r|)=
      ∫r in Icc m.rmin 1,
        |deriv m.alpha.val.val r*(MassCellAveraging.sample f 0 (as j) (m.alpha.val.val r))^2-
          deriv m.alpha.val.val r*(f (m.alpha.val.val r))^2| := by
    apply integral_congr_ae
    filter_upwards [m.originalRadiusWeights_comp_column_ae f (fun z=>z^2) (as j) (ho j) (hend j),
      m.radiusMassWeight_square_pullback hx hkmin hfloor] with r hcol hfixed
    rw [hcol,←hfixed]
  convert hl using 1
  funext j
  exact heq j

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
