module

public import ComparisonNativeRadiusVarianceAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

namespace MassCellAveraging

theorem abs_le_square_div_add (v : ℝ) {t : ℝ} (ht : 0<t) :
    |v| ≤ v^2/t+t := by
  have h : |v| * t ≤ v^2+t^2 := by nlinarith [sq_nonneg (|v|-t),sq_abs v]
  calc
    |v| ≤ (v^2+t^2)/t := (le_div_iff₀ ht).mpr h
    _ = v^2/t+t := by field_simp <;> ring

theorem sample_eventually_L1 (f : ℝ→ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hm : ∀j,PartitionMesh (mesh j) 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (hlim : Tendsto mesh atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠ j in atTop,(∫u in (0:ℝ)..1,|sample f 0 (as j) u-f u|) ≤ epsilon := by
  have hiF : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hf.integrable (by norm_num))
  let t := epsilon/2
  have ht : 0<t := by dsimp [t];positivity
  have heta : 0<epsilon*t/2 := by positivity
  filter_upwards [sample_memLp_two_eventually_square f hf as mesh ho hm he hlim heta] with j hj
  have hiP := sample_integrable_comp f 0 (as j) id 0 1
  have hiErr : IntervalIntegrable (fun u=>(sample f 0 (as j) u-f u)^2) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      ((sample_memLp_two f 0 (as j)).sub hf).integrable_sq
  have hbound := intervalIntegral.integral_mono_on zero_le_one (hiP.sub hiF).abs
    ((hiErr.div_const t).add intervalIntegrable_const)
    (fun u _=>abs_le_square_div_add (sample f 0 (as j) u-f u) ht)
  rw [intervalIntegral.integral_add (hiErr.div_const t) intervalIntegrable_const,
    intervalIntegral.integral_div,intervalIntegral.integral_const] at hbound
  have herror : (∫u in (0:ℝ)..1,(sample f 0 (as j) u-f u)^2)/t ≤ epsilon/2 := by
    apply (div_le_iff₀ ht).mpr
    nlinarith [hj]
  dsimp [t] at hbound herror
  norm_num only [sub_zero,one_smul] at hbound
  linarith

theorem sample_tendsto_L1 (f : ℝ→ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hm : ∀j,PartitionMesh (mesh j) 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>∫u in (0:ℝ)..1,|sample f 0 (as j) u-f u|) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun j=>ha.trans_le (intervalIntegral.integral_nonneg_of_ae
      zero_le_one (Eventually.of_forall (fun u=>abs_nonneg _))))
  · intro b hb
    filter_upwards [sample_eventually_L1 f hf as mesh ho hm he hlim (by linarith : 0<b/2)]
      with j hj
    exact hj.trans_lt (by linarith)
end MassCellAveraging
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparison_originalAverage_linear_radius_density_ae
    (α : inverseIntegralConstraints 0 0 k M) (f : ℝ→ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
      radiusCellEnergyDensity R 0 as (fun i=>MassCellAveraging.originalCoefficient f 0 as i) r=
        MassCellAveraging.sample f 0 as (α.val.val r) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  have hR : Monotone R := comparisonSweepQuantile_monotone hc hk hkc hm hM α
  have hR1 : R 1=1 := by
    have ht := comparisonSweepQuantile_inverse hc hk hkc hm hM α (by norm_num : (1:ℝ)∈Icc 0 1)
    simpa only [α.property.2.1] using ht
  have hR0 : R 0=0 := by
    have ht := comparisonSweepQuantile_inverse hc hk hkc hm hM α (by norm_num : (0:ℝ)∈Icc 0 1)
    simpa only [α.property.1] using ht
  have hcut : ∀ᵐ r∂volume,∀v∈as,r ≠ R v.val := by
    clear ho he
    induction as with
    | nil=>exact Eventually.of_forall (fun _ _ h=>by simp at h)
    | cons b bs ih=>
      filter_upwards [volume.ae_ne (R b.val),ih] with r hr hi v hv
      rcases List.mem_cons.mp hv with heq|hm
      · subst v;exact hr
      · exact hi v hm
  have hpoint {a : ℝ} (bs : List PositiveMass) (hord : MassOrdered a bs)
      (hend : partitionEnd a bs=1) (r : ℝ) (hr : r∈Ioo (R a) 1)
      (hcuts : ∀v∈bs,r ≠ R v.val) :
      radiusCellEnergyDensity R a bs (fun i=>MassCellAveraging.originalCoefficient f a bs i) r=
        MassCellAveraging.sample f a bs (α.val.val r) := by
    induction bs generalizing a with
    | nil=>
      simp only [partitionEnd] at hend
      subst a
      rw [hR1] at hr
      exact False.elim (not_lt_of_ge hr.1.le hr.2)
    | cons b bs ih=>
      have hrI : r∈Icc (0:ℝ) 1 :=
        ⟨(comparisonSweepQuantile_bounds hc hk hkc hm hM α a).1.trans hr.1.le,hr.2.le⟩
      have hbI := comparisonSweepQuantile_bounds hc hk hkc hm hM α b.val
      have hmass : α.val.val (R b.val)=b.val :=
        comparisonSweepQuantile_mass_spec hc hk hkc hm hM α (massOrdered_bounds hord.2.2)
      by_cases hrb : r<R b.val
      · have hum : α.val.val r<b.val := by
          have hs := inverseConstraint_strictMonoOn hc hk hkc α.property hrI hbI hrb
          rwa [hmass] at hs
        have hcell : r∈Ioc (R a) (R b.val) := ⟨hr.1,hrb.le⟩
        rw [radiusCellEnergyDensity,indicator_of_mem hcell,
          radiusCellEnergyDensity_eq_zero_of_le R hR bs hord.2.2 _ hrb.le,add_zero,
          MassCellAveraging.sample,ite_eq_left hum]
        simp only [MassCellAveraging.originalCoefficient,partitionPoint,partitionValues,partitionValues_zero,id_eq]
      · have hneq := hcuts b (List.mem_cons_self)
        have hlt : R b.val<r := lt_of_le_of_ne (le_of_not_gt hrb) hneq.symm
        have hum : b.val ≤ α.val.val r := by
          have hs := α.val.property.2 hlt.le
          rwa [hmass] at hs
        have hnot : r∉Ioc (R a) (R b.val) := fun hc=>not_le_of_gt hlt hc.2
        rw [radiusCellEnergyDensity,indicator_of_notMem hnot,zero_add,
          MassCellAveraging.sample,ite_eq_right (not_lt.mpr hum)]
        exact ih hord.2.2 hend ⟨hlt,hr.2⟩ (fun v hv=>hcuts v (List.mem_cons_of_mem _ hv))
  filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae hcut,
    ae_restrict_of_ae (volume.ae_ne (0:ℝ)),ae_restrict_of_ae (volume.ae_ne (1:ℝ))] with r hr hcuts hr0 hr1
  exact hpoint as ho he r (by rw [hR0];exact ⟨lt_of_le_of_ne hr.1 hr0.symm,lt_of_le_of_ne hr.2 hr1⟩) hcuts

theorem comparison_originalRadiusWeights_linear_column_ae {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) (f : ℝ→ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) :
    ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
      comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as Finset.univ id
        (fun i=>comparisonOriginalRadiusWeights q as f i) r=
      MassCellAveraging.sample f 0 as (α.val.val r) := by
  have heq (r : ℝ) : comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as Finset.univ id
        (fun i=>comparisonOriginalRadiusWeights q as f i) r=
      radiusCellEnergyDensity (comparisonSweepQuantile hc hk hkc hm hM α) 0 as
        (fun i=>MassCellAveraging.originalCoefficient f 0 as i) r := by
    unfold comparisonNativeUnitColumnWeight
    rw [radiusCellEnergyDensity_eq_finite_sum,radiusCellEnergyDensity_eq_finite_sum]
    unfold finiteRadiusCellDensity
    apply Finset.sum_congr rfl
    intro i hi
    have hiFin : i<(sampleClockSteps q 0 as).length+1 := by
      simp only [sampleClockSteps_length]
      have := Finset.mem_range.mp hi
      omega
    simp only [nativeSelectedColumn,dite_eq_left hiFin,Finset.mem_univ,ite_true,id_eq,
      comparisonOriginalRadiusWeights]
  filter_upwards [comparison_originalAverage_linear_radius_density_ae hc hk hkc hm hM α f as ho he] with r hr
  rw [heq r]
  exact hr

include hc hk hkc hm hM in
theorem comparison_sample_linear_sweep_tendsto_L1
    (α : inverseIntegralConstraints 0 0 k M) (f : ℝ→ℝ)
    (hf : MemLp f 2 (volume.restrict (Ioc (0:ℝ) 1)))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1) (hlim : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j=>∫r in Icc (0:ℝ) 1,
      |deriv α.val.val r*MassCellAveraging.sample f 0 (as j) (α.val.val r)-
        deriv α.val.val r*f (α.val.val r)|) atTop (𝓝 0) := by
  have heq (j:ℕ) : (∫r in Icc (0:ℝ) 1,
      |deriv α.val.val r*MassCellAveraging.sample f 0 (as j) (α.val.val r)-
        deriv α.val.val r*f (α.val.val r)|)=
      ∫u in (0:ℝ)..1,|MassCellAveraging.sample f 0 (as j) u-f u| := by
    rw [comparisonSweep_mass_substitution hc hk hkc hm hM α]
    apply setIntegral_congr_fun measurableSet_Icc
    intro r _
    dsimp only
    rw [←mul_sub,abs_mul,abs_of_nonneg (comparisonSweep_density_nonneg α r)]
  simp_rw [heq]
  exact MassCellAveraging.sample_tendsto_L1 f hf as mesh ho hmesh he hlim

theorem comparison_originalRadiusWeights_linear_tendsto_L1 {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Icc (0:ℝ) 1)
    {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin) (hfloor : ∀r∈A,kmin ≤ k r)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0)) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let f := comparisonRadiusMassWeight R α.val.val A x kmin
    Tendsto (fun j=>∫r in Icc (0:ℝ) 1,
      |deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        Finset.univ id (fun i=>comparisonOriginalRadiusWeights q (as j) f i) r-
        A.indicator (fun _=>1/x) r|) atTop (𝓝 0) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let f := comparisonRadiusMassWeight R α.val.val A x kmin
  have hf := comparisonRadiusMassWeight_memLp_two R α.val.val
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α).measurable hA hx hkmin
  have hlimNative := comparison_sample_linear_sweep_tendsto_L1 hc hk hkc hm hM
    α f hf as mesh ho hmesh hend hlim
  have heq (j:ℕ) : (∫r in Icc (0:ℝ) 1,
      |deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        Finset.univ id (fun i=>comparisonOriginalRadiusWeights q (as j) f i) r-
        A.indicator (fun _=>1/x) r|)=
      ∫r in Icc (0:ℝ) 1,
        |deriv α.val.val r*MassCellAveraging.sample f 0 (as j) (α.val.val r)-
          deriv α.val.val r*f (α.val.val r)| := by
    apply integral_congr_ae
    filter_upwards [comparison_originalRadiusWeights_linear_column_ae hc hk hkc hm hM q α f (as j) (ho j) (hend j),
      comparisonRadiusMassWeight_linear_pullback hc hk hkc hm hM α hA hAD hx hkmin hfloor]
      with r hcol hfixed
    rw [hcol,←hfixed]
  convert hlimNative using 1
  funext j
  exact heq j

end
end OAI.SKFluctuations.LaplaceWindowFormalization
