module

public import ComparisonNativeRadiusRawEndpoint

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2400000
attribute [local instance] Classical.propDecidable

namespace MassCellAveraging

def originalCoefficient (f : ℝ→ℝ) (a : ℝ) (as : List PositiveMass) (i : ℕ) : ℝ :=
  average f (partitionPoint a as i) (partitionPoint a as (i+1))

theorem sample_on_original_cell (f : ℝ→ℝ) {a : ℝ} (as : List PositiveMass)
    (ho : MassOrdered a as) {i : ℕ} (hi : i<as.length) {u : ℝ}
    (hu : u∈Ioo (partitionPoint a as i) (partitionPoint a as (i+1))) :
    sample f a as u=originalCoefficient f a as i := by
  induction as generalizing a i with
  | nil=>simp at hi
  | cons b bs ih=>
    cases i with
    | zero=>
      have hu' : a<u ∧ u<b.val := by
        simpa only [partitionPoint,partitionValues,partitionValues_zero,id_eq,mem_Ioo] using hu
      replace hu := hu'
      simp only [sample,ite_eq_left hu.2,originalCoefficient,partitionPoint,partitionValues,partitionValues_zero,id_eq]
    | succ i=>
      have hm := (partitionPoint_mem bs ho.2.2 i).1
      have hbu : b.val ≤ u := hm.trans hu.1.le
      rw [sample,ite_eq_right (not_lt.mpr hbu)]
      exact ih ho.2.2 (by simpa using hi) hu

end MassCellAveraging
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparison_originalAverage_radius_density_ae
    (α : inverseIntegralConstraints 0 0 k M) (f : ℝ→ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
      radiusCellEnergyDensity R 0 as (fun i=>(MassCellAveraging.originalCoefficient f 0 as i)^2) r=
        (MassCellAveraging.sample f 0 as (α.val.val r))^2 := by
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
      radiusCellEnergyDensity R a bs (fun i=>(MassCellAveraging.originalCoefficient f a bs i)^2) r=
        (MassCellAveraging.sample f a bs (α.val.val r))^2 := by
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

def comparisonOriginalRadiusWeights {ι : Type} (q : ℝ→ι→ℝ≥0)
    (as : List PositiveMass) (f : ℝ→ℝ) : Fin ((sampleClockSteps q 0 as).length+1)→ℝ :=
  fun i=>MassCellAveraging.originalCoefficient f 0 as i.val

theorem comparison_originalRadiusWeights_column_ae {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) (f : ℝ→ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) :
    ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
      comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as Finset.univ id
        (fun i=>(comparisonOriginalRadiusWeights q as f i)^2) r=
      (MassCellAveraging.sample f 0 as (α.val.val r))^2 := by
  have heq (r : ℝ) : comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as Finset.univ id
        (fun i=>(comparisonOriginalRadiusWeights q as f i)^2) r=
      radiusCellEnergyDensity (comparisonSweepQuantile hc hk hkc hm hM α) 0 as
        (fun i=>(MassCellAveraging.originalCoefficient f 0 as i)^2) r := by
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
  filter_upwards [comparison_originalAverage_radius_density_ae hc hk hkc hm hM α f as ho he] with r hr
  rw [heq r]
  exact hr

end
end OAI.SKFluctuations.LaplaceWindowFormalization
