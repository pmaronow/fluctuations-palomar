module

public import VariableEndpointPhysicalRegularity
public import ActualComparisonCaps
public import PhysicalLocalCapPathBound

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def sampleParameterDurations (R : ℝ→ℝ) : ℝ→List PositiveMass→List ℝ≥0
  | _,[]=>[]
  | u,a::as=>(R a.val-R u).toNNReal::sampleParameterDurations R a.val as

theorem sampleParameterDurations_total (R : ℝ→ℝ) (hR : Monotone R)
    {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as) :
    ((sampleParameterDurations R u as).map fun (w:ℝ≥0)=>(w:ℝ)).sum=
      R (partitionEnd u as)-R u := by
  induction as generalizing u with
  | nil=>simp [sampleParameterDurations,partitionEnd]
  | cons a as ih=>
    simp only [sampleParameterDurations,List.map_cons,List.sum_cons,
      Real.coe_toNNReal _ (sub_nonneg.mpr (hR ho.2.1)),partitionEnd]
    rw [ih ho.2.2]
    ring

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonVariableEndpointField_radius_gap
    {N d lam u v z : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hd : 0 < d) (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (h : ℝ→ℝ) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (hu : u∈Icc (0:ℝ) 1) (hv : v∈Icc (0:ℝ) 1) (huv : u ≤ v)
    (hz : z ≤ 1) (hRz : comparisonSweepQuantile hc hk hkc hm hM α v ≤ z) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let F := fun x=>h x+laplaceComparisonStrength d lam (R x)*R x
    ((1/3)/Real.log N)*laplaceComparisonStrength d lam z*(R v-R u) ≤
      ((F v).toNNReal-(F u).toNNReal:ℝ≥0) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let g := laplaceComparisonStrength d lam
  let κ := (1/3)/Real.log N
  have hRu := comparisonSweepQuantile_bounds hc hk hkc hm hM α u
  have hRv := comparisonSweepQuantile_bounds hc hk hkc hm hM α v
  have hRuv := comparisonSweepQuantile_monotone hc hk hkc hm hM α huv
  have hgap := laplaceComparisonField_radius_gap hN hlog hd hnd hlam hld hRu.1 hRuv hRv.2
  have hκ : 0 < κ := div_pos (by norm_num) (by linarith)
  have hgz : g z ≤ g (R v) :=
    (laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) le_rfl).1
      hRv ⟨hRv.1.trans hRz,hz⟩ hRz
  have hprod := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hgz hκ.le) (sub_nonneg.mpr hRuv)
  have huF : 0 ≤ h u+g (R u)*R u := add_nonneg
    (hh0.trans (hh (by norm_num) hu hu.1)) (mul_nonneg (laplaceComparisonStrength_pos d hlam _).le hRu.1)
  have hvF : 0 ≤ h v+g (R v)*R v := add_nonneg
    (hh0.trans (hh (by norm_num) hv hv.1)) (mul_nonneg (laplaceComparisonStrength_pos d hlam _).le hRv.1)
  change κ*g z*(R v-R u) ≤ _
  rw [NNReal.coe_sub_def,Real.coe_toNNReal _ hvF,Real.coe_toNNReal _ huF]
  apply le_trans _ (le_max_left _ _)
  have hhm := hh hu hv huv
  change κ*g (R v)*(R v-R u) ≤ g (R v)*R v-g (R u)*R u at hgap
  nlinarith

theorem comparisonSampledField_radius_slope
    {N d lam u z : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hd : 0 < d) (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (b h : ℝ→ℝ) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0)
    (α : inverseIntegralConstraints 0 0 k M) (n : ℕ)
    (as : List PositiveMass) (ho : MassOrdered u as)
    (hu : u∈Icc (0:ℝ) 1) (hz : z ≤ 1)
    (has : ∀a∈as,a.val ≤ 1 ∧ comparisonSweepQuantile hc hk hkc hm hM α a.val ≤ z) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun x=>(b x-laplaceComparisonStrength d lam (R x)).toNNReal
    let hf := fun x=>(h x+laplaceComparisonStrength d lam (R x)*R x).toNNReal
    List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1)))=>
      ((1/3)/Real.log N)*laplaceComparisonStrength d lam z*(w:ℝ) ≤ st.2 (Sum.inl 0))
      (sampleParameterDurations R u as)
      (sampleClockSteps (completedPathClock (n+1) bf hf) u as) := by
  dsimp only
  induction as generalizing u with
  | nil=>exact List.Forall₂.nil
  | cons a as ih=>
    apply List.Forall₂.cons
    · change ((1/3)/Real.log N)*laplaceComparisonStrength d lam z*
        ((comparisonSweepQuantile hc hk hkc hm hM α a.val-comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal:ℝ) ≤ _
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr
        (comparisonSweepQuantile_monotone hc hk hkc hm hM α ho.2.1))]
      exact comparisonVariableEndpointField_radius_gap hc hk hkc hm hM
        hN hlog hd hnd hlam hld h hh hh0 α hu
        ⟨a.property.le,(has a (by simp)).1⟩ ho.2.1 hz (has a (by simp)).2
    · exact ih ho.2.2 ⟨a.property.le,(has a (by simp)).1⟩
        (fun b hb=>has b (List.mem_cons_of_mem _ hb))

theorem comparisonSampledRadius_duration_mesh
    (α : inverseIntegralConstraints 0 0 k M) {u mesh : ℝ}
    (as : List PositiveMass) (ho : MassOrdered u as) (hmesh : PartitionMesh mesh u as) :
    ∀w∈sampleParameterDurations (comparisonSweepQuantile hc hk hkc hm hM α) u as,
      (w:ℝ) ≤ mesh/c := by
  induction as generalizing u with
  | nil=>simp [sampleParameterDurations]
  | cons a as ih=>
    intro w hw
    rcases List.mem_cons.mp hw with hw|hw
    · subst w
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr
        (comparisonSweepQuantile_monotone hc hk hkc hm hM α ho.2.1))]
      have hb := (comparisonSweepQuantile_lipschitz hc hk hkc hm hM α).dist_le_mul a.val u
      simp only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr ho.2.1),
        abs_of_nonneg (sub_nonneg.mpr (comparisonSweepQuantile_monotone hc hk hkc hm hM α ho.2.1))] at hb
      change _ ≤ (1/c)*(a.val-u) at hb
      have hh := mul_le_mul_of_nonneg_left hmesh.1 (by positivity : 0 ≤ 1/c)
      exact hb.trans (by convert hh using 1 <;> ring)
    · exact ih ho.2.2 hmesh.2 w hw
end
end OAI.SKFluctuations.LaplaceWindowFormalization
