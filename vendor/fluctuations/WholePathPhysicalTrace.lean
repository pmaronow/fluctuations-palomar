module

public import BoundaryCapMassCellSum
public import PhysicalBoundaryCapLaw
public import SKFluctuationsOAI.Probability.SKFluctuations.InverseConstraintNonempty
public import ActualMacroClockGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem completedSampledField_gap {n : ℕ} (hn : 0 < n)
    (b h : ℝ → ℝ≥0) {g a : ℝ} (as : List PositiveMass) (ha : MassOrdered a as)
    (hgap : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      g*(v-u) ≤ (h v:ℝ)-(h u:ℝ)) :
    List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex n)) =>
      g*(w:ℝ) ≤ st.2 (Sum.inl ⟨0,hn⟩))
      (sampleMassDurations a as) (sampleClockSteps (completedPathClock n b h) a as) := by
  induction as generalizing a with
  | nil => exact List.Forall₂.nil
  | cons c cs ih =>
    apply List.Forall₂.cons
    · change g*((c.val-a).toNNReal:ℝ) ≤ ((h c.val-h a:ℝ≥0):ℝ)
      rw [Real.coe_toNNReal _ (sub_nonneg.mpr ha.2.1),NNReal.coe_sub_def]
      exact (hgap a (massOrdered_bounds ha) c.val (massOrdered_bounds ha.2.2)
        ha.2.1).trans (le_max_left _ _)
    · exact ih ha.2.2

theorem physicalPathSecondMoment_le_one (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) {j : ℕ} (hj : j ≤ steps.length) :
    physicalPathSecondMoment n steps q₀ j ≤ 1 := by
  rw [physicalSecondMoment_eq_rootLevelPairMean n steps ha q₀ j hj]
  exact (rootLevelPairMean_SK_bounds n (uniformWeight_pos n) (finiteFeature n) q₀ steps ha j).2.1

theorem completedSampledWholePath_trace_le (n dim : ℕ)
    (e : Fin (dim+1) ≃ FeatureIndex (n+1))
    (b h : ℝ → ℝ≥0) {g mesh : ℝ} (hg : 0 < g) (hmesh0 : 0 ≤ mesh)
    (as : List PositiveMass) (ha : MassOrdered 0 as)
    (hmesh : ∀ w ∈ sampleMassDurations 0 as, (w:ℝ) ≤ mesh)
    (hgap : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      g*(v-u) ≤ (h v:ℝ)-(h u:ℝ)) :
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    massCellSum as 0 (fun j =>
      ∫ p, physicalCutSourceSquareTrace (n+1) steps id j p
        ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps) ≤
      2/((n+1:ℝ)*g)+2*mesh := by
  dsimp only
  let q := completedPathClock (n+1) b h
  let steps := sampleClockSteps q 0 as
  have ho : OrderedSteps 0 steps := sampleClockSteps_ordered q as ha
  have hl : (sampleMassDurations 0 as).length ≤ steps.length := by
    have heq {a : ℝ} (bs : List PositiveMass) : (sampleMassDurations a bs).length = bs.length := by
      induction bs generalizing a with
      | nil => rfl
      | cons c cs ih => simp only [sampleMassDurations,List.length_cons,ih]
    change (sampleMassDurations 0 as).length ≤ (sampleClockSteps q 0 as).length
    simp only [heq,sampleClockSteps_length,le_refl]
  have hh := physicalWeightedCutSquareTrace_le_pathSecondMoment n dim e (q 0)
    (sampleMassDurations 0 as) steps [] (by simpa using ho) hl hmesh0 hmesh hg
    (sampledFieldClock_aligned (n+1) (by omega) b h as 0)
    (completedSampledField_gap (by omega : 0 < n+1) b h as ha hgap)
    (by simpa using physicalPathSecondMoment_le_one (n+1) steps ho (q 0) (j := steps.length) le_rfl)
  rw [physicalWeightedCutSum_sampleMassDurations as ha] at hh
  let F := fun ss : List (GaussianStep (FeatureIndex (n+1))) =>
    massCellSum as 0 (fun j =>
      ∫ p, physicalCutSourceSquareTrace (n+1) ss id j p
        ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) ss)
  simp only [mul_one] at hh
  change F (steps++[]) ≤ 2/((n+1:ℝ)*g)+2*mesh at hh
  change F steps ≤ 2/((n+1:ℝ)*g)+2*mesh
  rwa [List.append_nil] at hh

theorem macroSampledWholePath_trace_le {η Q t bstar mesh : ℝ}
    (hη : 0 < η) (hQ : 1 < Q) (ht : 0 < t) (hbstar : 0 < bstar)
    (α : MacroInverseClass η Q) (n dim : ℕ)
    (e : Fin (dim+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u)
    (hmesh0 : 0 ≤ mesh) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (hmesh : ∀ w ∈ sampleMassDurations 0 as, (w:ℝ) ≤ mesh) :
    let q := completedPathClock (n+1) (fun u => (b u).toNNReal)
      (fun u => (h u+t*b u*macroInverseQuantile hη hQ α u).toNNReal)
    let steps := sampleClockSteps q 0 as
    massCellSum as 0 (fun j =>
      ∫ p, physicalCutSourceSquareTrace (n+1) steps id j p
        ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps) ≤
      2/((n+1:ℝ)*(t*bstar/Q))+2*mesh := by
  have hnon (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      0 ≤ h u+t*b u*macroInverseQuantile hη hQ α u :=
    add_nonneg (hhn u hu) (mul_nonneg (mul_nonneg ht.le (hbstar.le.trans (hbb u hu)))
      (macroInverseQuantile_bounds hη hQ α u).1)
  apply completedSampledWholePath_trace_le n dim e _ _
    (div_pos (mul_pos ht hbstar) (zero_lt_one.trans hQ)) hmesh0 as ha hmesh
  intro u hu v hv huv
  rw [Real.coe_toNNReal _ (hnon v hv),Real.coe_toNNReal _ (hnon u hu)]
  exact macro_inverse_field_gap hη hQ α b h ht.le hbstar.le hb hh hbb hu hv huv

end OAI.SKFluctuations.LaplaceWindowFormalization
