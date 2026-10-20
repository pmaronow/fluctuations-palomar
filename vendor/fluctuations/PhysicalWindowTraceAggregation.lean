module

public import PhysicalCutSusceptibilityMean
public import BoundaryCapMassCellSum
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalDyadicClock

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

theorem physicalRootedRadiusWindowSusceptibility_eq_trace (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ) :
    (∫ p, physicalSusceptibilityMassIntegral n steps id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut r) p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) =
    ∑ j, physicalWindowCellMass steps 0 J j *
      (∫ p, physicalCutSourceMixedTrace n steps id j.val p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) := by
  have h := physicalRadiusWindowSusceptibility_integral_eq_trace n steps ha
    (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id J r hr hc
  simpa only [Kernel.comap_id, rootedHierarchyPathLaw] using h

theorem physicalRootedRadiusWindowSusceptibility_le_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (r : Fin (steps.length+2) → ℝ) (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ)
    {a : ℝ} (ha0 : 0 < a)
    (hcut : ∀ j ∈ J, a ≤ physicalCutMass 0 steps j.val) :
    (∫ p, physicalSusceptibilityMassIntegral n steps id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut r) p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) ≤
    (∑ j, physicalWindowCellMass steps 0 J j *
      (∫ p, physicalCutSourceSquareTrace n steps id j.val p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps)) / a := by
  rw [physicalRootedRadiusWindowSusceptibility_eq_trace n steps ha q₀ J r hr hc,
    Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  by_cases hj : j ∈ J
  · have h := physicalCutSusceptibility_integral_le_square_of_cutMass n steps ha ha0
      (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id j.val (hcut j hj)
    rw [physicalCutSusceptibility_integral_eq_trace n steps ha
      (Measure.pi fun i => gaussianReal 0 (q₀ i)) id measurable_id j.val] at h
    simp only [Kernel.comap_id] at h
    simpa only [mul_div_assoc, rootedHierarchyPathLaw] using
      mul_le_mul_of_nonneg_left h (physicalWindowCellMass_nonneg steps ha J j)
  · simp [physicalWindowCellMass, hj]

theorem physicalWindowCellSum_eq_Ico {ι : Type}
    (steps : List (GaussianStep ι)) (a : ℝ) {p q : ℕ}
    (hq : q ≤ steps.length+1) (f : ℕ → ℝ) :
    (∑ j, physicalWindowCellMass steps a (physicalIntervalCells steps p q) j * f j.val) =
      ∑ j ∈ Finset.Ico p q,
        (physicalCutMass a steps (j+1)-physicalCutMass a steps j) * f j := by
  simp only [physicalWindowCellMass, ite_mul, zero_mul,
    Finset.sum_ite_mem, Finset.univ_inter]
  simp_rw [pathMassDifferences_eq_cutMass]
  apply Finset.sum_bij (fun j _ => j.val)
  · intro j hj
    exact Finset.mem_Ico.mpr ((mem_physicalIntervalCells steps p q j).mp hj)
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro j hj
    have hj' := Finset.mem_Ico.mp hj
    let i : Fin (steps.length+1) := ⟨j, hj'.2.trans_le hq⟩
    exact ⟨i, (mem_physicalIntervalCells steps p q i).mpr hj', rfl⟩
  · intros
    rfl

theorem physicalCutMass_append_prefix {ι : Type}
    (before after : List (GaussianStep ι)) (a : ℝ) (j : ℕ) (hj : j ≤ before.length) :
    physicalCutMass a (before++after) j = physicalCutMass a before j := by
  induction before generalizing a j with
  | nil =>
    have : j=0 := by simpa using hj
    subst j
    simp [physicalCutMass]
  | cons st before ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih st.1 j (by simpa using hj)

theorem physicalCutMass_append_shift {ι : Type}
    (before after : List (GaussianStep ι)) (a : ℝ) (j : ℕ) :
    physicalCutMass a (before++after) (before.length+j) =
      physicalCutMass (physicalCutMass a before before.length) after j := by
  induction before generalizing a with
  | nil => simp [physicalCutMass]
  | cons st before ih =>
    simpa only [List.cons_append, List.length_cons, Nat.succ_add,
      physicalCutMass] using ih st.1

theorem physicalPartitionPoint_length (a : ℝ) (as : List PositiveMass) :
    partitionPoint a as as.length = partitionEnd a as := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih => exact ih b.val

theorem physicalSampledCutMass_internal {ι : Type}
    (q : ℝ → ι → ℝ≥0) (before band : List PositiveMass)
    (tail : List (GaussianStep ι)) {a : ℝ} (hend : partitionEnd 0 before=a)
    (j : ℕ) (hj : j ≤ band.length) :
    physicalCutMass 0
      ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
      (before.length+j) = partitionPoint a band j := by
  rw [List.append_assoc]
  have hlen := sampleClockSteps_length q 0 before
  rw [← hlen, physicalCutMass_append_shift, hlen,
    physicalCutMass_sampleClockSteps q 0 before _ le_rfl,
    physicalPartitionPoint_length, hend, physicalCutMass_append_prefix]
  · exact physicalCutMass_sampleClockSteps q a band j hj
  · simpa only [sampleClockSteps_length] using hj

theorem massCellSum_eq_partitionPoint_sum (as : List PositiveMass) (a : ℝ) (f : ℕ → ℝ) :
    massCellSum as a f = ∑ j ∈ Finset.range as.length,
      (partitionPoint a as (j+1)-partitionPoint a as j)*f j := by
  induction as generalizing a f with
  | nil => simp [massCellSum]
  | cons b bs ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [massCellSum, partitionPoint, partitionValues]
    rw [ih]
    simp only [partitionPoint, partitionValues_zero, id_eq]
    ring

theorem physicalWindowCellSum_internal_massCellSum {ι : Type}
    (q : ℝ → ι → ℝ≥0) (before band : List PositiveMass)
    (tail : List (GaussianStep ι)) {a : ℝ} (hend : partitionEnd 0 before=a)
    (f : ℕ → ℝ) :
    let steps := ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
    (∑ j, physicalWindowCellMass steps 0
      (physicalIntervalCells steps before.length (before.length+band.length)) j * f j.val) =
    massCellSum band a (fun j => f (before.length+j)) := by
  dsimp only
  have hq : before.length+band.length ≤
      ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail).length+1 := by
    simp only [List.length_append, sampleClockSteps_length]
    omega
  rw [physicalWindowCellSum_eq_Ico _ _ hq, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_left]
  rw [massCellSum_eq_partitionPoint_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Finset.mem_range.mp hj
  rw [show before.length+j+1 = before.length+(j+1) by omega,
    physicalSampledCutMass_internal q before band tail hend (j+1) (by omega),
    physicalSampledCutMass_internal q before band tail hend j (by omega)]

theorem physicalRootedRadiusWindowSusceptibility_internal_eq_massCellSum (n : ℕ)
    (q : ℝ → FeatureIndex n → ℝ≥0) (before band : List PositiveMass)
    (tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (hend : partitionEnd 0 before=a)
    (ha : OrderedSteps 0 ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail))
    (r : Fin (((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail).length+2) → ℝ)
    (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass
      ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail) 0
      (physicalIntervalCells ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
        before.length (before.length+band.length)) j ≠ 0 → r j.castSucc < r j.succ) :
    let steps := ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
    let J := physicalIntervalCells steps before.length (before.length+band.length)
    (∫ p, physicalSusceptibilityMassIntegral n steps id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut r) p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) (q 0) steps) =
    massCellSum band a (fun j =>
      ∫ p, physicalCutSourceMixedTrace n steps id (before.length+j) p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) (q 0) steps) := by
  dsimp only
  rw [physicalRootedRadiusWindowSusceptibility_eq_trace n _ ha (q 0) _ r hr hc]
  exact physicalWindowCellSum_internal_massCellSum q before band tail hend
    (fun k => ∫ p, physicalCutSourceMixedTrace n
      ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail) id k p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) (q 0)
        ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail))

theorem physicalRootedRadiusWindowSusceptibility_internal_le_massCellSum (n : ℕ)
    (q : ℝ → FeatureIndex n → ℝ≥0) (before band : List PositiveMass)
    (tail : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha0 : 0 < a)
    (hend : partitionEnd 0 before=a) (hband : MassOrdered a band)
    (ha : OrderedSteps 0 ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail))
    (r : Fin (((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail).length+2) → ℝ)
    (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass
      ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail) 0
      (physicalIntervalCells ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
        before.length (before.length+band.length)) j ≠ 0 → r j.castSucc < r j.succ) :
    let steps := ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
    let J := physicalIntervalCells steps before.length (before.length+band.length)
    (∫ p, physicalSusceptibilityMassIntegral n steps id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut r) p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) (q 0) steps) ≤
    massCellSum band a (fun j =>
      ∫ p, physicalCutSourceSquareTrace n steps id (before.length+j) p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) (q 0) steps) / a := by
  dsimp only
  have hcut : ∀ j ∈ physicalIntervalCells
      ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
      before.length (before.length+band.length),
      a ≤ physicalCutMass 0
        ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail) j.val := by
    intro j hj
    have hj' := (mem_physicalIntervalCells _ _ _ j).mp hj
    have hindex : before.length+(j.val-before.length)=j.val := Nat.add_sub_of_le hj'.1
    rw [← hindex, physicalSampledCutMass_internal q before band tail hend
      (j.val-before.length) (by omega)]
    exact (partitionPoint_mem band hband _).1
  have h := physicalRootedRadiusWindowSusceptibility_le_square n _ ha (q 0) _ r hr hc ha0 hcut
  rw [physicalWindowCellSum_internal_massCellSum q before band tail hend
    (fun k => ∫ p, physicalCutSourceSquareTrace n
      ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail) id k p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) (q 0)
        ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail))] at h
  exact h

theorem physicalRootedRadiusWindowSusceptibility_internal_le_cap (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1))
    (q : ℝ → FeatureIndex (n+1) → ℝ≥0) (before band : List PositiveMass)
    (tail : List (GaussianStep (FeatureIndex (n+1)))) {a g M mesh : ℝ}
    (ha0 : 0 < a) (hend : partitionEnd 0 before=a) (hband : MassOrdered a band)
    (ha : OrderedSteps 0 ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail))
    (hg : 0 < g) (hmesh0 : 0 ≤ mesh)
    (hmesh : ∀ (w:ℝ≥0), w ∈ sampleMassDurations a band → (w:ℝ) ≤ mesh)
    (hfield : ∀ st ∈ sampleClockSteps q 0 before ++ sampleClockSteps q a band,
      ∀ j, st.2 (Sum.inl j)=st.2 (Sum.inl 0))
    (hslope : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      g*(w:ℝ) ≤ st.2 (Sum.inl 0)) (sampleMassDurations a band) (sampleClockSteps q a band))
    (hmean : physicalPathSecondMoment (n+1)
      ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
      (q 0) (sampleClockSteps q 0 before ++ sampleClockSteps q a band).length ≤ M)
    (r : Fin (((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail).length+2) → ℝ)
    (hr : Monotone r)
    (hc : ∀ j, physicalWindowCellMass
      ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail) 0
      (physicalIntervalCells ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
        before.length (before.length+band.length)) j ≠ 0 → r j.castSucc < r j.succ) :
    let steps := ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
    let J := physicalIntervalCells steps before.length (before.length+band.length)
    (∫ p, physicalSusceptibilityMassIntegral (n+1) steps id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut r) p
      ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps) ≤
    (2*M/(((n+1 : ℕ):ℝ)*g)+2*mesh*M)/a := by
  dsimp only
  apply (physicalRootedRadiusWindowSusceptibility_internal_le_massCellSum
    (n+1) q before band tail ha0 hend hband ha r hr hc).trans
  apply div_le_div_of_nonneg_right _ ha0.le
  rw [← physicalBoundaryCap_massCellSum (n+1) q before band hband tail ha]
  have hzero : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1))) =>
      g*(w:ℝ) ≤ st.2 (Sum.inl 0))
      (List.replicate (sampleClockSteps q 0 before).length 0) (sampleClockSteps q 0 before) := by
    generalize sampleClockSteps q 0 before = common
    induction common with
    | nil => exact List.Forall₂.nil
    | cons st common ih =>
      simp only [List.length_cons, List.replicate_succ]
      exact List.Forall₂.cons (by simp) ih
  have hweights : ∀ (w:ℝ≥0),
      w ∈ List.replicate (sampleClockSteps q 0 before).length 0 ++ sampleMassDurations a band →
      (w:ℝ) ≤ mesh := by
    intro w hw
    rcases List.mem_append.mp hw with hw|hw
    · obtain ⟨_,rfl⟩ := List.mem_replicate.mp hw
      exact hmesh0
    · exact hmesh w hw
  simpa only [Nat.cast_add, Nat.cast_one] using
    physicalFiniteCapBoundaryTrace_rooted_le_pathSecondMoment n d e (q 0)
      _ _ tail ha hmesh0 hweights hg hfield (List.rel_append hzero hslope) hmean

theorem physicalWindowMass_internal_eq {ι : Type}
    (q : ℝ → ι → ℝ≥0) (before band : List PositiveMass)
    (tail : List (GaussianStep ι)) {a : ℝ} (hend : partitionEnd 0 before=a) :
    let steps := ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
    physicalWindowMass steps 0
      (physicalIntervalCells steps before.length (before.length+band.length)) =
      partitionEnd a band-a := by
  dsimp only
  rw [physicalIntervalMass _ _ (by omega)
    (by simp only [List.length_append, sampleClockSteps_length]; omega),
    physicalSampledCutMass_internal q before band tail hend band.length le_rfl,
    physicalPartitionPoint_length]
  have h := physicalSampledCutMass_internal q before band tail hend 0 (Nat.zero_le _)
  simpa only [Nat.add_zero, partitionPoint, partitionValues_zero, id_eq] using congrArg
    (fun z : ℝ => partitionEnd a band-z) h

theorem physicalWindowMass_internal_pos {ι : Type}
    (q : ℝ → ι → ℝ≥0) (before band : List PositiveMass)
    (tail : List (GaussianStep ι)) {a : ℝ}
    (hend : partitionEnd 0 before=a) (hwidth : a < partitionEnd a band) :
    let steps := ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
    0 < physicalWindowMass steps 0
      (physicalIntervalCells steps before.length (before.length+band.length)) := by
  dsimp only
  rw [physicalWindowMass_internal_eq q before band tail hend]
  exact sub_pos.mpr hwidth

theorem physicalIntervalWindow_secondMoment_le_end (n : ℕ)
    (q : ℝ → FeatureIndex n → ℝ≥0) (before band : List PositiveMass)
    (tail : List (GaussianStep (FeatureIndex n))) {a M : ℝ}
    (ha : OrderedSteps 0 ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail))
    (hmean : physicalPathSecondMoment n
      ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
      (q 0) (sampleClockSteps q 0 before ++ sampleClockSteps q a band).length ≤ M) :
    let steps := ((sampleClockSteps q 0 before ++ sampleClockSteps q a band)++tail)
    ∀ j ∈ physicalIntervalCells steps before.length (before.length+band.length),
      (∫ p, ‖actualSpinPath n steps id j.val p‖^2
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) (q 0) steps) ≤ M := by
  dsimp only
  intro j hj
  have hj' := (mem_physicalIntervalCells _ _ _ j).mp hj
  apply (physicalPathSecondMoment_mono n _ ha (q 0) _ _).trans hmean
  · simp only [List.length_append, sampleClockSteps_length]
    omega
  · simp only [List.length_append]
    omega

theorem physicalPathSecondMoment_nonneg (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q₀ : FeatureIndex n → ℝ≥0) (j : ℕ) :
    0 ≤ physicalPathSecondMoment n steps q₀ j := by
  exact integral_nonneg fun p => sq_nonneg ‖actualSpinPath n steps id j p‖

def physicalCutIndexRadius {ι : Type} (steps : List (GaussianStep ι)) :
    Fin (steps.length+2) → ℝ := fun j => (j.val : ℝ)

theorem physicalCutIndexRadius_monotone {ι : Type} (steps : List (GaussianStep ι)) :
    Monotone (physicalCutIndexRadius steps) := by
  intro i j hij
  exact Nat.cast_le.mpr hij

theorem physicalCutIndexRadius_cell_strict {ι : Type} (steps : List (GaussianStep ι))
    (j : Fin (steps.length+1)) :
    physicalCutIndexRadius steps j.castSucc < physicalCutIndexRadius steps j.succ := by
  change (j.val : ℝ) < ((j.val+1 : ℕ):ℝ)
  exact_mod_cast Nat.lt_succ_self j.val

theorem physicalRadiusWindowSusceptibility_grid_independent (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q₀ : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (r t : Fin (steps.length+2) → ℝ) (hr : Monotone r) (ht : Monotone t)
    (hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ)
    (hd : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → t j.castSucc < t j.succ) :
    (∫ p, physicalSusceptibilityMassIntegral n steps id
      (radiusCellMeasure (fun j => r j.castSucc) (fun j => r j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut r) p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) =
    (∫ p, physicalSusceptibilityMassIntegral n steps id
      (radiusCellMeasure (fun j => t j.castSucc) (fun j => t j.succ)
        (physicalWindowCellMass steps 0 J)) (radiusGridCut t) p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q₀ steps) := by
  rw [physicalRootedRadiusWindowSusceptibility_eq_trace n steps ha q₀ J r hr hc,
    physicalRootedRadiusWindowSusceptibility_eq_trace n steps ha q₀ J t ht hd]

end OAI.SKFluctuations.LaplaceWindowFormalization
