module

public import WholePathPhysicalTrace
public import PhysicalWindowTraceAggregation
public import PhysicalCutCovarianceTrace
public import MassCellCauchySchwarz
public import RetainedWindowGeometry
public import CanonicalCoarseMassGrid
public import MacroEnvelopeIntegration
public import MacroScalarCompetitors

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : DecidableEq (FeatureIndex (n+1)) := fun _ _ => Classical.propDecidable _

theorem completed_internal_window_centered_second_le (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ≥0)
    {a g mesh : ℝ} (ha0 : 0 < a) (hg : 0 < g) (hmesh0 : 0 ≤ mesh)
    (before band : List PositiveMass) (tail : List (GaussianStep (FeatureIndex (n+1))))
    (hend : partitionEnd 0 before=a) (hband : MassOrdered a band)
    (hwidth : a < partitionEnd a band)
    (hmesh : ∀ w ∈ sampleMassDurations a band, (w:ℝ) ≤ mesh)
    (hgap : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      g*(v-u) ≤ (h v:ℝ)-(h u:ℝ))
    (ha : OrderedSteps 0
      ((sampleClockSteps (completedPathClock (n+1) b h) 0 before ++
        sampleClockSteps (completedPathClock (n+1) b h) a band)++tail)) :
    let q := completedPathClock (n+1) b h
    let steps := ((sampleClockSteps q 0 before++sampleClockSteps q a band)++tail)
    let J := physicalIntervalCells steps before.length (before.length+band.length)
    let mu := rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps
    let A := fun p => (physicalPinnedPair (uniformWeight (n+1)) (finiteFeature (n+1))
      (spinSource (n+1)) steps 0 (physicalWindowWeight steps 0 J) p.1 p.2).1
    (momentNorm mu (fun p => A p-∫ z, A z ∂mu) 2)^2 ≤
      (7/3:ℝ)*(partitionEnd a band-a)⁻¹^2*(2/((n+1:ℝ)*g)+2*mesh)/a := by
  dsimp only
  let q := completedPathClock (n+1) b h
  let common := sampleClockSteps q 0 before
  let mid := sampleClockSteps q a band
  let steps := ((common++mid)++tail)
  let J := physicalIntervalCells steps before.length (before.length+band.length)
  let r := physicalCutIndexRadius steps
  have hr : Monotone r := physicalCutIndexRadius_monotone steps
  have hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ :=
    fun j _ => physicalCutIndexRadius_cell_strict steps j
  have hfield : ∀ st ∈ common++mid, ∀ j, st.2 (Sum.inl j)=st.2 (Sum.inl 0) := by
    dsimp only [common,mid]
    rw [← hend, ← sampleClockSteps_append]
    exact sampledFieldClock_aligned (n+1) (by omega) b h (before++band) 0
  have hslope := completedSampledField_gap (by omega : 0 < n+1) b h band hband hgap
  have hmean : physicalPathSecondMoment (n+1) steps (q 0) (common++mid).length ≤ 1 :=
    physicalPathSecondMoment_le_one (n+1) steps ha (q 0)
      (by simp only [steps,List.length_append]; omega)
  have henergy := physicalRootedRadiusWindowSusceptibility_internal_le_cap n d e q
    before band tail ha0 hend hband ha hg hmesh0 hmesh hfield hslope hmean r hr hc
  have hm := physical_window_centered_moment_energy (n+1) 1 (by omega) steps ha (q 0) J r hr hc
  dsimp only at henergy hm
  norm_num only [Nat.cast_one,inv_one,Real.rpow_one,Nat.cast_ofNat,pow_one] at hm
  have hbound := hm.trans (mul_le_mul_of_nonneg_left henergy
    (show 0 ≤ (7/3:ℝ)*(physicalWindowMass steps 0 J)⁻¹^2 by positivity))
  have hmass : physicalWindowMass steps 0 J = partitionEnd a band-a :=
    physicalWindowMass_internal_eq q before band tail hend
  rw [hmass] at hbound
  simpa only [common,mid,steps,J,q,mul_div_assoc,mul_one,Nat.cast_add,Nat.cast_one] using hbound

theorem macro_internal_window_centered_second_le {η Q t bstar a mesh : ℝ}
    (hη : 0 < η) (hQ : 1 < Q) (ht : 0 < t) (hbstar : 0 < bstar)
    (α : MacroInverseClass η Q) (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u)
    (ha0 : 0 < a) (hmesh0 : 0 ≤ mesh)
    (before band : List PositiveMass) (tail : List (GaussianStep (FeatureIndex (n+1))))
    (hend : partitionEnd 0 before=a) (hband : MassOrdered a band)
    (hwidth : a < partitionEnd a band)
    (hmesh : ∀ w ∈ sampleMassDurations a band, (w:ℝ) ≤ mesh)
    (ha : OrderedSteps 0
      ((sampleClockSteps (completedPathClock (n+1) (fun u => (b u).toNNReal)
        (fun u => (h u+t*b u*macroInverseQuantile hη hQ α u).toNNReal)) 0 before ++
        sampleClockSteps (completedPathClock (n+1) (fun u => (b u).toNNReal)
        (fun u => (h u+t*b u*macroInverseQuantile hη hQ α u).toNNReal)) a band)++tail)) :
    let q := completedPathClock (n+1) (fun u => (b u).toNNReal)
      (fun u => (h u+t*b u*macroInverseQuantile hη hQ α u).toNNReal)
    let steps := ((sampleClockSteps q 0 before++sampleClockSteps q a band)++tail)
    let J := physicalIntervalCells steps before.length (before.length+band.length)
    let mu := rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps
    let A := fun p => (physicalPinnedPair (uniformWeight (n+1)) (finiteFeature (n+1))
      (spinSource (n+1)) steps 0 (physicalWindowWeight steps 0 J) p.1 p.2).1
    (momentNorm mu (fun p => A p-∫ z, A z ∂mu) 2)^2 ≤
      (7/3:ℝ)*(partitionEnd a band-a)⁻¹^2*(2/((n+1:ℝ)*(t*bstar/Q))+2*mesh)/a := by
  have hnon (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) :
      0 ≤ h u+t*b u*macroInverseQuantile hη hQ α u :=
    add_nonneg (hhn u hu) (mul_nonneg (mul_nonneg ht.le (hbstar.le.trans (hbb u hu)))
      (macroInverseQuantile_bounds hη hQ α u).1)
  apply completed_internal_window_centered_second_le n d e _ _ ha0
    (div_pos (mul_pos ht hbstar) (zero_lt_one.trans hQ)) hmesh0 before band tail
    hend hband hwidth hmesh _ ha
  intro u hu v hv huv
  rw [Real.coe_toNNReal _ (hnon v hv),Real.coe_toNNReal _ (hnon u hu)]
  exact macro_inverse_field_gap hη hQ α b h ht.le hbstar.le hb hh hbb hu hv huv

def badProfileBlocks (S : ℕ → ℝ) (N : ℕ) (osc : ℝ) : Finset ℕ :=
  (Finset.range N).filter (fun i => osc < S (i+2)-S i)

theorem badProfileBlocks_card_bound (S : ℕ → ℝ) (hS : Monotone S)
    (N : ℕ) (osc : ℝ) :
    osc*((badProfileBlocks S N osc).card:ℝ) ≤ 2*(S (N+1)-S 0) := by
  have ht (M : ℕ) : ∑ i ∈ Finset.range M, (S (i+2)-S i) =
      S (M+1)+S M-S 1-S 0 := by
    induction M with
    | zero => simp
    | succ M ih => rw [Finset.sum_range_succ,ih]; ring
  have hbad : ∑ i ∈ badProfileBlocks S N osc, osc ≤
      ∑ i ∈ badProfileBlocks S N osc, (S (i+2)-S i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact (Finset.mem_filter.mp hi).2.le
  have hsub : ∑ i ∈ badProfileBlocks S N osc, (S (i+2)-S i) ≤
      ∑ i ∈ Finset.range N, (S (i+2)-S i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro i hi hni
    exact sub_nonneg.mpr (hS (by omega))
  simp only [Finset.sum_const,nsmul_eq_mul] at hbad
  rw [ht] at hsub
  have hs0 := hS (show 0 ≤ 1 from by omega)
  have hsN := hS (show N ≤ N+1 from by omega)
  nlinarith

theorem badProfileBlocks_mass_bound (S : ℕ → ℝ) (hS : Monotone S)
    (N : ℕ) {osc width : ℝ} (hosc : 0 < osc) (hwidth : 0 ≤ width)
    (weight : ℕ → ℝ) (hw : ∀ i ∈ badProfileBlocks S N osc, weight i ≤ width) :
    ∑ i ∈ badProfileBlocks S N osc, weight i ≤
      2*width*(S (N+1)-S 0)/osc := by
  have hs := Finset.sum_le_sum hw
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hb := mul_le_mul_of_nonneg_left (badProfileBlocks_card_bound S hS N osc) hwidth
  apply (le_div_iff₀ hosc).mpr
  have hs' := mul_le_mul_of_nonneg_right hs hosc.le
  nlinarith

theorem weighted_profile_mean_close {I : Type*} [Fintype I]
    (alpha profile : I → ℝ) (h0 : ∀ j, 0 ≤ alpha j) (hnorm : ∑ j, alpha j=1)
    {S osc : ℝ} (hclose : ∀ j, alpha j ≠ 0 → |profile j-S| ≤ osc) :
    |(∑ j, alpha j*profile j)-S| ≤ osc := by
  have he : (∑ j, alpha j*profile j)-S = ∑ j, alpha j*(profile j-S) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hnorm,one_mul]
  rw [he]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    ∑ j, |alpha j*(profile j-S)| ≤ ∑ j, alpha j*osc := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases ha : alpha j=0
      · simp only [ha,zero_mul,abs_zero]; exact le_rfl
      · rw [abs_mul,abs_of_nonneg (h0 j)]
        exact mul_le_mul_of_nonneg_left (hclose j ha) (h0 j)
    _ = osc := by rw [← Finset.sum_mul,hnorm,one_mul]

def physicalSampledS (n : ℕ) (b h : ℝ → ℝ≥0) (as : List PositiveMass)
    (ha : MassOrdered 0 as) : ℝ → ℝ :=
  stepPairMoment (uniformWeight (n + 1)) (finiteFeature (n + 1))
    (completedPathClock (n + 1) b h 0)
    (sampleClockSteps (completedPathClock (n + 1) b h) 0 as)
    (sampleClockSteps_ordered _ as ha).mem_pos
    (orderedOverlap (n + 1))

theorem physicalSampledS_intervalIntegrable (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (a c : ℝ) :
    IntervalIntegrable (physicalSampledS n b h as ha) volume a c :=
  stepPairMoment_intervalIntegrable _ _ _ _ _ _ a c

theorem physicalOrderedPathS_intervalIntegrable (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (orderedPathS (n + 1) b h) volume 0 1 :=
  pathPairMoment_intervalIntegrable_all (uniformWeight_pos (n + 1)) (orderedFeature (n + 1))
    (orderedPathClock (n + 1) b h) (orderedPathClock_monotone (n + 1) hb hh) _

theorem physicalSampledS_l1_bound (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1)) (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as = 1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) :
    (∫ u in 0..1, |physicalSampledS n b h as ha u - orderedPathS (n + 1) b h u|) ≤
      mesh * physicalBApproximationConstant n b h := by
  have hD : ∀ i, 0 ≤ physicalFeatureCoordinateBound n i := by
    intro i
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hφ : ∀ σ i, |finiteFeature (n + 1) σ (Pi.single i 1)| ≤ physicalFeatureCoordinateBound n i := by
    intro σ i
    unfold physicalFeatureCoordinateBound
    exact Finset.single_le_sum (fun τ _ => abs_nonneg (finiteFeature (n + 1) τ (Pi.single i 1))) (Finset.mem_univ σ)
  have hP : ∀ σ τ, |orderedOverlap (n + 1) σ τ| ≤ (1 : ℝ) :=
    orderedOverlap_abs_le_one (n + 1)
  have hbound := sampledPairMoment_l1_bound (uniformWeight_pos (n + 1)) (finiteFeature (n + 1))
    (physicalFeatureCoordinateBound n) hD hφ (completedPathClock (n + 1) b h)
    (completedPathClock_monotone (n + 1) hb hh) as ha he hm
    (orderedOverlap (n + 1)) (by norm_num : (0 : ℝ) ≤ 1) hP
  have heq : (∫ u in 0..1, |physicalSampledS n b h as ha u - orderedPathS (n + 1) b h u|) =
      ∫ u in 0..1, |physicalSampledS n b h as ha u -
        pathPairMoment (uniformWeight (n + 1)) (finiteFeature (n + 1))
          (completedPathClock (n + 1) b h) (orderedOverlap (n + 1)) u| := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with u hu
    rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
    rw [show orderedPathS (n + 1) b h u = _ from
      orderedPathPair_eq_completed (n + 1) (by omega) b h hb hh _ hu]
  rw [heq]
  calc
    _ ≤ ClockTree.errorJetVariation 2 0 0 * 1 *
        (4 * mesh * clockVariationBound (physicalFeatureCoordinateBound n) (completedPathClock (n + 1) b h)) := hbound
    _ = mesh * physicalBApproximationConstant n b h := by
      unfold physicalBApproximationConstant
      ring

theorem physicalSampledS_mem_Icc (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : ℝ) :
    physicalSampledS n b h as ha u ∈ Icc (0:ℝ) 1 := by
  let q := completedPathClock (n+1) b h
  let steps := sampleClockSteps q 0 as
  have ho : OrderedSteps 0 steps := sampleClockSteps_ordered q as ha
  have hj : (splitClockSteps u steps).1.length ≤ steps.length := by
    have hh := congrArg List.length (splitClockSteps_append u steps)
    rw [List.length_append] at hh
    omega
  have he := physicalSecondMoment_eq_stepPairMoment (n+1) (by omega) steps ho (q 0) u
  change physicalPathSecondMoment (n+1) steps (q 0) (splitClockSteps u steps).1.length =
    physicalSampledS n b h as ha u at he
  rw [← he]
  exact ⟨physicalPathSecondMoment_nonneg (n+1) steps (q 0) _,
    physicalPathSecondMoment_le_one (n+1) steps ho (q 0) hj⟩

theorem sq_difference_le_two_abs {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1)
    (hb : b ∈ Icc (0:ℝ) 1) : |a^2-b^2| ≤ 2*|a-b| := by
  rw [show a^2-b^2=(a-b)*(a+b) by ring,abs_mul,
    abs_of_nonneg (add_nonneg ha.1 hb.1)]
  have h := mul_le_mul_of_nonneg_left (show a+b ≤ 2 by linarith [ha.2,hb.2]) (abs_nonneg (a-b))
  linarith

theorem intervalIntegrable_square_of_unit_bound {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume 0 1)
    (hbound : ∀ u ∈ Ioc (0:ℝ) 1, f u ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (fun u => (f u)^2) volume 0 1 := by
  apply IntervalIntegrable.mono_fun' (intervalIntegrable_const (c := (1:ℝ)))
    (hf.aestronglyMeasurable_restrict_uIoc.pow 2)
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hu
  change ‖(f u)^2‖ ≤ 1
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := hbound u hu
  nlinarith [h.1,h.2]

def physicalSampledThermal (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (u : ℝ) : ℝ :=
  physicalSampledB n b h as ha u-(physicalSampledS n b h as ha u)^2

theorem physicalSampledThermal_intervalIntegrable (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    IntervalIntegrable (physicalSampledThermal n b h as ha) volume 0 1 :=
  (physicalSampledB_intervalIntegrable n b h as ha 0 1).sub
    (intervalIntegrable_square_of_unit_bound (physicalSampledS_intervalIntegrable n b h as ha 0 1)
      (fun u _ => physicalSampledS_mem_Icc n b h as ha u))

theorem physicalOrderedThermal_intervalIntegrable (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) :
    IntervalIntegrable (fun u => orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)
      volume 0 1 :=
  (physicalOrderedPathB_intervalIntegrable n b h hb hh).sub
    (intervalIntegrable_square_of_unit_bound (physicalOrderedPathS_intervalIntegrable n b h hb hh)
      (fun u hu => ⟨(orderedPath_SK_bounds (n+1) (by omega) b h hb hh hu).1,
        (orderedPath_SK_bounds (n+1) (by omega) b h hb hh hu).2.1⟩))

theorem physicalSampledThermal_l1_bound (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hm : PartitionMesh mesh 0 as) :
    (∫ u in 0..1, |physicalSampledThermal n b h as ha u-
      (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)|) ≤
        3*mesh*physicalBApproximationConstant n b h := by
  have hf := physicalSampledThermal_intervalIntegrable n b h as ha
  have hg := physicalOrderedThermal_intervalIntegrable n b h hb hh
  have hB := ((physicalSampledB_intervalIntegrable n b h as ha 0 1).sub
    (physicalOrderedPathB_intervalIntegrable n b h hb hh)).abs
  have hS := ((physicalSampledS_intervalIntegrable n b h as ha 0 1).sub
    (physicalOrderedPathS_intervalIntegrable n b h hb hh)).abs
  have hp : ∀ u ∈ Ioo (0:ℝ) 1,
      |physicalSampledThermal n b h as ha u-
        (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)| ≤
      |physicalSampledB n b h as ha u-orderedPathB (n+1) b h u|+
        2*|physicalSampledS n b h as ha u-orderedPathS (n+1) b h u| := by
    intro u hu
    have hpath := orderedPath_SK_bounds (n+1) (by omega) b h hb hh ⟨hu.1,hu.2.le⟩
    have hsquare := sq_difference_le_two_abs (physicalSampledS_mem_Icc n b h as ha u)
      ⟨hpath.1,hpath.2.1⟩
    have heq : physicalSampledThermal n b h as ha u-
        (orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2) =
      (physicalSampledB n b h as ha u-orderedPathB (n+1) b h u)-
        ((physicalSampledS n b h as ha u)^2-(orderedPathS (n+1) b h u)^2) := by
      unfold physicalSampledThermal
      ring
    rw [heq]
    exact (abs_sub _ _).trans (add_le_add le_rfl hsquare)
  have hInt := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1)
    ((hf.sub hg).abs) (hB.add (hS.const_mul 2)) hp
  rw [intervalIntegral.integral_add hB (hS.const_mul 2),intervalIntegral.integral_const_mul] at hInt
  have hBb := physicalSampledB_l1_bound n b h hb hh as ha he hm
  have hSb := physicalSampledS_l1_bound n b h hb hh as ha he hm
  linarith

theorem physicalSampledThermal_integral_tendsto (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀ j, MassOrdered 0 (as j)) (he : ∀ j, partitionEnd 0 (as j)=1)
    (hm : ∀ j, PartitionMesh (mesh j) 0 (as j)) (hmesh : Tendsto mesh atTop (𝓝 0)) :
    Tendsto (fun j => ∫ u in 0..1, physicalSampledThermal n b h (as j) (ho j) u)
      atTop (𝓝 (∫ u in 0..1, orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  have hbound (j : ℕ) :
      |(∫ u in 0..1, physicalSampledThermal n b h (as j) (ho j) u)-
        (∫ u in 0..1, orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2)| ≤
          3*mesh j*physicalBApproximationConstant n b h := by
    rw [← intervalIntegral.integral_sub (physicalSampledThermal_intervalIntegrable n b h (as j) (ho j))
      (physicalOrderedThermal_intervalIntegrable n b h hb hh)]
    exact (intervalIntegral.abs_integral_le_integral_abs (by norm_num : (0:ℝ)≤1)).trans
      (physicalSampledThermal_l1_bound n b h hb hh (as j) (ho j) (he j) (hm j))
  exact squeeze_zero (fun _ => abs_nonneg _) hbound
    (by simpa only [mul_assoc,zero_mul,mul_left_comm (3:ℝ)] using
      hmesh.mul_const (3*physicalBApproximationConstant n b h))

theorem physicalWindowCellSum_subset {ι : Type} (steps : List (GaussianStep ι))
    {a : ℝ} (ha : OrderedSteps a steps) {J K : Finset (Fin (steps.length+1))}
    (hJK : J ⊆ K) (F : ℕ → ℝ) (hF : ∀ j, 0 ≤ F j) :
    (∑ j, physicalWindowCellMass steps a J j*F j.val) ≤
      (∑ j, physicalWindowCellMass steps a K j*F j.val) := by
  apply Finset.sum_le_sum
  intro j hj
  by_cases hJ : j ∈ J
  · have hK := hJK hJ
    simp only [physicalWindowCellMass,hJ,hK,ite_true]
    exact le_rfl
  · simp only [physicalWindowCellMass,hJ,ite_false,zero_mul]
    exact mul_nonneg (physicalWindowCellMass_nonneg steps ha K j) (hF j.val)

theorem physicalSampledWindowSquareTrace_le_whole (n : ℕ)
    (q : ℝ → FeatureIndex n → ℝ≥0) (as : List PositiveMass) (ha : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (hJ : J ⊆ physicalIntervalCells (sampleClockSteps q 0 as) 0 as.length) :
    let steps := sampleClockSteps q 0 as
    let F := fun j => ∫ p, physicalCutSourceSquareTrace n steps id j p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) (q 0) steps
    (∑ j, physicalWindowCellMass steps 0 J j*F j.val) ≤ massCellSum as 0 F := by
  dsimp only
  let steps := sampleClockSteps q 0 as
  let F := fun j => ∫ p, physicalCutSourceSquareTrace n steps id j p
    ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) (q 0) steps
  have ho := sampleClockSteps_ordered q as ha
  have hF (j : ℕ) : 0 ≤ F j := integral_nonneg fun p =>
    (physicalCutSourceSquareTrace_mem_Icc n steps ho id j p).1
  have hh := physicalWindowCellSum_subset steps ho hJ F hF
  have he := physicalWindowCellSum_internal_massCellSum q [] as [] (a := (0:ℝ)) rfl F
  dsimp only at he
  simp only [List.length_nil,Nat.zero_add] at he
  let G := fun ss : List (GaussianStep (FeatureIndex n)) =>
    ∑ j, physicalWindowCellMass ss 0 (physicalIntervalCells ss 0 as.length) j*F j.val
  change G ((sampleClockSteps q 0 []++sampleClockSteps q 0 as)++[]) = massCellSum as 0 F at he
  simp only [sampleClockSteps,List.nil_append,List.append_nil] at he
  exact hh.trans_eq he

theorem completed_sampled_window_centered_second_le (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ≥0)
    {a g mesh : ℝ} (ha0 : 0 < a) (hg : 0 < g) (hmesh0 : 0 ≤ mesh)
    (as : List PositiveMass) (ha : MassOrdered 0 as)
    (hmesh : ∀ w ∈ sampleMassDurations 0 as, (w:ℝ) ≤ mesh)
    (hgap : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      g*(v-u) ≤ (h v:ℝ)-(h u:ℝ))
    (J : Finset (Fin ((sampleClockSteps (completedPathClock (n+1) b h) 0 as).length+1)))
    (hJ : J ⊆ physicalIntervalCells (sampleClockSteps (completedPathClock (n+1) b h) 0 as) 0 as.length)
    (hcut : ∀ j ∈ J, a ≤ physicalCutMass 0
      (sampleClockSteps (completedPathClock (n+1) b h) 0 as) j.val) :
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    let mu := rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps
    let A := fun p => (physicalPinnedPair (uniformWeight (n+1)) (finiteFeature (n+1))
      (spinSource (n+1)) steps 0 (physicalWindowWeight steps 0 J) p.1 p.2).1
    (momentNorm mu (fun p => A p-∫ z, A z ∂mu) 2)^2 ≤
      (7/3:ℝ)*(physicalWindowMass steps 0 J)⁻¹^2*(2/((n+1:ℝ)*g)+2*mesh)/a := by
  dsimp only
  let q := completedPathClock (n+1) b h
  let steps := sampleClockSteps q 0 as
  let r := physicalCutIndexRadius steps
  have ho := sampleClockSteps_ordered q as ha
  have hr : Monotone r := physicalCutIndexRadius_monotone steps
  have hc : ∀ j, physicalWindowCellMass steps 0 J j ≠ 0 → r j.castSucc < r j.succ :=
    fun j _ => physicalCutIndexRadius_cell_strict steps j
  have henergy := physicalRootedRadiusWindowSusceptibility_le_square (n+1) steps ho
    (q 0) J r hr hc ha0 hcut
  have hsum := physicalSampledWindowSquareTrace_le_whole (n+1) q as ha J hJ
  have hwhole := completedSampledWholePath_trace_le n d e b h hg hmesh0 as ha hmesh hgap
  dsimp only at henergy hsum hwhole
  have he := henergy.trans
    (div_le_div_of_nonneg_right (hsum.trans hwhole) ha0.le)
  have hm := physical_window_centered_moment_energy (n+1) 1 (by omega) steps ho (q 0) J r hr hc
  dsimp only at hm
  norm_num only [Nat.cast_one,inv_one,Real.rpow_one,Nat.cast_ofNat,pow_one] at hm
  have hb := hm.trans (mul_le_mul_of_nonneg_left he
    (show 0 ≤ (7/3:ℝ)*(physicalWindowMass steps 0 J)⁻¹^2 by positivity))
  simpa only [steps,q,mul_div_assoc] using hb

theorem hierarchyPairMean_centered_square {S I : Type*} [Fintype S] [Nonempty S]
    [Fintype I] {w : S → ℝ} (hw : ∀ s, 0 < w s)
    (phi : S → (I → ℝ) →L[ℝ] ℝ) (K : S → S → ℝ)
    (steps : List (GaussianStep I)) {a : ℝ} (ha : OrderedSteps a steps) (c : ℝ) (x : I → ℝ) :
    hierarchyPairMean w phi (fun s t => (K s t-c)^2) steps x =
      hierarchyPairMean w phi (fun s t => (K s t)^2) steps x-
        2*c*hierarchyPairMean w phi K steps x+c^2 := by
  let p := fun s => hierarchyAtom w phi steps s x
  have hp : ∑ s, p s=1 := hierarchyAtom_sum hw phi steps ha x
  have h (s t) : p s*p t*(K s t-c)^2 =
      p s*p t*(K s t)^2-2*c*(p s*p t*K s t)+c^2*(p s*p t) := by ring
  have hm : (∑ s, ∑ t, 2*c*(p s*p t*K s t)) =2*c*(∑ s, ∑ t, p s*p t*K s t) := by
    simp only [← Finset.mul_sum]
  have hc : (∑ s, ∑ t, c^2*(p s*p t))=c^2 := by
    simp only [← Finset.mul_sum,hp,mul_one]
  change (∑ s, ∑ t, p s*p t*(K s t-c)^2) =
    (∑ s, ∑ t, p s*p t*(K s t)^2)-2*c*(∑ s, ∑ t, p s*p t*K s t)+c^2
  simp_rw [h,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  rw [hm,hc]

theorem physicalCutPairDefectSecond_eq_thermal (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q0 : FeatureIndex n → ℝ≥0) :
    physicalCutPairDefectSecond n pre tail q0
      (physicalPathSecondMoment n (pre++tail) q0 pre.length) =
      rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
        (fun sigma tau => (orderedOverlap n sigma tau)^2) (pre++tail) pre.length-
      (physicalPathSecondMoment n (pre++tail) q0 pre.length)^2 := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
  let X := actualSpinPath n (pre++tail) id
  let c := physicalPathSecondMoment n (pre++tail) q0 pre.length
  let B := fun p : PhysicalPathState (FeatureIndex n → ℝ) n (pre++tail) =>
    hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun sigma tau => (orderedOverlap n sigma tau)^2) tail (actualCutField pre tail p.1 p.2)
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 (pre++tail) ha
  have hBI := (hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun sigma tau => (orderedOverlap n sigma tau)^2) tail (ha.suffix pre tail) 0).integrable_comp_measurable
      (actualCutField_measurable_joint pre tail) (μ := mu)
  have hQI := (physical_sqnorm_memLp n (pre++tail) ha id measurable_id mu pre.length 1).integrable le_rfl
  have he (p : PhysicalPathState (FeatureIndex n → ℝ) n (pre++tail)) :
      hierarchyPairMean (uniformWeight n) (finiteFeature n)
        (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail (actualCutField pre tail p.1 p.2) =
        B p-2*c*‖X pre.length p‖^2+c^2 := by
    rw [hierarchyPairMean_centered_square (uniformWeight_pos n) (finiteFeature n)
      (orderedOverlap n) tail (ha.suffix pre tail)]
    rw [← actualSpinPath_norm_sq_at_cut n pre tail ha]
  change (∫ p, hierarchyPairMean (uniformWeight n) (finiteFeature n)
    (fun sigma tau => (orderedOverlap n sigma tau-c)^2) tail
    (actualCutField pre tail p.1 p.2) ∂mu) = _
  simp_rw [he]
  have hs := integral_sub hBI (hQI.const_mul (2*c))
  have hadd := integral_add (hBI.sub (hQI.const_mul (2*c))) (integrable_const (c^2))
  simp only [Pi.add_apply,Pi.sub_apply] at hs hadd
  rw [hadd,hs,integral_const_mul,integral_const,probReal_univ,one_smul]
  change (∫ p, B p ∂mu)-2*c*c+c^2 = _
  have hroot := physicalRootLevelB_eq_actual_cutExpectation n pre tail ha q0
  change _ = ∫ p, B p ∂mu at hroot
  rw [← hroot]
  dsimp only [c]
  ring

theorem physical_root_thermal_le_norm_variance (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (i : ℕ) (hi : i ≤ steps.length) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let S := physicalPathSecondMoment n steps q0 i
    let C := ∫ p, physicalCutSpinTraceCovSq n steps id i p ∂mu
    rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
      (fun sigma tau => (orderedOverlap n sigma tau)^2) steps i-S^2 ≤
      (momentNorm mu (fun p => ‖actualSpinPath n steps id i p‖^2-S) 2)^2+
        2*Real.sqrt C+C := by
  dsimp only
  have ho : OrderedSteps 0 (steps.take i++steps.drop i) := by
    simpa only [List.take_append_drop] using ha
  have hD := physical_prefix_centered_overlap_integral n (steps.take i) (steps.drop i)
    ho q0 (physicalPathSecondMoment n (steps.take i++steps.drop i) q0 (steps.take i).length)
  dsimp only at hD
  change physicalCutPairDefectSecond n (steps.take i) (steps.drop i) q0
    (physicalPathSecondMoment n (steps.take i++steps.drop i) q0 (steps.take i).length) ≤ _ at hD
  rw [physicalCutPairDefectSecond_eq_thermal n (steps.take i) (steps.drop i) ho q0] at hD
  have hC : (fun p : PhysicalPathState (FeatureIndex n → ℝ) n (steps.take i++steps.drop i) =>
      physicalSpinTraceCovSq n (steps.drop i) (actualCutField (steps.take i) (steps.drop i) p.1 p.2)) =
      physicalCutSpinTraceCovSq n (steps.take i++steps.drop i) id (steps.take i).length := by
    funext p
    exact (physicalCutSpinTraceCovSq_eq_actualCut n (steps.take i) (steps.drop i) id p).symm
  rw [hC] at hD
  let R := fun (ss : List (GaussianStep (FeatureIndex n))) (k : ℕ) =>
    (momentNorm (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 ss)
      (fun p => ‖actualSpinPath n ss id k p‖^2-physicalPathSecondMoment n ss q0 k) 2)^2+
      2*Real.sqrt (∫ p, physicalCutSpinTraceCovSq n ss id k p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 ss)+
      (∫ p, physicalCutSpinTraceCovSq n ss id k p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 ss)
  change rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
    (fun sigma tau => (orderedOverlap n sigma tau)^2) (steps.take i++steps.drop i) (steps.take i).length-
    (physicalPathSecondMoment n (steps.take i++steps.drop i) q0 (steps.take i).length)^2 ≤
    R (steps.take i++steps.drop i) (steps.take i).length at hD
  simp only [List.take_append_drop,List.length_take,min_eq_left hi] at hD
  exact hD

theorem physical_root_thermal_le_two_buffers (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (i : ℕ) (hi : i ≤ steps.length)
    (Jm Jp : Finset (Fin (steps.length+1)))
    (hvm : 0 < physicalWindowMass steps 0 Jm) (hvp : 0 < physicalWindowMass steps 0 Jp)
    (him : ∀ j ∈ Jm, j.val ≤ i) (hip : ∀ j ∈ Jp, i ≤ j.val)
    {osc : ℝ} (hosc : 0 ≤ osc)
    (hclosem : ∀ j ∈ Jm, |physicalPathSecondMoment n steps q0 j.val-
      physicalPathSecondMoment n steps q0 i| ≤ osc)
    (hclosep : ∀ j ∈ Jp, |physicalPathSecondMoment n steps q0 j.val-
      physicalPathSecondMoment n steps q0 i| ≤ osc) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
    let S := physicalPathSecondMoment n steps q0 i
    let Am := fun p => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 (physicalWindowWeight steps 0 Jm) p.1 p.2).1
    let Ap := fun p => (physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0 (physicalWindowWeight steps 0 Jp) p.1 p.2).1
    let C := ∫ p, physicalCutSpinTraceCovSq n steps id i p ∂mu
    rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
      (fun sigma tau => (orderedOverlap n sigma tau)^2) steps i-S^2 ≤
      12*(momentNorm mu (fun p => Am p-∫ z, Am z ∂mu) 2)^2+
      12*(momentNorm mu (fun p => Ap p-∫ z, Ap z ∂mu) 2)^2+
      3*osc^2+2*Real.sqrt C+C := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let km := physicalWindowWeight steps 0 Jm
  let kp := physicalWindowWeight steps 0 Jp
  let S := physicalPathSecondMoment n steps q0 i
  have hm0 (j) : 0 ≤ pathMassDifferences steps 0 j*km j :=
    mul_nonneg (pathMassDifferences_nonneg steps ha j) (physicalWindowWeight_nonneg steps ha Jm j)
  have hp0 (j) : 0 ≤ pathMassDifferences steps 0 j*kp j :=
    mul_nonneg (pathMassDifferences_nonneg steps ha j) (physicalWindowWeight_nonneg steps ha Jp j)
  have hnm := physicalWindowWeight_normalized steps 0 Jm hvm
  have hnp := physicalWindowWeight_normalized steps 0 Jp hvp
  have him' : ∀ j, pathMassDifferences steps 0 j*km j ≠ 0 → j.val ≤ i := by
    intro j hj
    apply him j
    by_contra hnot
    simp only [km,physicalWindowWeight,if_neg hnot,mul_zero,ne_self_iff_false] at hj
  have hip' : ∀ j, pathMassDifferences steps 0 j*kp j ≠ 0 → i ≤ j.val := by
    intro j hj
    apply hip j
    by_contra hnot
    simp only [kp,physicalWindowWeight,if_neg hnot,mul_zero,ne_self_iff_false] at hj
  have hcm : |(∑ j, (pathMassDifferences steps 0 j*km j)*physicalPathSecondMoment n steps q0 j.val)-S| ≤ osc := by
    apply weighted_profile_mean_close _ _ hm0 hnm
    intro j hj
    apply hclosem j
    by_contra hnot
    simp only [km,physicalWindowWeight,if_neg hnot,mul_zero,ne_self_iff_false] at hj
  have hcp : |(∑ j, (pathMassDifferences steps 0 j*kp j)*physicalPathSecondMoment n steps q0 j.val)-S| ≤ osc := by
    apply weighted_profile_mean_close _ _ hp0 hnp
    intro j hj
    apply hclosep j
    by_contra hnot
    simp only [kp,physicalWindowWeight,if_neg hnot,mul_zero,ne_self_iff_false] at hj
  have hbuf := physical_buffered_norm_concentration n steps ha q0 km kp
    (physicalWindowWeight_nonneg steps ha Jm) (physicalWindowWeight_nonneg steps ha Jp)
    hnm hnp (hi.trans (Nat.le_succ _)) him' hip' (by norm_num : 1 ≤ (2:ℝ)) hosc hcm hcp
  dsimp only at hbuf
  have hsq := pow_le_pow_left₀ (momentNorm_nonneg (μ := mu) _ _) hbuf 2
  have hD := physical_root_thermal_le_norm_variance n steps ha q0 i hi
  dsimp only at hD
  have hsum (a b c : ℝ) : (2*a+2*b+c)^2 ≤ 12*a^2+12*b^2+3*c^2 := by
    nlinarith [sq_nonneg (2*a-2*b),sq_nonneg (2*a-c),sq_nonneg (2*b-c)]
  have hh := hsq.trans (hsum _ _ _)
  dsimp only [mu,km,kp,S] at hh
  linarith

theorem completed_sampled_buffered_thermal_le (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ≥0)
    {a g mesh osc : ℝ} (ha0 : 0 < a) (hg : 0 < g) (hmesh0 : 0 ≤ mesh) (hosc : 0 ≤ osc)
    (as : List PositiveMass) (ha : MassOrdered 0 as)
    (hmesh : ∀ w ∈ sampleMassDurations 0 as, (w:ℝ) ≤ mesh)
    (hgap : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      g*(v-u) ≤ (h v:ℝ)-(h u:ℝ))
    (i : ℕ) (hi : i ≤ as.length)
    (Jm Jp : Finset (Fin ((sampleClockSteps (completedPathClock (n+1) b h) 0 as).length+1)))
    (hJm : Jm ⊆ physicalIntervalCells (sampleClockSteps (completedPathClock (n+1) b h) 0 as) 0 as.length)
    (hJp : Jp ⊆ physicalIntervalCells (sampleClockSteps (completedPathClock (n+1) b h) 0 as) 0 as.length)
    (hcutm : ∀ j ∈ Jm, a ≤ physicalCutMass 0 (sampleClockSteps (completedPathClock (n+1) b h) 0 as) j.val)
    (hcutp : ∀ j ∈ Jp, a ≤ physicalCutMass 0 (sampleClockSteps (completedPathClock (n+1) b h) 0 as) j.val)
    (hvm : 0 < physicalWindowMass (sampleClockSteps (completedPathClock (n+1) b h) 0 as) 0 Jm)
    (hvp : 0 < physicalWindowMass (sampleClockSteps (completedPathClock (n+1) b h) 0 as) 0 Jp)
    (him : ∀ j ∈ Jm, j.val ≤ i) (hip : ∀ j ∈ Jp, i ≤ j.val)
    (hclosem : ∀ j ∈ Jm,
      |physicalPathSecondMoment (n+1) (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
        (completedPathClock (n+1) b h 0) j.val-
       physicalPathSecondMoment (n+1) (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
        (completedPathClock (n+1) b h 0) i| ≤ osc)
    (hclosep : ∀ j ∈ Jp,
      |physicalPathSecondMoment (n+1) (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
        (completedPathClock (n+1) b h 0) j.val-
       physicalPathSecondMoment (n+1) (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
        (completedPathClock (n+1) b h 0) i| ≤ osc) :
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    let mu := rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps
    let S := physicalPathSecondMoment (n+1) steps (q 0) i
    let C := ∫ p, physicalCutSpinTraceCovSq (n+1) steps id i p ∂mu
    rootLevelPairMean (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0)
      (fun sigma tau => (orderedOverlap (n+1) sigma tau)^2) steps i-S^2 ≤
      28*((physicalWindowMass steps 0 Jm)⁻¹^2+(physicalWindowMass steps 0 Jp)⁻¹^2)*
        (2/((n+1:ℝ)*g)+2*mesh)/a+3*osc^2+2*Real.sqrt C+C := by
  dsimp only
  have ho := sampleClockSteps_ordered (completedPathClock (n+1) b h) as ha
  have hm := completed_sampled_window_centered_second_le n d e b h ha0 hg hmesh0 as ha
    hmesh hgap Jm hJm hcutm
  have hp := completed_sampled_window_centered_second_le n d e b h ha0 hg hmesh0 as ha
    hmesh hgap Jp hJp hcutp
  have hD := physical_root_thermal_le_two_buffers (n+1) _ ho
    (completedPathClock (n+1) b h 0) i (by simpa only [sampleClockSteps_length] using hi)
    Jm Jp hvm hvp him hip hosc hclosem hclosep
  dsimp only at hm hp hD
  have hbound := add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ) ≤ 12))
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 12))
  have he : 12*((7/3:ℝ)*(physicalWindowMass
      (sampleClockSteps (completedPathClock (n+1) b h) 0 as) 0 Jm)⁻¹^2*
      (2/((n+1:ℝ)*g)+2*mesh)/a)+
      12*((7/3:ℝ)*(physicalWindowMass
      (sampleClockSteps (completedPathClock (n+1) b h) 0 as) 0 Jp)⁻¹^2*
      (2/((n+1:ℝ)*g)+2*mesh)/a) =
      28*((physicalWindowMass (sampleClockSteps (completedPathClock (n+1) b h) 0 as) 0 Jm)⁻¹^2+
        (physicalWindowMass (sampleClockSteps (completedPathClock (n+1) b h) 0 as) 0 Jp)⁻¹^2)*
      (2/((n+1:ℝ)*g)+2*mesh)/a := by ring
  rw [he] at hbound
  linarith

structure PhysicalCutBufferGeometry (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0)
    (a width osc : ℝ) (i : ℕ) where
  past : Finset (Fin (steps.length+1))
  future : Finset (Fin (steps.length+1))
  past_internal : past ⊆ physicalIntervalCells steps 0 steps.length
  future_internal : future ⊆ physicalIntervalCells steps 0 steps.length
  past_cut : ∀ j ∈ past, a ≤ physicalCutMass 0 steps j.val
  future_cut : ∀ j ∈ future, a ≤ physicalCutMass 0 steps j.val
  past_mass : width ≤ physicalWindowMass steps 0 past
  future_mass : width ≤ physicalWindowMass steps 0 future
  past_before : ∀ j ∈ past, j.val ≤ i
  future_after : ∀ j ∈ future, i ≤ j.val
  past_close : ∀ j ∈ past,
    |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i| ≤ osc
  future_close : ∀ j ∈ future,
    |physicalPathSecondMoment n steps q0 j.val-physicalPathSecondMoment n steps q0 i| ≤ osc

theorem inv_square_le_of_positive_lower {width mass : ℝ} (hw : 0 < width)
    (hwm : width ≤ mass) : mass⁻¹^2 ≤ width⁻¹^2 := by
  have hm := hw.trans_le hwm
  have hi : mass⁻¹ ≤ width⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hw hwm
  exact pow_le_pow_left₀ (inv_nonneg.mpr hm.le) hi 2

theorem completed_sampled_weighted_thermal_le (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ≥0)
    {a width g mesh osc : ℝ} (ha0 : 0 < a) (hw : 0 < width)
    (hg : 0 < g) (hmesh0 : 0 ≤ mesh) (hosc : 0 ≤ osc)
    (as : List PositiveMass) (ha : MassOrdered 0 as)
    (hmesh : ∀ w ∈ sampleMassDurations 0 as, (w:ℝ) ≤ mesh)
    (hgap : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      g*(v-u) ≤ (h v:ℝ)-(h u:ℝ))
    (weight : ℕ → ℝ) (hweight : ∀ j < as.length, weight j ∈ Icc (0:ℝ) 1)
    (hcut : ∀ j < as.length, 0 < weight j →
      a ≤ physicalCutMass 0 (sampleClockSteps (completedPathClock (n+1) b h) 0 as) j)
    (hbuffers : ∀ j < as.length, 0 < weight j → Nonempty
      (PhysicalCutBufferGeometry (n+1) (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
        (completedPathClock (n+1) b h 0) a width osc j)) :
    let q := completedPathClock (n+1) b h
    let steps := sampleClockSteps q 0 as
    massCellSum as 0 (fun j => weight j*(
      rootLevelPairMean (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0)
        (fun sigma tau => (orderedOverlap (n+1) sigma tau)^2) steps j-
      (physicalPathSecondMoment (n+1) steps (q 0) j)^2)) ≤
      56*width⁻¹^2*(2/((n+1:ℝ)*g)+2*mesh)/a+3*osc^2+
        2*Real.sqrt (2/((n+1:ℝ)*g)+2*mesh)/a+(2/((n+1:ℝ)*g)+2*mesh)/a^2 := by
  dsimp only
  let q := completedPathClock (n+1) b h
  let steps := sampleClockSteps q 0 as
  let mu := rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps
  let H := fun j => ∫ p, physicalCutSourceSquareTrace (n+1) steps id j p ∂mu
  let C := fun j => ∫ p, physicalCutSpinTraceCovSq (n+1) steps id j p ∂mu
  let T := 2/((n+1:ℝ)*g)+2*mesh
  let K := 56*width⁻¹^2*T/a+3*osc^2
  have ho := sampleClockSteps_ordered q as ha
  have hH (j) : 0 ≤ H j := integral_nonneg fun p =>
    (physicalCutSourceSquareTrace_mem_Icc (n+1) steps ho id j p).1
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hp (j) (hj : j < as.length) : weight j*(
      rootLevelPairMean (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0)
        (fun sigma tau => (orderedOverlap (n+1) sigma tau)^2) steps j-
      (physicalPathSecondMoment (n+1) steps (q 0) j)^2) ≤
      K+2*Real.sqrt (H j)/a+H j/a^2 := by
    by_cases hz : weight j=0
    · rw [hz,zero_mul]
      exact add_nonneg (add_nonneg hK (by positivity)) (div_nonneg (hH j) (sq_nonneg a))
    · have hwj : 0 < weight j := lt_of_le_of_ne (hweight j hj).1 (Ne.symm hz)
      obtain ⟨buf⟩ := hbuffers j hj hwj
      have hb := completed_sampled_buffered_thermal_le n d e b h ha0 hg hmesh0 hosc as ha
        hmesh hgap j (Nat.le_of_lt hj) buf.past buf.future
        (by simpa only [sampleClockSteps_length] using buf.past_internal)
        (by simpa only [sampleClockSteps_length] using buf.future_internal)
        buf.past_cut buf.future_cut (hw.trans_le buf.past_mass) (hw.trans_le buf.future_mass)
        buf.past_before buf.future_after buf.past_close buf.future_close
      dsimp only at hb
      have him := inv_square_le_of_positive_lower hw buf.past_mass
      have hip := inv_square_le_of_positive_lower hw buf.future_mass
      have hscale : 28*((physicalWindowMass steps 0 buf.past)⁻¹^2+
          (physicalWindowMass steps 0 buf.future)⁻¹^2)*T/a ≤ 56*width⁻¹^2*T/a := by
        have hs := add_le_add him hip
        have hh := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ) ≤ 28)) (div_nonneg hT ha0.le)
        dsimp only [steps,q]
        convert hh using 1 <;> ring
      have hc := physicalCutSpinTraceCovSq_integral_le_square_of_cutMass (n+1) steps ho ha0
        (Measure.pi fun z => gaussianReal 0 (q 0 z)) id measurable_id j (hcut j hj hwj)
      have hc' : C j ≤ H j/a^2 := by
        simpa only [rootedHierarchyPathLaw,Kernel.comap_id,mu,C,H] using hc
      have hcs : Real.sqrt (C j) ≤ Real.sqrt (H j)/a := by
        have hh := Real.sqrt_le_sqrt hc'
        rw [Real.sqrt_div (hH j),Real.sqrt_sq_eq_abs,abs_of_pos ha0] at hh
        exact hh
      have hcs' : 2*Real.sqrt (C j) ≤ 2*Real.sqrt (H j)/a := by
        calc
          _ ≤ 2*(Real.sqrt (H j)/a) := mul_le_mul_of_nonneg_left hcs (by norm_num)
          _ = _ := by ring
      have hd : rootLevelPairMean (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0)
          (fun sigma tau => (orderedOverlap (n+1) sigma tau)^2) steps j-
          (physicalPathSecondMoment (n+1) steps (q 0) j)^2 ≤
          K+2*Real.sqrt (H j)/a+H j/a^2 := by
        dsimp only [K,T,steps,q] at hscale ⊢
        dsimp only [C,mu,steps,q] at hc' hcs'
        linarith
      have hn : 0 ≤ K+2*Real.sqrt (H j)/a+H j/a^2 :=
        add_nonneg (add_nonneg hK (by positivity)) (div_nonneg (hH j) (sq_nonneg a))
      exact (mul_le_mul_of_nonneg_left hd hwj.le).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (hweight j hj).2 hn)
  have hh := massCellSum_mono as ha hp
  rw [massCellSum_add,massCellSum_add,massCellSum_const] at hh
  have hs := completedSampledWholePath_sqrtTrace_le n d e b h hg hmesh0 as ha hmesh hgap
  have ht := completedSampledWholePath_trace_le n d e b h hg hmesh0 as ha hmesh hgap
  dsimp only at hs ht
  change massCellSum as 0 (fun j => Real.sqrt (H j)) ≤ Real.sqrt T at hs
  change massCellSum as 0 H ≤ T at ht
  have hs' : massCellSum as 0 (fun j => 2*Real.sqrt (H j)/a) ≤ 2*Real.sqrt T/a := by
    calc
      _ = (2/a)*massCellSum as 0 (fun j => Real.sqrt (H j)) := by
        have he : (fun j => 2*Real.sqrt (H j)/a)=(fun j => (2/a)*Real.sqrt (H j)) := by
          funext j; ring
        rw [he,massCellSum_const_mul]
      _ ≤ (2/a)*Real.sqrt T := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have ht' : massCellSum as 0 (fun j => H j/a^2) ≤ T/a^2 := by
    calc
      _ = (a^2)⁻¹*massCellSum as 0 H := by
        have he : (fun j => H j/a^2)=(fun j => (a^2)⁻¹*H j) := by funext j; simp only [div_eq_mul_inv,mul_comm]
        rw [he,massCellSum_const_mul]
      _ ≤ (a^2)⁻¹*T := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  have he := mul_le_mul_of_nonneg_right ha.end_bounds.2 hK
  have he' : (partitionEnd 0 as-0)*K ≤ K := by simpa only [sub_zero,one_mul] using he
  have hb := hh.trans (add_le_add (add_le_add he' hs') ht')
  simpa only [K,T,steps,q] using hb

theorem physical_root_thermal_mem_Icc (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (i : ℕ) (hi : i ≤ steps.length) :
    rootLevelPairMean (uniformWeight n) (finiteFeature n) q0
      (fun sigma tau => (orderedOverlap n sigma tau)^2) steps i-
      (physicalPathSecondMoment n steps q0 i)^2 ∈ Icc (0:ℝ) 1 := by
  rw [physicalSecondMoment_eq_rootLevelPairMean n steps ha q0 i hi]
  have h := rootLevelPairMean_SK_bounds n (uniformWeight_pos n) (finiteFeature n) q0 steps ha i
  dsimp only at h
  have hn := sq_nonneg (rootLevelPairMean (uniformWeight n) (finiteFeature n) q0 (orderedOverlap n) steps i)
  exact ⟨sub_nonneg.mpr h.2.2.1,by linarith⟩

theorem massCellSum_le_weighted_add_omitted (as : List PositiveMass) (ha : MassOrdered 0 as)
    (f weight : ℕ → ℝ) (hf : ∀ j < as.length, f j ∈ Icc (0:ℝ) 1)
    (hw : ∀ j < as.length, weight j ∈ Icc (0:ℝ) 1) :
    massCellSum as 0 f ≤ massCellSum as 0 (fun j => weight j*f j)+
      massCellSum as 0 (fun j => 1-weight j) := by
  rw [← massCellSum_add]
  apply massCellSum_mono as ha
  intro j hj
  have hh := mul_le_mul_of_nonneg_left (hf j hj).2 (sub_nonneg.mpr (hw j hj).2)
  nlinarith

theorem massStepFunction_congr_upto (as : List PositiveMass) (f g : ℕ → ℝ)
    (he : ∀ j ≤ as.length, f j=g j) : massStepFunction as f=massStepFunction as g := by
  induction as generalizing f g with
  | nil => funext u; exact he 0 le_rfl
  | cons b bs ih =>
    have ht : massStepFunction bs (fun j => f (j+1))=massStepFunction bs (fun j => g (j+1)) :=
      ih _ _ (fun j hj => he (j+1) (by simp only [List.length_cons]; omega))
    funext u
    simp only [massStepFunction,he 0 (by simp),ht]

theorem physicalSampledS_eq_rooted_massStepFunction (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    physicalSampledS n b h as ha = massStepFunction as (fun j =>
      physicalPathSecondMoment (n+1) (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
        (completedPathClock (n+1) b h 0) j) := by
  unfold physicalSampledS
  rw [physicalStepPairMoment_eq_rooted_massStepFunction (n+1) _ _
    (sampleClockSteps_ordered _ as ha),sampleClockSteps_masses]
  apply massStepFunction_congr_upto
  intro j hj
  exact (physicalSecondMoment_eq_rootLevelPairMean (n+1) _
    (sampleClockSteps_ordered _ as ha) _ j (by simpa only [sampleClockSteps_length] using hj)).symm

theorem physicalSampledThermal_eq_rooted_massStepFunction (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) :
    physicalSampledThermal n b h as ha = massStepFunction as (fun j =>
      rootLevelPairMean (uniformWeight (n+1)) (finiteFeature (n+1))
        (completedPathClock (n+1) b h 0) (fun sigma tau => (orderedOverlap (n+1) sigma tau)^2)
        (sampleClockSteps (completedPathClock (n+1) b h) 0 as) j-
      (physicalPathSecondMoment (n+1) (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
        (completedPathClock (n+1) b h 0) j)^2) := by
  unfold physicalSampledThermal
  rw [physicalSampledB_eq_rooted_massStepFunction,physicalSampledS_eq_rooted_massStepFunction]
  funext u
  simp only [pow_two,← massStepFunction_mul,← massStepFunction_sub]

theorem physicalSampledThermal_integral_eq_massCellSum (n : ℕ) (b h : ℝ → ℝ≥0)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1) :
    (∫ u in 0..1, physicalSampledThermal n b h as ha u) =
    massCellSum as 0 (fun j => rootLevelPairMean (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) b h 0) (fun sigma tau => (orderedOverlap (n+1) sigma tau)^2)
      (sampleClockSteps (completedPathClock (n+1) b h) 0 as) j-
      (physicalPathSecondMoment (n+1) (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
        (completedPathClock (n+1) b h 0) j)^2) := by
  rw [physicalSampledThermal_eq_rooted_massStepFunction,← he,← massCellSum_eq_integral as ha]

theorem physical_profile_oscillation (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) {l r i j : ℕ}
    (hr : r ≤ steps.length) (hli : l ≤ i) (hir : i ≤ r) (hlj : l ≤ j) (hjr : j ≤ r)
    {osc : ℝ} (hspread : physicalPathSecondMoment n steps q0 r-
      physicalPathSecondMoment n steps q0 l ≤ osc) :
    |physicalPathSecondMoment n steps q0 j-physicalPathSecondMoment n steps q0 i| ≤ osc := by
  have hli' := physicalPathSecondMoment_mono n steps ha q0 hli (hir.trans hr)
  have hir' := physicalPathSecondMoment_mono n steps ha q0 hir hr
  have hlj' := physicalPathSecondMoment_mono n steps ha q0 hlj (hjr.trans hr)
  have hjr' := physicalPathSecondMoment_mono n steps ha q0 hjr hr
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem physicalRetained_cut_buffers (n : ℕ) (q : ℝ → FeatureIndex n → ℝ≥0)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (a b c d : PositiveMass) (ha : a ∈ as) (hb : b ∈ as) (hc : c ∈ as) (hd : d ∈ as)
    (hab : a.val ≤ b.val) (hbc : b.val ≤ c.val) (hcd : c.val ≤ d.val)
    {threshold width osc : ℝ} (hta : threshold ≤ a.val)
    (hwm : width ≤ b.val-a.val) (hwp : width ≤ d.val-c.val)
    (i : ℕ) (hbi : retainedMassPrefixIndex b.val as ≤ i)
    (hic : i ≤ retainedMassPrefixIndex c.val as)
    (hspread : physicalPathSecondMoment n (sampleClockSteps q 0 as) (q 0)
      (retainedMassPrefixIndex d.val as)-
      physicalPathSecondMoment n (sampleClockSteps q 0 as) (q 0)
      (retainedMassPrefixIndex a.val as) ≤ osc) :
    Nonempty (PhysicalCutBufferGeometry n (sampleClockSteps q 0 as) (q 0)
      threshold width osc i) := by
  let steps := sampleClockSteps q 0 as
  let pa := retainedMassPrefixIndex a.val as
  let pb := retainedMassPrefixIndex b.val as
  let pc := retainedMassPrefixIndex c.val as
  let pd := retainedMassPrefixIndex d.val as
  let Jm := physicalIntervalCells steps pa pb
  let Jp := physicalIntervalCells steps pc pd
  have ho' := sampleClockSteps_ordered q as ho
  have hpab : pa ≤ pb := retainedMassPrefixIndex_monotone as ho a b ha hb hab
  have hpbc : pb ≤ pc := retainedMassPrefixIndex_monotone as ho b c hb hc hbc
  have hpcd : pc ≤ pd := retainedMassPrefixIndex_monotone as ho c d hc hd hcd
  have hpd : pd ≤ steps.length := by
    simpa only [steps,sampleClockSteps_length] using retainedMassPrefixIndex_le_length d.val as
  have hpb : pb ≤ steps.length := (hpbc.trans hpcd).trans hpd
  have hgeom := physicalRetainedPastFuture_bracket q as a.val b.val c.val d.val i hbi hic
  have hgm := physicalRetainedWindow_geometry q as ho a b ha hb hab
  have hgp := physicalRetainedWindow_geometry q as ho c d hc hd hcd
  dsimp only at hgm hgp
  have hmj (j) (hj : j ∈ Jm) : pa ≤ j.val ∧ j.val ≤ pd := by
    have hh := (mem_physicalIntervalCells steps pa pb j).mp hj
    exact ⟨hh.1,(hh.2.le.trans hpbc).trans hpcd⟩
  have hpj (j) (hj : j ∈ Jp) : pa ≤ j.val ∧ j.val ≤ pd := by
    have hh := (mem_physicalIntervalCells steps pc pd j).mp hj
    exact ⟨(hpab.trans hpbc).trans hh.1,hh.2.le⟩
  refine ⟨{
    past := Jm
    future := Jp
    past_internal := ?_
    future_internal := ?_
    past_cut := fun j hj => hta.trans ((hgm.2 j hj).1)
    future_cut := fun j hj => (hta.trans (hab.trans hbc)).trans ((hgp.2 j hj).1)
    past_mass := ?_
    future_mass := ?_
    past_before := hgeom.1
    future_after := hgeom.2
    past_close := ?_
    future_close := ?_
  }⟩
  · intro j hj
    exact (mem_physicalIntervalCells steps 0 steps.length j).mpr
      ⟨Nat.zero_le _,((mem_physicalIntervalCells steps pa pb j).mp hj).2.trans_le hpb⟩
  · intro j hj
    exact (mem_physicalIntervalCells steps 0 steps.length j).mpr
      ⟨Nat.zero_le _,((mem_physicalIntervalCells steps pc pd j).mp hj).2.trans_le hpd⟩
  · exact hwm.trans_eq hgm.1.symm
  · exact hwp.trans_eq hgp.1.symm
  · intro j hj
    exact physical_profile_oscillation n steps ho' (q 0) hpd (hpab.trans hbi)
      (hic.trans hpcd) (hmj j hj).1 (hmj j hj).2 hspread
  · intro j hj
    exact physical_profile_oscillation n steps ho' (q 0) hpd (hpab.trans hbi)
      (hic.trans hpcd) (hpj j hj).1 (hpj j hj).2 hspread

theorem completed_sampled_thermal_le_geometric_omission (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ≥0)
    {a width g mesh osc : ℝ} (ha0 : 0 < a) (hw : 0 < width)
    (hg : 0 < g) (hmesh0 : 0 ≤ mesh) (hosc : 0 ≤ osc)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (hmesh : ∀ w ∈ sampleMassDurations 0 as, (w:ℝ) ≤ mesh)
    (hgap : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      g*(v-u) ≤ (h v:ℝ)-(h u:ℝ))
    (weight : ℕ → ℝ) (hweight : ∀ j < as.length, weight j ∈ Icc (0:ℝ) 1)
    (hcut : ∀ j < as.length, 0 < weight j →
      a ≤ physicalCutMass 0 (sampleClockSteps (completedPathClock (n+1) b h) 0 as) j)
    (hbuffers : ∀ j < as.length, 0 < weight j → Nonempty
      (PhysicalCutBufferGeometry (n+1) (sampleClockSteps (completedPathClock (n+1) b h) 0 as)
        (completedPathClock (n+1) b h 0) a width osc j)) :
    (∫ u in 0..1, physicalSampledThermal n b h as ha u) ≤
      56*width⁻¹^2*(2/((n+1:ℝ)*g)+2*mesh)/a+3*osc^2+
        2*Real.sqrt (2/((n+1:ℝ)*g)+2*mesh)/a+(2/((n+1:ℝ)*g)+2*mesh)/a^2+
        massCellSum as 0 (fun j => 1-weight j) := by
  rw [physicalSampledThermal_integral_eq_massCellSum n b h as ha he]
  let q := completedPathClock (n+1) b h
  let steps := sampleClockSteps q 0 as
  let F := fun j => rootLevelPairMean (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0)
    (fun sigma tau => (orderedOverlap (n+1) sigma tau)^2) steps j-
    (physicalPathSecondMoment (n+1) steps (q 0) j)^2
  have hwhole := massCellSum_le_weighted_add_omitted as ha F weight
    (fun j hj => physical_root_thermal_mem_Icc (n+1) steps (sampleClockSteps_ordered q as ha) (q 0) j
      (by simpa only [steps,sampleClockSteps_length] using Nat.le_of_lt hj)) hweight
  have hselected := completed_sampled_weighted_thermal_le n d e b h ha0 hw hg hmesh0 hosc
    as ha hmesh hgap weight hweight hcut hbuffers
  dsimp only at hselected
  exact hwhole.trans (add_le_add hselected le_rfl)

def physicalSelectionWeight {ι : Type} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (i : ℕ) : ℝ :=
  if ∃ j ∈ J, j.val=i then 1 else 0

theorem physicalSelectionWeight_mem_Icc {ι : Type} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (i : ℕ) :
    physicalSelectionWeight steps J i ∈ Icc (0:ℝ) 1 := by
  unfold physicalSelectionWeight
  split_ifs <;> norm_num

theorem physicalSelectionWeight_at_fin {ι : Type} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (j : Fin (steps.length+1)) :
    physicalSelectionWeight steps J j.val=if j∈J then 1 else 0 := by
  have he : (∃ k∈J, k.val=j.val) ↔ j∈J := by
    constructor
    · rintro ⟨k,hk,hkj⟩
      have h := Fin.ext hkj
      simpa only [h] using hk
    · intro hj; exact ⟨j,hj,rfl⟩
  simp only [physicalSelectionWeight,he]

theorem physicalSelectionWeight_pos_iff {ι : Type} (steps : List (GaussianStep ι))
    (J : Finset (Fin (steps.length+1))) (i : ℕ) :
    0 < physicalSelectionWeight steps J i ↔ ∃ j∈J, j.val=i := by
  unfold physicalSelectionWeight
  split_ifs <;> simp_all

theorem physicalSampledInternalCellSum_eq_massCellSum {ι : Type}
    (q : ℝ → ι → ℝ≥0) (as : List PositiveMass) (f : ℕ → ℝ) :
    let steps := sampleClockSteps q 0 as
    (∑ j, physicalWindowCellMass steps 0 (physicalIntervalCells steps 0 as.length) j*f j.val)=
      massCellSum as 0 f := by
  dsimp only
  have he := physicalWindowCellSum_internal_massCellSum q [] as [] (a := (0:ℝ)) rfl f
  dsimp only at he
  simp only [List.length_nil,Nat.zero_add] at he
  let G := fun ss : List (GaussianStep ι) =>
    ∑ j, physicalWindowCellMass ss 0 (physicalIntervalCells ss 0 as.length) j*f j.val
  change G ((sampleClockSteps q 0 []++sampleClockSteps q 0 as)++[])=massCellSum as 0 f at he
  simp only [sampleClockSteps,List.nil_append,List.append_nil] at he
  exact he

theorem physicalSelectionWeight_omitted_mass {ι : Type}
    (q : ℝ → ι → ℝ≥0) (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) :
    massCellSum as 0 (fun j => 1-physicalSelectionWeight (sampleClockSteps q 0 as) J j)=
      physicalWindowMass (sampleClockSteps q 0 as) 0
        ((physicalIntervalCells (sampleClockSteps q 0 as) 0 as.length)\J) := by
  rw [← physicalSampledInternalCellSum_eq_massCellSum q as]
  unfold physicalWindowMass
  have hs : (∑ j : Fin ((sampleClockSteps q 0 as).length+1),
      if j∈(physicalIntervalCells (sampleClockSteps q 0 as) 0 as.length)\J then
        pathMassDifferences (sampleClockSteps q 0 as) 0 j else 0)=
      ∑ j∈(physicalIntervalCells (sampleClockSteps q 0 as) 0 as.length)\J,
        pathMassDifferences (sampleClockSteps q 0 as) 0 j := by
    simp only [Finset.sum_ite_mem,Finset.univ_inter]
  rw [← hs]
  apply Finset.sum_congr rfl
  intro j hj
  rw [physicalSelectionWeight_at_fin]
  unfold physicalWindowCellMass
  by_cases hi : j∈physicalIntervalCells (sampleClockSteps q 0 as) 0 as.length
  · by_cases hJ : j∈J
    · simp [hi,hJ]
    · simp [hi,hJ]
  · simp [hi]

theorem completed_sampled_thermal_le_retained_grid (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ≥0)
    {a width g mesh osc : ℝ} (ha0 : 0 < a) (hw : 0 < width)
    (hg : 0 < g) (hmesh0 : 0 ≤ mesh) (hosc : 0 < osc)
    (as : List PositiveMass) (ha : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (hmesh : ∀ w ∈ sampleMassDurations 0 as, (w:ℝ) ≤ mesh)
    (hgap : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      g*(v-u) ≤ (h v:ℝ)-(h u:ℝ))
    (u : ℕ → PositiveMass) (hu : ∀ i, u i∈as) (hU : Monotone (fun i => (u i).val))
    (N : ℕ) (hgrid : ∀ i ≤ N+2, (u i).val=a+(i:ℝ)*width)
    (hunit : (u (N+2)).val=1) :
    (∫ v in 0..1, physicalSampledThermal n b h as ha v) ≤
      56*width⁻¹^2*(2/((n+1:ℝ)*g)+2*mesh)/a+3*osc^2+
        2*Real.sqrt (2/((n+1:ℝ)*g)+2*mesh)/a+(2/((n+1:ℝ)*g)+2*mesh)/a^2+
        a+2*width+3*width/osc := by
  let q := completedPathClock (n+1) b h
  let steps := sampleClockSteps q 0 as
  let P := fun i => retainedMassPrefixIndex (u i).val as
  let S := fun i => physicalPathSecondMoment (n+1) steps (q 0) (P i)
  let J := coarsePhysicalGoodCells steps P S N osc
  let weight := physicalSelectionWeight steps J
  have ho := sampleClockSteps_ordered q as ha
  have hP : Monotone P := fun i j hij =>
    retainedMassPrefixIndex_monotone as ha (u i) (u j) (hu i) (hu j) (hU hij)
  have hPL (i) : P i ≤ steps.length := by
    simpa only [steps,sampleClockSteps_length] using retainedMassPrefixIndex_le_length (u i).val as
  have hS : Monotone S := fun i j hij =>
    physicalPathSecondMoment_mono (n+1) steps ho (q 0) (hP hij) (hPL j)
  have hS0 : 0 ≤ S 0 := physicalPathSecondMoment_nonneg (n+1) steps (q 0) _
  have hS1 : S (N+2) ≤ 1 := physicalPathSecondMoment_le_one (n+1) steps ho (q 0) (hPL _)
  have hnode (i) : a ≤ (u i).val := by
    have hh := hU (Nat.zero_le i)
    dsimp only at hh
    rw [hgrid 0 (by omega)] at hh
    simpa only [Nat.cast_zero,zero_mul,add_zero] using hh
  have hcut (i : ℕ) (hi : i < as.length) (hwi : 0 < weight i) :
      a ≤ physicalCutMass 0 steps i := by
    obtain ⟨j,hj,hji⟩ := (physicalSelectionWeight_pos_iff steps J i).mp hwi
    obtain ⟨k,hk,hgood,hleft,hright⟩ := coarsePhysicalGoodCells_index steps P S N osc hj
    have hh := physicalCutMass_monotone steps ho hleft
    change physicalCutMass 0 steps (P (k+1)) ≤ physicalCutMass 0 steps j.val at hh
    rw [physicalCutMass_retained_prefix q as ha (u (k+1)) (hu _),hji] at hh
    exact (hnode _).trans hh
  have hbuffers (i : ℕ) (hi : i < as.length) (hwi : 0 < weight i) :
      Nonempty (PhysicalCutBufferGeometry (n+1) steps (q 0) a width osc i) := by
    obtain ⟨j,hj,hji⟩ := (physicalSelectionWeight_pos_iff steps J i).mp hwi
    obtain ⟨k,hk,hgood,hleft,hright⟩ := coarsePhysicalGoodCells_index steps P S N osc hj
    have hwm : width ≤ (u (k+1)).val-(u k).val := by
      rw [hgrid (k+1) (by omega),hgrid k (by omega)]
      norm_num only [Nat.cast_add,Nat.cast_one]
      linarith
    have hwp : width ≤ (u (k+3)).val-(u (k+2)).val := by
      rw [hgrid (k+3) (by omega),hgrid (k+2) (by omega)]
      norm_num only [Nat.cast_add,Nat.cast_ofNat]
      linarith
    exact physicalRetained_cut_buffers (n+1) q as ha (u k) (u (k+1)) (u (k+2)) (u (k+3))
      (hu _) (hu _) (hu _) (hu _) (hU (by omega)) (hU (by omega)) (hU (by omega))
      (hnode k) hwm hwp i (hji ▸ hleft) (hji ▸ hright.le) hgood
  have hwhole := completed_sampled_thermal_le_geometric_omission n d e b h ha0 hw hg hmesh0
    hosc.le as ha he hmesh hgap weight (fun j _ => physicalSelectionWeight_mem_Icc steps J j)
    hcut hbuffers
  have homit := retainedEqualWidthGoodCells_omitted_mass q as ha he u hu hU N hw.le hosc
    hgrid hunit S hS hS0 hS1
  dsimp only at homit
  have hm : massCellSum as 0 (fun j => 1-weight j) ≤ a+2*width+3*width/osc := by
    rw [physicalSelectionWeight_omitted_mass q as J]
    have hlen : steps.length=as.length := sampleClockSteps_length q 0 as
    change physicalWindowMass steps 0 ((physicalIntervalCells steps 0 as.length)\J) ≤ _
    rw [← hlen]
    exact homit
  have hb := hwhole.trans (add_le_add le_rfl hm)
  linarith

theorem completed_ordered_thermal_le_field_gap (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    {a g osc : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hg : 0 < g) (hosc : 0 < osc)
    (N : ℕ)
    (hgap : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      g*(v-u) ≤ (h v:ℝ)-(h u:ℝ)) :
    let width := coarseMassWidth a N
    (∫ u in 0..1, orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2) ≤
      56*width⁻¹^2*(2/((n+1:ℝ)*g))/a+3*osc^2+
        2*Real.sqrt (2/((n+1:ℝ)*g))/a+(2/((n+1:ℝ)*g))/a^2+
        a+2*width+3*width/osc := by
  dsimp only
  let us := coarseMassNodes ha0 ha1 N
  let hu := coarseMassNodes_bound ha0 ha1 N
  let as := finiteCutMasses us
  let mesh := fun k : ℕ => ((k+1:ℕ):ℝ)⁻¹
  let width := coarseMassWidth a N
  let T := 2/((n+1:ℝ)*g)
  let R := fun x : ℝ => 56*width⁻¹^2*(T+2*x)/a+3*osc^2+
    2*Real.sqrt (T+2*x)/a+(T+2*x)/a^2+a+2*width+3*width/osc
  have hR : Continuous R := by dsimp only [R]; fun_prop
  have hleft := physicalSampledThermal_integral_tendsto n b h hb hh as mesh
    (finiteCutMasses_ordered us hu) (finiteCutMasses_end us hu)
    (finiteCutMasses_mesh us hu) uniformMasses_mesh_tendsto
  have hright : Tendsto (fun k => R (mesh k)) atTop (𝓝 (R 0)) :=
    (hR.tendsto 0).comp uniformMasses_mesh_tendsto
  have hfinite (k : ℕ) : (∫ u in 0..1, physicalSampledThermal n b h (as k)
      (finiteCutMasses_ordered us hu k) u) ≤ R (mesh k) := by
    exact completed_sampled_thermal_le_retained_grid n d e b h ha0
      (coarseMassWidth_pos ha1 N) hg (by dsimp only [mesh]; positivity) hosc
      (as k) (finiteCutMasses_ordered us hu k) (finiteCutMasses_end us hu k)
      (sampleMassDurations_mesh _ (finiteCutMasses_ordered us hu k) (finiteCutMasses_mesh us hu k))
      hgap (coarseMassNode ha0 ha1 N)
      (fun i => finiteCutMasses_nodes us k (coarseMassNode_mem ha0 ha1 N i))
      (coarseMassNode_monotone ha0 ha1 N) N
      (fun i hi => coarseMassNode_grid ha0 ha1 N i hi) (coarseMassNode_last ha0 ha1 N)
  have hbound := le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hfinite)
  simpa only [R,T,width,mul_zero,zero_mul,add_zero] using hbound

def thermalBufferBudget (a : ℝ) (N : ℕ) (osc T : ℝ) : ℝ :=
  let width := coarseMassWidth a N
  56*width⁻¹^2*T/a+3*osc^2+2*Real.sqrt T/a+T/a^2+a+2*width+3*width/osc

theorem thermalBufferBudget_continuous (a : ℝ) (N : ℕ) (osc : ℝ) :
    Continuous (thermalBufferBudget a N osc) := by
  unfold thermalBufferBudget
  fun_prop

theorem thermalBufferBudget_monotone {a : ℝ} (ha : 0 < a) (N : ℕ) (osc : ℝ) :
    Monotone (thermalBufferBudget a N osc) := by
  intro T U hTU
  unfold thermalBufferBudget
  have h1 := mul_le_mul_of_nonneg_left hTU (show 0 ≤ 56*(coarseMassWidth a N)⁻¹^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hTU) (by norm_num : (0:ℝ) ≤ 2)
  have h3 := div_le_div_of_nonneg_right hTU (sq_nonneg a)
  have h1' := div_le_div_of_nonneg_right h1 ha.le
  have h2' := div_le_div_of_nonneg_right h2 ha.le
  linarith

theorem coarseMassWidth_tendsto (a : ℝ) :
    Tendsto (coarseMassWidth a) atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (1-a)/(N+2:ℝ)) atTop (𝓝 0)
  have ht := uniformMasses_mesh_tendsto.comp (tendsto_add_atTop_nat 1)
  have hh := ht.const_mul (1-a)
  simpa only [coarseMassWidth,Function.comp_apply,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,
    add_assoc,one_add_one_eq_two,div_eq_mul_inv,mul_zero] using hh

theorem exists_thermalBufferBudget_parameters {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∃ N : ℕ, ∃ osc : ℝ, 0 < osc ∧
      ∃ delta : ℝ, 0 < delta ∧ thermalBufferBudget a N osc delta < epsilon := by
  let a := min (epsilon/16) (1/4:ℝ)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have ha4 : a ≤ (1/4:ℝ) := min_le_right _ _
  have haeps : a ≤ epsilon/16 := min_le_left _ _
  have ha1 : a < 1 := lt_of_le_of_lt ha4 (by norm_num)
  have hsmall : a+3*a^2 < epsilon/2 := by nlinarith
  let L := a+3*a^2
  let F := fun N : ℕ => L+(2+3/a)*coarseMassWidth a N
  have ht : Tendsto F atTop (𝓝 L) := by
    simpa only [F,mul_zero,add_zero] using
      (coarseMassWidth_tendsto a).const_mul (2+3/a) |>.const_add L
  have hev : ∀ᶠ N : ℕ in atTop, F N < epsilon/2 := ht.eventually (eventually_lt_nhds hsmall)
  obtain ⟨N,hN⟩ := hev.exists
  have hb : thermalBufferBudget a N a 0 < epsilon := by
    have he : thermalBufferBudget a N a 0=F N := by
      unfold thermalBufferBudget F L
      rw [Real.sqrt_zero]
      ring
    rw [he]
    linarith
  have hnear : ∀ᶠ T : ℝ in 𝓝 (0:ℝ), thermalBufferBudget a N a T < epsilon :=
    (thermalBufferBudget_continuous a N a).continuousAt.eventually (eventually_lt_nhds hb)
  obtain ⟨delta,hd,hnear⟩ := Metric.eventually_nhds_iff.mp hnear
  have hhalf : thermalBufferBudget a N a (delta/2) < epsilon := by
    apply hnear
    rw [dist_zero_right,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < delta/2)]
    linarith
  exact ⟨a,ha,ha1,N,a,ha,delta/2,by positivity,hhalf⟩

theorem exists_physical_thermal_trace_threshold {epsilon : ℝ} (heps : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ (n d : ℕ)
      (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ≥0)
      (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
      (g : ℝ), 0 < g →
      (∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
        g*(v-u) ≤ (h v:ℝ)-(h u:ℝ)) →
      2/((n+1:ℝ)*g) ≤ delta →
      (∫ u in 0..1, orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2) < epsilon := by
  obtain ⟨a,ha0,ha1,N,osc,hosc,delta,hd,hsmall⟩ := exists_thermalBufferBudget_parameters heps
  refine ⟨delta,hd,?_⟩
  intro n d e b h hb hh g hg hgap hT
  have hbound := completed_ordered_thermal_le_field_gap n d e b h hb hh ha0 ha1 hg hosc N hgap
  dsimp only at hbound
  change _ ≤ thermalBufferBudget a N osc (2/((n+1:ℝ)*g)) at hbound
  exact (hbound.trans (thermalBufferBudget_monotone ha0 N osc hT)).trans_lt hsmall

theorem physicalOrderedThermal_nonneg (n : ℕ) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) :
    0 ≤ ∫ u in 0..1, orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2 := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply integral_nonneg_of_ae
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  filter_upwards [] with u hu
  exact sub_nonneg.mpr (orderedPath_SK_bounds (n+1) (by omega) b h hb hh hu).2.2.1

theorem completed_ordered_thermal_tendsto (d : ℕ → ℕ)
    (e : ∀ n, Fin (d n+1) ≃ FeatureIndex (n+1))
    (b h : ℕ → ℝ → ℝ≥0)
    (hb : ∀ n, MonotoneOn (b n) (Icc (0:ℝ) 1))
    (hh : ∀ n, MonotoneOn (h n) (Icc (0:ℝ) 1))
    (g : ℕ → ℝ) (hg : ∀ n, 0 < g n)
    (hgap : ∀ n, ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      g n*(v-u) ≤ (h n v:ℝ)-(h n u:ℝ))
    (hT : Tendsto (fun n : ℕ => 2/((n+1:ℝ)*g n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ u in 0..1, orderedPathB (n+1) (b n) (h n) u-
      (orderedPathS (n+1) (b n) (h n) u)^2) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon heps
  obtain ⟨delta,hd,hsmall⟩ := exists_physical_thermal_trace_threshold heps
  have hev : ∀ᶠ n : ℕ in atTop, 2/((n+1:ℝ)*g n) ≤ delta :=
    hT.eventually (eventually_le_nhds hd)
  obtain ⟨N,hN⟩ := eventually_atTop.mp hev
  refine ⟨N,?_⟩
  intro n hn
  rw [dist_zero_right,Real.norm_eq_abs,abs_of_nonneg
    (physicalOrderedThermal_nonneg n (b n) (h n) (hb n) (hh n))]
  exact hsmall n (d n) (e n) (b n) (h n) (hb n) (hh n) (g n) (hg n) (hgap n) (hN n hn)

theorem macroThermalDefect_le_buffer_budget {η Q t bstar a osc : ℝ}
    (hη : 0 < η) (hQ : 1 < Q) (ht : 0 < t) (ht1 : t ≤ 1) (hbstar : 0 < bstar)
    (α : MacroInverseClass η Q) (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u)
    (ha0 : 0 < a) (ha1 : a < 1) (hosc : 0 < osc) (N : ℕ) :
    macroThermalDefect (n+1) b h (macroInverseQuantile hη hQ α) t ≤
      thermalBufferBudget a N osc (2/((n+1:ℝ)*(t*bstar/Q))) := by
  let q := macroInverseQuantile hη hQ α
  let bf := fun u => ((1-t)*b u).toNNReal
  let hf := fun u => (h u+t*b u*q u).toNNReal
  have hmatrix : MonotoneOn (fun u => (1-t)*b u) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact mul_le_mul_of_nonneg_left (hb hu hv huv) (sub_nonneg.mpr ht1)
  have htb : MonotoneOn (fun u => t*b u) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact mul_le_mul_of_nonneg_left (hb hu hv huv) ht.le
  have hfield : MonotoneOn (fun u => h u+t*b u*q u) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (hh hu hv huv)
      (mul_le_mul (htb hu hv huv) (macroInverseQuantile_monotone hη hQ α hu hv huv)
        (macroInverseQuantile_bounds hη hQ α u).1
        (mul_nonneg ht.le (hbstar.le.trans (hbb v hv))))
  have hnon (u : ℝ) (hu : u ∈ Icc (0:ℝ) 1) : 0 ≤ h u+t*b u*q u :=
    add_nonneg (hhn u hu) (mul_nonneg (mul_nonneg ht.le (hbstar.le.trans (hbb u hu)))
      (macroInverseQuantile_bounds hη hQ α u).1)
  have hgap : ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, u ≤ v →
      (t*bstar/Q)*(v-u) ≤ (hf v:ℝ)-(hf u:ℝ) := by
    intro u hu v hv huv
    rw [Real.coe_toNNReal _ (hnon v hv),Real.coe_toNNReal _ (hnon u hu)]
    exact macro_inverse_field_gap hη hQ α b h ht.le hbstar.le hb hh hbb hu hv huv
  have hd := completed_ordered_thermal_le_field_gap n d e bf hf
    (toNNReal_monotoneOn hmatrix) (toNNReal_monotoneOn hfield) ha0 ha1
    (div_pos (mul_pos ht hbstar) (zero_lt_one.trans hQ)) hosc N hgap
  dsimp only at hd
  exact hd

def physicalFeatureDimension (n : ℕ) : ℕ := Fintype.card (FeatureIndex n)-1

def physicalFeatureEnumeration (n : ℕ) : Fin (physicalFeatureDimension n+1) ≃ FeatureIndex n := by
  letI : Nonempty (FeatureIndex n) := ⟨Sum.inr none⟩
  have hcard : 1 ≤ Fintype.card (FeatureIndex n) := Nat.succ_le_of_lt Fintype.card_pos
  exact (finCongr (Nat.sub_add_cancel hcard)).trans (Fintype.equivFin (FeatureIndex n)).symm

theorem macroThermalDefect_le_buffer_budget_nat {η Q t bstar a osc : ℝ}
    (hη : 0 < η) (hQ : 1 < Q) (ht : 0 < t) (ht1 : t ≤ 1) (hbstar : 0 < bstar)
    (α : MacroInverseClass η Q) (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u)
    (ha0 : 0 < a) (ha1 : a < 1) (hosc : 0 < osc) (N : ℕ) :
    macroThermalDefect n b h (macroInverseQuantile hη hQ α) t ≤
      thermalBufferBudget a N osc (2/((n:ℝ)*(t*bstar/Q))) := by
  cases n with
  | zero => omega
  | succ n =>
    simpa only [Nat.cast_add,Nat.cast_one] using macroThermalDefect_le_buffer_budget hη hQ ht ht1
      hbstar α n (physicalFeatureDimension (n+1)) (physicalFeatureEnumeration (n+1))
      b h hb hh hbb hhn ha0 ha1 hosc N

theorem macro_field_reciprocal_tendsto {tau bstar : ℝ} (htau : 0 < tau) (hbstar : 0 < bstar) :
    Tendsto (fun n : ℕ => 2/((n:ℝ)*(tau*bstar/macroDensityCap n))) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (n:ℝ)^(-(7:ℝ)/8)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,neg_div] using
      (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 7/8)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have he : ∀ᶠ n : ℕ in atTop,
      (2/(tau*bstar))*(n:ℝ)^(-(7:ℝ)/8)=2/((n:ℝ)*(tau*bstar/macroDensityCap n)) := by
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
    have hQ0 : 0 < macroDensityCap n := Real.rpow_pos_of_pos hn0 _
    have hratio : macroDensityCap n/(n:ℝ)=(n:ℝ)^(-(7:ℝ)/8) := by
      unfold macroDensityCap
      rw [div_eq_mul_inv,← Real.rpow_neg_one,← Real.rpow_add hn0]
      norm_num
    rw [← hratio]
    field_simp
  have hh : Tendsto (fun n : ℕ => (2/(tau*bstar))*(n:ℝ)^(-(7:ℝ)/8)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hp.const_mul (2/(tau*bstar))
  exact hh.congr' he

theorem eventually_macroThermalDefect_uniform (b h : ℝ → ℝ)
    {bstar tau epsilon : ℝ} (hbstar : 0 < bstar) (htau : 0 < tau) (heps : 0 < epsilon)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hbb : ∀ u ∈ Icc (0:ℝ) 1, bstar ≤ b u)
    (hhn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ h u) :
    ∀ᶠ n : ℕ in atTop, ∀ (hη : 0 < macroDensityFloor n) (hQ : 1 < macroDensityCap n),
      ∀ t ∈ Icc tau 1, ∀ α : MacroInverseClass (macroDensityFloor n) (macroDensityCap n),
        macroThermalDefect n b h (macroInverseQuantile hη hQ α) t < epsilon := by
  obtain ⟨a,ha0,ha1,N,osc,hosc,delta,hd,hsmall⟩ := exists_thermalBufferBudget_parameters heps
  have hev := (macro_field_reciprocal_tendsto htau hbstar).eventually (eventually_le_nhds hd)
  filter_upwards [hev,eventually_gt_atTop (0:ℕ)] with n htrace hn
  intro hη hQ t ht α
  have ht0 : 0 < t := htau.trans_le ht.1
  have hg0 : 0 < tau*bstar/macroDensityCap n :=
    div_pos (mul_pos htau hbstar) (zero_lt_one.trans hQ)
  have hgle : tau*bstar/macroDensityCap n ≤ t*bstar/macroDensityCap n :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ht.1 hbstar.le) (zero_lt_one.trans hQ).le
  have hden : (n:ℝ)*(tau*bstar/macroDensityCap n) ≤ (n:ℝ)*(t*bstar/macroDensityCap n) :=
    mul_le_mul_of_nonneg_left hgle (by positivity)
  have hrec : 2/((n:ℝ)*(t*bstar/macroDensityCap n)) ≤ delta :=
    (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2)
      (mul_pos (by exact_mod_cast hn) hg0) hden).trans htrace
  have hbnd := macroThermalDefect_le_buffer_budget_nat hη hQ ht0 ht.2 hbstar α n hn
    b h hb hh hbb hhn ha0 ha1 hosc N
  exact (hbnd.trans (thermalBufferBudget_monotone ha0 N osc hrec)).trans_lt hsmall

theorem physicalOrderedThermal_mem_Icc_nat (n : ℕ) (hn : 0 < n) (b h : ℝ → ℝ≥0)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1)) :
    (∫ u in 0..1, orderedPathB n b h u-(orderedPathS n b h u)^2) ∈ Icc (0:ℝ) 1 := by
  have hBI : IntervalIntegrable (orderedPathB n b h) volume 0 1 := by
    simpa only [one_mul,orderedPathB] using orderedPathPair_mul_integrable n hn b h hb hh
      (fun sigma tau => (orderedOverlap n sigma tau)^2) (fun _ => 1) intervalIntegrable_const
  have hI := hBI.sub (orderedPathS_sq_intervalIntegrable n hn b h hb hh)
  have hupper := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ) ≤ 1)
    hI (intervalIntegrable_const (c := (1:ℝ))) (fun u hu => by
      have hh' := orderedPath_SK_bounds n hn b h hb hh ⟨hu.1,hu.2.le⟩
      linarith [sq_nonneg (orderedPathS n b h u)])
  have hnon : 0 ≤ ∫ u in 0..1, orderedPathB n b h u-(orderedPathS n b h u)^2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply integral_nonneg_of_ae
    apply (ae_restrict_iff' measurableSet_Ioc).mpr
    filter_upwards [] with u hu
    exact sub_nonneg.mpr (orderedPath_SK_bounds n hn b h hb hh hu).2.2.1
  exact ⟨hnon,by simpa using hupper⟩

theorem macroThermalDefect_mem_Icc (n : ℕ) (hn : 0 < n) (b h q : ℝ → ℝ)
    (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (hq : MonotoneOn q (Icc (0:ℝ) 1))
    (hbn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ b u) (hqn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ q u)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : macroThermalDefect n b h q t ∈ Icc (0:ℝ) 1 := by
  have hmatrix : MonotoneOn (fun u => (1-t)*b u) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact mul_le_mul_of_nonneg_left (hb hu hv huv) (sub_nonneg.mpr ht.2)
  have htb : MonotoneOn (fun u => t*b u) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact mul_le_mul_of_nonneg_left (hb hu hv huv) ht.1
  have hfield : MonotoneOn (fun u => h u+t*b u*q u) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    exact add_le_add (hh hu hv huv)
      (mul_le_mul (htb hu hv huv) (hq hu hv huv) (hqn u hu) (mul_nonneg ht.1 (hbn v hv)))
  exact physicalOrderedThermal_mem_Icc_nat n hn _ _
    (toNNReal_monotoneOn hmatrix) (toNNReal_monotoneOn hfield)

end OAI.SKFluctuations.LaplaceWindowFormalization
