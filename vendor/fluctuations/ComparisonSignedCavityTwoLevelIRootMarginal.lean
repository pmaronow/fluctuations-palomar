module

public import ComparisonSignedCavityActualAnchorMarginal

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
  [MeasurableSpace S] [StandardBorelSpace S]

theorem integral_departedAnchorRootLaw_target_test {w : S → ℝ} (hw : ∀ σ,0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (pre mid tail : List (GaussianStep ι))
    {a : ℝ} (hs : OrderedSteps a (pre++(mid++tail))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) [IsFiniteMeasure μ] (x : P → ι → ℝ) (hx : Measurable x)
    {B : (ι → ℝ) → ℝ} (hB : BddSmooth 0 B) :
    (∫ z,B (departedAnchorTargetRoot z) ∂departedAnchorRootLaw w φ pre mid tail μ x hx) =
      ∫ p,prefixTest pre (gaussianHierarchy w φ (mid++tail)) B (x p) ∂μ := by
  rw [←integral_map departedAnchorTargetRoot_measurable.aemeasurable hB.continuous.aestronglyMeasurable,
    departedAnchorRootLaw_target_marginal hw φ pre mid tail hs μ x hx,
    integral_actualPrefixFieldLaw hw φ pre (mid++tail) hs μ x hx hB]

end OAI.SKFluctuations.Hierarchy

namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_common_i_pair_marginal (n : ℕ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre++(mid++tail)))
    (E : ClockTree (Spin n) (mid++tail)) (s : E.Slot)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (Q : Spin n → Spin n → ℝ) (x : RestCoordinate n → ℝ) :
    (∫ z,(E.fork E).expect (restWeight n) (restFeature n)
      (fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+j))
      (fun σ=>Q (E.atSlot σ.1 s) (E.atSlot σ.2 s)) (exteriorForestIRoot z)
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x) =
    (ClockTree.pairClock (pre++(mid++tail)) pre.length).disorderExpect
      (restWeight n) (restFeature n) v q
      (fun σ=>Q (ClockTree.pairSpin _ _ σ).1 (ClockTree.pairSpin _ _ σ).2) x := by
  let qc := cumulativeIncrements (q 0) (fun k=>q (k+1))
  let qi := fun j=>qc (pre.length+j)
  let qs := fun j=>qc (pre.length+(mid.length+j))
  have hs : OrderedSteps a (clockSteps pre qc ++
      (clockSteps mid qi ++ clockSteps tail qs)) := by
    rw [←nativeExteriorForest_clockSteps_eq]
    exact clockSteps_ordered ho qc
  have hR : BddSmooth 0 ((E.fork E).expect (restWeight n) (restFeature n) qi
      (fun σ=>Q (E.atSlot σ.1 s) (E.atSlot σ.2 s))) :=
    (E.fork E).nativeAnchor_expect_smooth (restWeight_pos n) (restFeature n)
      ho.suffix_end qi _ 0
  unfold nativeExteriorForestDisorderRootLaw nativeExteriorForestRootLaw
  unfold exteriorForestRootLaw exteriorForestIRoot
  rw [integral_departedAnchorRootLaw_target_test (restWeight_pos n) (restFeature n)
    _ _ _ hs _ _ _ hR]
  rw [ClockTree.disorderExpect_integral (restWeight_pos n) (restFeature n) _ ho]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [ClockTree.pairClock_expect (restWeight_pos n) (restFeature n) _ ho,
    ClockTree.pairMean_eq_levelPairMean (restWeight_pos n) (restFeature n) _ ho]
  rw [nativeExteriorForest_clockSteps_eq]
  have hl : pre.length=(clockSteps pre qc).length := by simp only [length_clockSteps]
  rw [hl,levelPairMean_prefix]
  simp only [length_clockSteps]
  congr 1
  funext z
  have hpair := native_fork_same_slot_expect_eq_root_pair n E ho.suffix_end s qi Q z
  simpa only [clockSteps_append,qi,qs,Nat.add_assoc] using hpair

end OAI.SKFluctuations.Cavity
