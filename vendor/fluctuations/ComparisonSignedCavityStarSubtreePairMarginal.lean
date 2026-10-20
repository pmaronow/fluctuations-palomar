module

public import ComparisonSignedCavityActualAnchorMarginal

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy
variable {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem levelPairMean_prefix_add (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (P : S→S→ℝ) (pre tail : List (GaussianStep ι)) (j : ℕ) :
    levelPairMean w φ P (pre++tail) (pre.length+j)=
      prefixTest pre (gaussianHierarchy w φ tail) (levelPairMean w φ P tail j) := by
  induction pre with
  | nil=>simp only [List.nil_append,List.length_nil,Nat.zero_add,prefixTest]
  | cons st pre ih=>
    rcases st with ⟨m,q⟩
    simp only [List.cons_append,List.length_cons,Nat.succ_add,levelPairMean,prefixTest,
      prefixContinuation_hierarchy,ih]

end OAI.SKFluctuations.Hierarchy
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_common_star_subtree_pair_marginal (n : ℕ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre ++ (mid ++ tail)))
    (E : ClockTree (Spin n) tail) (s t : E.Slot) (hst : s ≠ t)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (Q : Spin n → Spin n → ℝ) (x : RestCoordinate n → ℝ) :
    (∫ z,E.expect (restWeight n) (restFeature n)
      (fun j => cumulativeIncrements (q 0) (fun k => q (k+1))
        (pre.length+(mid.length+j)))
      (fun σ => Q (E.atSlot σ s) (E.atSlot σ t)) (exteriorForestStarRoot z)
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x) =
    (ClockTree.pairClock (pre ++ (mid ++ tail)) (pre.length+mid.length+E.splitIndex s t)).disorderExpect
      (restWeight n) (restFeature n) v q
      (fun σ => Q (ClockTree.pairSpin _ _ σ).1 (ClockTree.pairSpin _ _ σ).2) x := by
  let qc := cumulativeIncrements (q 0) (fun k => q (k+1))
  let qs := fun j => qc (pre.length+(mid.length+j))
  have hs : OrderedSteps a (clockSteps pre qc ++
      (clockSteps mid (fun j => qc (pre.length+j)) ++ clockSteps tail qs)) := by
    rw [←nativeExteriorForest_clockSteps_eq]
    exact clockSteps_ordered ho qc
  have hR : BddSmooth 0 (E.expect (restWeight n) (restFeature n) qs
      (fun σ => Q (E.atSlot σ s) (E.atSlot σ t))) :=
    E.nativeAnchor_expect_smooth (restWeight_pos n) (restFeature n)
      ho.suffix_end.suffix_end qs _ 0
  unfold nativeExteriorForestDisorderRootLaw nativeExteriorForestRootLaw
  unfold exteriorForestRootLaw exteriorForestStarRoot
  rw [integral_departedAnchorRootLaw_exterior_test (restWeight_pos n) (restFeature n)
    _ _ _ hs _ _ _ hR]
  rw [ClockTree.disorderExpect_integral (restWeight_pos n) (restFeature n) _ ho]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro y
  dsimp only
  rw [ClockTree.pairClock_expect (restWeight_pos n) (restFeature n) _ ho,
    ClockTree.pairMean_eq_levelPairMean (restWeight_pos n) (restFeature n) _ ho]
  have hc : clockSteps (pre ++ (mid ++ tail)) qc =
      (clockSteps pre qc ++ clockSteps mid (fun j => qc (pre.length+j))) ++ clockSteps tail qs := by
    rw [nativeExteriorForest_clockSteps_eq,List.append_assoc]
  rw [hc]
  have hl : pre.length+mid.length =
      (clockSteps pre qc ++ clockSteps mid (fun j => qc (pre.length+j))).length := by
    simp only [List.length_append,length_clockSteps]
  rw [hl,levelPairMean_prefix_add]
  congr 1
  funext z
  rw [E.expect_pairAtSlot (restWeight_pos n) (restFeature n) ho.suffix_end.suffix_end qs s t hst Q,
    ClockTree.pairMean_eq_levelPairMean (restWeight_pos n) (restFeature n) tail ho.suffix_end.suffix_end]

end OAI.SKFluctuations.Cavity
