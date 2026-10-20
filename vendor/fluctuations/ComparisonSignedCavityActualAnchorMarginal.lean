module

public import ComparisonSignedCavityNativeAnchorRawMoment
public import ComparisonSignedCavityMinimumSourceClocks
public import ComparisonSignedCavityLowAllocation
public import ComparisonSignedCavityExteriorForestDisorder
public import CavityPhysicalWeightedExterior

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_fork_same_slot_expect_eq_root_pair (n : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (s : E.Slot) (q : ℕ → RestCoordinate n → ℝ≥0)
    (Q : Spin n → Spin n → ℝ) (x : RestCoordinate n → ℝ) :
    (E.fork E).expect (restWeight n) (restFeature n) q
      (fun σ => Q (E.atSlot σ.1 s) (E.atSlot σ.2 s)) x =
      hierarchyPairMean (restWeight n) (restFeature n) Q (clockSteps as q) x := by
  have H := (E.fork E).expect_pairAtSlot (restWeight_pos n) (restFeature n) ho q
    (Sum.inl s) (Sum.inr s) (by exact Sum.inl_ne_inr) Q x
  simp only [ClockTree.atSlot,ClockTree.splitIndex,Sum.elim_inl,Sum.elim_inr] at H
  rw [H,ClockTree.pairMean_eq_levelPairMean (restWeight_pos n) (restFeature n) as ho]
  cases as <;> rfl

theorem native_twin_star_pair_marginal (n : ℕ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre ++ (mid ++ tail)))
    (E : ClockTree (Spin n) tail) (s : E.Slot)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (Q : Spin n → Spin n → ℝ) (x : RestCoordinate n → ℝ) :
    (∫ z,(E.fork E).expect (restWeight n) (restFeature n)
      (fun j => cumulativeIncrements (q 0) (fun k => q (k+1))
        (pre.length+(mid.length+j)))
      (fun σ => Q (E.atSlot σ.1 s) (E.atSlot σ.2 s)) (twinPrefixBRoot z)
      ∂nativeTwinPrefixDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x) =
    (ClockTree.pairClock (pre ++ (mid ++ tail)) (pre.length+mid.length)).disorderExpect
      (restWeight n) (restFeature n) v q
      (fun σ => Q (ClockTree.pairSpin _ _ σ).1 (ClockTree.pairSpin _ _ σ).2) x := by
  let qc := cumulativeIncrements (q 0) (fun k => q (k+1))
  let qs := fun j => qc (pre.length+(mid.length+j))
  have hs : OrderedSteps a (clockSteps pre qc ++
      (clockSteps mid (fun j => qc (pre.length+j)) ++ clockSteps tail qs)) := by
    rw [←nativeExteriorForest_clockSteps_eq]
    exact clockSteps_ordered ho qc
  have hR : BddSmooth 0 ((E.fork E).expect (restWeight n) (restFeature n) qs
      (fun σ => Q (E.atSlot σ.1 s) (E.atSlot σ.2 s))) :=
    (E.fork E).nativeAnchor_expect_smooth (restWeight_pos n) (restFeature n)
      ho.suffix_end.suffix_end qs _ 0
  unfold nativeTwinPrefixDisorderRootLaw nativeTwinPrefixRootLaw
  rw [integral_twinPrefixRootLaw_B_test (restWeight_pos n) (restFeature n) _ _ _ hs
    _ _ _ hR]
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
  rw [hl,levelPairMean_prefix]
  congr 1
  funext z
  exact native_fork_same_slot_expect_eq_root_pair n E ho.suffix_end.suffix_end s qs Q z

theorem native_common_star_pair_marginal (n : ℕ)
    (pre mid tail : List PositiveMass) {a : ℝ}
    (ho : MassOrdered a (pre ++ (mid ++ tail)))
    (E : ClockTree (Spin n) tail) (s : E.Slot)
    (v : RestCoordinate n → ℝ) (q : ℕ → RestCoordinate n → ℝ)
    (Q : Spin n → Spin n → ℝ) (x : RestCoordinate n → ℝ) :
    (∫ z,(E.fork E).expect (restWeight n) (restFeature n)
      (fun j => cumulativeIncrements (q 0) (fun k => q (k+1))
        (pre.length+(mid.length+j)))
      (fun σ => Q (E.atSlot σ.1 s) (E.atSlot σ.2 s)) (exteriorForestStarRoot z)
      ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail v q x) =
    (ClockTree.pairClock (pre ++ (mid ++ tail)) (pre.length+mid.length)).disorderExpect
      (restWeight n) (restFeature n) v q
      (fun σ => Q (ClockTree.pairSpin _ _ σ).1 (ClockTree.pairSpin _ _ σ).2) x := by
  let qc := cumulativeIncrements (q 0) (fun k => q (k+1))
  let qs := fun j => qc (pre.length+(mid.length+j))
  have hs : OrderedSteps a (clockSteps pre qc ++
      (clockSteps mid (fun j => qc (pre.length+j)) ++ clockSteps tail qs)) := by
    rw [←nativeExteriorForest_clockSteps_eq]
    exact clockSteps_ordered ho qc
  have hR : BddSmooth 0 ((E.fork E).expect (restWeight n) (restFeature n) qs
      (fun σ => Q (E.atSlot σ.1 s) (E.atSlot σ.2 s))) :=
    (E.fork E).nativeAnchor_expect_smooth (restWeight_pos n) (restFeature n)
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
  rw [hl,levelPairMean_prefix]
  congr 1
  funext z
  exact native_fork_same_slot_expect_eq_root_pair n E ho.suffix_end.suffix_end s qs Q z

theorem native_fresh_anchor_hweight_eighth_eq_one (n : ℕ)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (q : ℕ → RestCoordinate n → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsProbabilityMeasure μ]
    (x : P → RestCoordinate n → ℝ) :
    (∫ z,E.expect (restWeight n) (restFeature n) q (fun _ => |(1:ℝ)|^8) (x z) ∂μ)=1 := by
  have he : ∀z,E.expect (restWeight n) (restFeature n) q (fun _ => |(1:ℝ)|^8) (x z)=1 := by
    intro z
    simpa only [abs_one,one_pow,ClockTree.expect,mul_one] using
      (E.weight_probability (restWeight_pos n) (restFeature n) ho q (x z)).2
  simp_rw [he]
  simp

theorem physical_exterior_fourth_eq_native_original_root (n : ℕ) (hn : 0 < n)
    {as : List PositiveMass} (E : ClockTree (Spin n) as) {a : ℝ}
    (ho : MassOrdered a as) (s : E.Slot) (q : ℕ → RestCoordinate n → ℝ≥0)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → RestCoordinate n → ℝ) (hx : Measurable x) :
    physicalOverlapMoment n 2 (clockSteps as (fun j => restFiniteVariance n (q j))) μ
      (fun z => restFiniteState n (x z)) ((restFiniteState_measurable n).comp hx) 0 =
    ∫ z,(E.fork E).expect (restWeight n) (restFeature n) q
      (fun σ => |orderedOverlap n (E.atSlot σ.1 s) (E.atSlot σ.2 s)|^4) (x z) ∂μ := by
  rw [physicalOverlapMoment_eq_root_pair n 2 _ (clockSteps_ordered ho _)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro z
  dsimp only
  rw [restFinite_clockTree_expect n hn]
  have H := (E.fork E).expect_pairAtSlot (uniformWeight_pos n) (finiteFeature n) ho
    (fun j => restFiniteVariance n (q j)) (Sum.inl s) (Sum.inr s)
    (by exact Sum.inl_ne_inr) (fun σ τ => |orderedOverlap n σ τ|^4) (restFiniteState n (x z))
  simp only [ClockTree.atSlot,ClockTree.splitIndex,Sum.elim_inl,Sum.elim_inr] at H
  rw [H,ClockTree.pairMean_eq_levelPairMean (uniformWeight_pos n) (finiteFeature n) as ho]

end OAI.SKFluctuations.Cavity
