module

public import ComparisonSignedCavityScalarResponse
public import ComparisonSignedCavityScalarNativeRemainder
public import ComparisonSignedCavityScalarTerminalPadding

@[expose] public section

noncomputable section
set_option maxHeartbeats 4000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_scalar_pairClock_eq_stepPairMean
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (q : ℕ → ℝ) (hq0 : q 0 = 0) (j : ℕ) (hj : j ≤ as.length) :
    nativeOriginalScalarPairMean as q j =
      stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
        (heatSteps (scalarBoundaryClocks (as.take j) q))
        (heatSteps (scalarBoundaryClocks (as.drop j) (fun k => q (j+k))))
        (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 := by
  let cs := scalarBoundaryClocks as q
  let pre := scalarBoundaryClocks (as.take j) q
  let post := scalarBoundaryClocks (as.drop j) (fun k => q (j + k))
  have hsplit : cs = pre ++ post := by
    dsimp only [cs, pre, post]
    have h := scalarBoundaryClocks_append (as.take j) (as.drop j) q
    simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left hj] using h
  have hopen : OrderedSteps 0 (heatSteps (ι := Fin 1) (pre ++ post)) := by
    rw [← hsplit]
    exact scalarBoundaryClocks_ordered ho q
  have hpost : OrderedSteps 0 (heatSteps (ι := Fin 1) post) := by
    apply OrderedSteps.suffix (heatSteps (ι := Fin 1) pre) (heatSteps post)
    simpa only [heatSteps, List.map_append] using hopen
  have hlen : (heatSteps (ι := Fin 1) pre).length = j := by
    dsimp only [pre]
    have h (bs : List PositiveMass) (r : ℕ → ℝ) :
        (scalarBoundaryClocks bs r).length = bs.length := by
      induction bs generalizing r with
      | nil => rfl
      | cons b bs ih => simp [scalarBoundaryClocks, ih]
    simp only [heatSteps, List.length_map, h, List.length_take, Nat.min_eq_left hj]
  have he : (ClockTree.pairClock (S := Bool) as j).disorderExpect
      (fun _ => (1/2 : ℝ)) scalarFeature (fun _ => 0) (fun j _ => q j)
      (fun σ => scalarFeature (ClockTree.pairSpin as j σ).1 (fun _ => 1) *
        scalarFeature (ClockTree.pairSpin as j σ).2 (fun _ => 1)) 0 =
      stepPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
        (heatSteps pre) (heatSteps post)
        (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1)) 0 := by
    rw [ClockTree.pairDisorder_eq_rootLevelPairMean
      (w := fun _ : Bool => (1/2 : ℝ)) (by intro σ; norm_num) scalarFeature as ho
      (fun j _ => q j) j
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1))]
    simp only [hq0, Real.toNNReal_zero, rootLevelPairMean, isotropicGaussian_zero,
      zeroContinuation, integral_dirac, add_zero]
    have hcs := scalarBoundaryClocks_heatSteps as q
    rw [hq0] at hcs
    rw [← hcs]
    change levelPairMean (fun _ : Bool => (1/2 : ℝ)) scalarFeature
      (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1))
      (heatSteps cs) j 0 = _
    rw [hsplit]
    simp only [heatSteps, List.map_append]
    rw [← hlen]
    exact (congrFun (stepPairMean_eq_levelPairMean (by intro σ; norm_num)
      scalarFeature _ (heatSteps pre) (heatSteps post) hpost) 0).symm
  exact he

theorem native_scalar_pairClock_eq_fixed_schedule_response {T : ℝ} (hT : 0 < T)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (q : ℕ → ℝ) (hq : Monotone q) (hq0 : q 0 = 0) (htotal : q as.length ≤ T)
    (j : ℕ) (hj : j ≤ as.length) :
    nativeOriginalScalarPairMean as q j =
      scalarCovarianceResponse hT
        (actualScalarScheduleMass hT (scalarBoundaryClocks as q) (by
          rw [scalarBoundaryClocks_duration as q hq, hq0, sub_zero]
          exact htotal)) (q j) := by
  rw [native_scalar_pairClock_eq_stepPairMean as ho q hq0 j hj]
  let pre := scalarBoundaryClocks (as.take j) q
  let post := scalarBoundaryClocks (as.drop j) (fun k => q (j+k))
  have hsplit : scalarBoundaryClocks as q = pre ++ post := by
    dsimp only [pre,post]
    simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left hj] using
      scalarBoundaryClocks_append (as.take j) (as.drop j) q
  have hopen : OrderedSteps 0 (heatSteps (ι := Fin 1) (pre ++ post)) := by
    rw [← hsplit]
    exact scalarBoundaryClocks_ordered ho q
  have ht : (scheduleDuration (pre ++ post) : ℝ) ≤ T := by
    rw [← hsplit, scalarBoundaryClocks_duration as q hq, hq0, sub_zero]
    exact htotal
  have hd : (scheduleDuration pre : ℝ) = q j := by
    dsimp only [pre]
    rw [scalarBoundaryClocks_duration _ q hq, List.length_take,
      Nat.min_eq_left hj, hq0, sub_zero]
  have he := finite_scalar_pair_eq_actual_plantedEnergy_fixed_horizon hT pre post ht hopen
  change stepPairMean _ _ (heatSteps pre) (heatSteps post) _ 0 = _
  rw [he, hd]
  unfold scalarCovarianceResponse
  simp only [← hsplit]

end OAI.SKFluctuations.Cavity
