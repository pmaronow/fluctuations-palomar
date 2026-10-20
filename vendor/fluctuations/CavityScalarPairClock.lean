module

public import ScalarFinitePairBridge
public import SKFluctuationsOAI.Probability.SKFluctuations.PhysicalPinnedWindow
public import CavityAttachedTree
public import CavityFiniteProfileClipping

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def scalarBoundaryClocks : List PositiveMass → (ℕ → ℝ) → List HeatClock
  | [], _ => []
  | a :: as, q => ⟨a.val, a.property, Real.toNNReal (q 1 - q 0)⟩ ::
      scalarBoundaryClocks as (fun j => q (j + 1))

theorem scalarBoundaryClocks_heatSteps (as : List PositiveMass) (q : ℕ → ℝ) :
    heatSteps (ι := Fin 1) (scalarBoundaryClocks as q) =
      diagonalBoundarySteps as (fun _ => q 0) (fun j _ => q (j + 1)) := by
  induction as generalizing q with
  | nil => rfl
  | cons a as ih =>
    simp only [scalarBoundaryClocks, heatSteps, List.map_cons, diagonalBoundarySteps]
    congr 1
    simpa only [heatSteps, Nat.zero_add, Nat.add_assoc] using ih (fun j => q (j + 1))

theorem scalarBoundaryClocks_duration (as : List PositiveMass) (q : ℕ → ℝ)
    (hq : Monotone q) :
    (scheduleDuration (scalarBoundaryClocks as q) : ℝ) = q as.length - q 0 := by
  induction as generalizing q with
  | nil => simp [scalarBoundaryClocks, scheduleDuration]
  | cons a as ih =>
    have hshift : Monotone (fun j => q (j + 1)) := hq.comp (monotone_id.add_const 1)
    simp only [scalarBoundaryClocks, scheduleDuration, NNReal.coe_add, List.length_cons]
    rw [Real.coe_toNNReal _ (sub_nonneg.mpr (hq (by omega : 0 ≤ 1))), ih _ hshift]
    ring

theorem scalarBoundaryClocks_append (as bs : List PositiveMass) (q : ℕ → ℝ) :
    scalarBoundaryClocks (as ++ bs) q = scalarBoundaryClocks as q ++
      scalarBoundaryClocks bs (fun j => q (as.length + j)) := by
  induction as generalizing q with
  | nil => simp [scalarBoundaryClocks]
  | cons a as ih =>
    simp only [List.cons_append, scalarBoundaryClocks, ih, List.length_cons]
    congr 2
    congr 1
    funext j
    congr 1
    omega

theorem scalarBoundaryClocks_ordered {as : List PositiveMass} {a : ℝ}
    (ho : MassOrdered a as) (q : ℕ → ℝ) :
    OrderedSteps a (heatSteps (ι := Fin 1) (scalarBoundaryClocks as q)) := by
  rw [scalarBoundaryClocks_heatSteps]
  rw [← clockSteps_cumulative]
  exact clockSteps_ordered ho _

theorem actual_scalar_pairClock_bounds (as : List PositiveMass)
    (ho : MassOrdered 0 as) (q : ℕ → ℝ) (hq : Monotone q) (hq0 : q 0 = 0)
    (j : ℕ) (hj : j ≤ as.length) :
    0 ≤ (ClockTree.pairClock (S := Bool) as j).disorderExpect
      (fun _ => (1/2 : ℝ)) scalarFeature (fun _ => 0) (fun j _ => q j)
      (fun σ => scalarFeature (ClockTree.pairSpin as j σ).1 (fun _ => 1) *
        scalarFeature (ClockTree.pairSpin as j σ).2 (fun _ => 1)) 0 ∧
    (ClockTree.pairClock (S := Bool) as j).disorderExpect
      (fun _ => (1/2 : ℝ)) scalarFeature (fun _ => 0) (fun j _ => q j)
      (fun σ => scalarFeature (ClockTree.pairSpin as j σ).1 (fun _ => 1) *
        scalarFeature (ClockTree.pairSpin as j σ).2 (fun _ => 1)) 0 ≤ q j := by
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
  have hd : (scheduleDuration pre : ℝ) = q j := by
    dsimp only [pre]
    rw [scalarBoundaryClocks_duration _ q hq, List.length_take, Nat.min_eq_left hj,
      hq0, sub_zero]
  rw [he]
  simpa only [hd] using finite_scalar_pair_bounds pre post hopen

theorem actual_scalar_distinct_pair_bounds {as : List PositiveMass}
    (T : ClockTree Bool as) (ho : MassOrdered 0 as) (q : ℕ → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (s t : T.Slot) (hst : s ≠ t) :
    0 ≤ T.disorderExpect (fun _ => (1/2 : ℝ)) scalarFeature
      (fun _ => 0) (fun j _ => q j)
      (fun σ => scalarFeature (T.atSlot σ s) (fun _ => 1) *
        scalarFeature (T.atSlot σ t) (fun _ => 1)) 0 ∧
    T.disorderExpect (fun _ => (1/2 : ℝ)) scalarFeature
      (fun _ => 0) (fun j _ => q j)
      (fun σ => scalarFeature (T.atSlot σ s) (fun _ => 1) *
        scalarFeature (T.atSlot σ t) (fun _ => 1)) 0 ≤ q (T.splitIndex s t) := by
  have he := T.disorderExpect_pairAtSlot_actual
    (w := fun _ : Bool => (1/2 : ℝ)) (by intro σ; norm_num) scalarFeature ho
    (fun _ => 0) (fun j _ => q j) 0 s t hst
    (fun σ τ => scalarFeature σ (fun _ => 1) * scalarFeature τ (fun _ => 1))
  rw [he]
  exact actual_scalar_pairClock_bounds as ho q hq hq0 _ (T.splitIndex_le_clockLength s t)

theorem actual_scalar_distinct_pair_abs_le {as : List PositiveMass}
    (T : ClockTree Bool as) (ho : MassOrdered 0 as) (q : ℕ → ℝ)
    (hq : Monotone q) (hq0 : q 0 = 0) (s t : T.Slot) (hst : s ≠ t)
    {C v : ℝ} (hclock : q (T.splitIndex s t) ≤ C * v) :
    |T.disorderExpect (fun _ => (1/2 : ℝ)) scalarFeature
      (fun _ => 0) (fun j _ => q j)
      (fun σ => scalarFeature (T.atSlot σ s) (fun _ => 1) *
        scalarFeature (T.atSlot σ t) (fun _ => 1)) 0| ≤ C * v := by
  have hg := actual_scalar_distinct_pair_bounds T ho q hq hq0 s t hst
  rw [abs_of_nonneg hg.1]
  exact hg.2.trans hclock

end OAI.SKFluctuations.LaplaceWindowFormalization
