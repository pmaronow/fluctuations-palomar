module

public import PhysicalCapEnergyUpper

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
local instance (n : ℕ) : DecidableEq (FeatureIndex (n+1)) := fun _ _=>Classical.propDecidable _
set_option maxHeartbeats 1000000

theorem splitClockSteps_nested {ι : Type*} [Fintype ι]
    (L : List (GaussianStep ι)) {u v : ℝ} (huv : u ≤ v) :
    (splitClockSteps v L).1=(splitClockSteps u L).1++
      (splitClockSteps v (splitClockSteps u L).2).1 ∧
    (splitClockSteps v L).2=(splitClockSteps v (splitClockSteps u L).2).2 := by
  induction L with
  | nil=>simp [splitClockSteps]
  | cons s L ih=>
    simp only [splitClockSteps]
    by_cases hsu : s.1 ≤ u
    · have hsv : s.1 ≤ v := hsu.trans huv
      simp only [ite_eq_left hsu,ite_eq_left hsv,List.cons_append,ih.1,ih.2,and_self]
    · simp only [ite_eq_right hsu,List.nil_append]
      constructor <;> rfl

theorem physicalCapVarianceSum_append {n : ℕ}
    (A B : List (GaussianStep (FeatureIndex n))) :
    physicalCapVarianceSum (A++B)=physicalCapVarianceSum A+physicalCapVarianceSum B := by
  induction A with
  | nil=>simp [physicalCapVarianceSum]
  | cons st A ih=>cases st;simp [physicalCapVarianceSum,ih,add_assoc]

theorem physicalCapVarianceSum_eq_clock_total (n : ℕ)
    (L : List (GaussianStep (FeatureIndex n))) (q₀ : FeatureIndex n→ℝ) :
    physicalCapVarianceSum L=∑ k,(stepClockValues q₀ L L.length k-q₀ k) := by
  induction L generalizing q₀ with
  | nil=>simp [physicalCapVarianceSum,stepClockValues]
  | cons st L ih=>
    rcases st with ⟨m,q⟩
    simp only [physicalCapVarianceSum,List.length_cons,stepClockValues]
    rw [ih (fun k=>q₀ k+(q k:ℝ)),←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring

theorem physicalFiniteOverlap_increment_le_clock (n d : ℕ) (hn : 0 < n)
    (e : Fin (d+1) ≃ FeatureIndex n) (q₀ : FeatureIndex n→ℝ≥0)
    (L : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 L)
    {u v : ℝ} (huv : u ≤ v) :
    stepPairMoment (uniformWeight n) (finiteFeature n) q₀ L ha.mem_pos (orderedOverlap n) v-
      stepPairMoment (uniformWeight n) (finiteFeature n) q₀ L ha.mem_pos (orderedOverlap n) u ≤
    physicalOverlapEnergyConstant n*∑ k,
      (stepClockFunction (fun k=>(q₀ k:ℝ)) L v k-
        stepClockFunction (fun k=>(q₀ k:ℝ)) L u k) := by
  let A := (splitClockSteps u L).1
  let B := (splitClockSteps v (splitClockSteps u L).2).1
  let C := (splitClockSteps v L).2
  have hsplit := splitClockSteps_nested L huv
  have hav : (splitClockSteps v L).1=A++B := hsplit.1
  have hall : (A++B)++C=L := by rw [←hav];exact splitClockSteps_append v L
  have hfull : OrderedSteps 0 ((A++B)++C) := hall.symm ▸ ha
  have hb := physicalCapEnergy_band_rooted_le_variance n d e q₀ A B C hfull
  rw [←physicalSecondMoment_eq_stepPairMoment n hn L ha q₀ v,
    ←physicalSecondMoment_eq_stepPairMoment n hn L ha q₀ u]
  change physicalPathSecondMoment n L q₀ (splitClockSteps v L).1.length-
    physicalPathSecondMoment n L q₀ A.length ≤ _
  have hvar : physicalCapVarianceSum B=∑ k,
      (stepClockFunction (fun k=>(q₀ k:ℝ)) L v k-
        stepClockFunction (fun k=>(q₀ k:ℝ)) L u k) := by
    have hh := physicalCapVarianceSum_append A B
    rw [←hav,physicalCapVarianceSum_eq_clock_total n _ (fun k=>(q₀ k:ℝ)),
      physicalCapVarianceSum_eq_clock_total n A (fun k=>(q₀ k:ℝ))] at hh
    simp_rw [stepClockFunction_split (fun k=>(q₀ k:ℝ)) v L ha,
      stepClockFunction_split (fun k=>(q₀ k:ℝ)) u L ha]
    rw [Finset.sum_sub_distrib]
    have he : (∑ k,stepClockValues (fun k=>(q₀ k:ℝ)) (splitClockSteps v L).1 (splitClockSteps v L).1.length k)-
        (∑ k,stepClockValues (fun k=>(q₀ k:ℝ)) A A.length k)=physicalCapVarianceSum B := by
      simp only [Finset.sum_sub_distrib] at hh
      linarith
    exact he.symm
  rw [hvar,hall,←hav] at hb
  exact hb

end OAI.SKFluctuations.LaplaceWindowFormalization
