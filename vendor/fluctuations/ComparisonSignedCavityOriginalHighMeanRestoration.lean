module

public import ComparisonSignedCavityCommonScalarInvariance
public import CavityEndpointLaw
public import CavityPhysicalMixedClock

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem original_deleted_centered_mean_abs_le (n : ℕ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (q : ℕ → FullCoordinate n → ℝ) (s t : T.Slot) (hst : s ≠ t) (center : ℝ) :
    |T.disorderExpect (fullWeight n) (fullFeature n) 0 q
      (fun σ => deletedOverlap n (joinSpin (T.atSlot σ s))
        (joinSpin (T.atSlot σ t))-center) 0| ≤
      1/(n+1:ℕ)+|(ClockTree.pairClock as (T.splitIndex s t)).disorderExpect
        (fullWeight n) (fullFeature n) 0 q
        (fun σ => orderedOverlap (n+1) (joinSpin (ClockTree.pairSpin as (T.splitIndex s t) σ).1)
          (joinSpin (ClockTree.pairSpin as (T.splitIndex s t) σ).2)) 0-center| := by
  let w := fun σ => T.disorderWeight (fullWeight n) (fullFeature n) 0 q σ 0
  let A := fun σ => deletedOverlap n (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))
  let B := fun σ => orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))
  have hw := T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho 0 q 0
  have hdelta : |∑σ,w σ*(A σ-B σ)| ≤ 1/(n+1:ℕ) := by
    calc
      _ ≤ ∑σ,|w σ*(A σ-B σ)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑σ,w σ*(1/(n+1:ℕ)) := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [abs_mul,abs_of_nonneg (hw.1 σ)]
        congr 1
        exact abs_deletedOverlap_sub n _ _
      _ = 1/(n+1:ℕ) := by rw [←Finset.sum_mul,hw.2,one_mul]
  have hpair := T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n)
    ho 0 q 0 s t hst (fun σ τ => orderedOverlap (n+1) (joinSpin σ) (joinSpin τ))
  rw [←hpair]
  change |∑σ,w σ*(A σ-center)| ≤ 1/(n+1:ℕ)+|(∑σ,w σ*B σ)-center|
  have hid : (∑σ,w σ*(A σ-center)) = (∑σ,w σ*(A σ-B σ))+((∑σ,w σ*B σ)-center) := by
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
    rw [hw.2,one_mul]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hdelta (le_refl _))

end OAI.SKFluctuations.Cavity
