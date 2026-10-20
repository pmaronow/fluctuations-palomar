module

public import ComparisonSignedCavitySecondLowOldDependentPowerPair
public import ComparisonSignedCavityHighMarkedRows

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open scoped BigOperators NNReal
variable {ι S : Type*} [Fintype ι] [Fintype S] [Nonempty S]
set_option maxHeartbeats 30000000

theorem native_second_low_full_clock_field_pair_symm
    {w : S → ℝ} (hw : ∀ σ, 0 < w σ) (φ : S → (ι → ℝ) →L[ℝ] ℝ)
    {as : List PositiveMass} (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ → ι → ℝ≥0) (P : T.Assignment → ℝ) (u v x : ι → ℝ) :
    T.profilePair w φ a q P (fun _ σ τ => φ σ u * φ τ v) x =
      T.profilePair w φ a q P (fun _ σ τ => φ σ v * φ τ u) x := by
  rw [profilePair_realize,profilePair_realize]
  exact ReplicaTree.native_second_low_marked_field_pair_symm hw φ (T.realize q)
    (clockSteps_ordered ho q) (fun σ => P ((T.assignmentEquiv q).symm σ)) u v x

end OAI.SKFluctuations.Hierarchy.ClockTree
