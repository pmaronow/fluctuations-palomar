module

public import CavityNativeSignedWeightedIncoming

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_centered_projected_power_le_fresh (n m : ℕ) (as : List PositiveMass)
    {a : ℝ} (ho : MassOrdered a as) (q : ℕ → RestCoordinate n → ℝ≥0)
    (x : RestCoordinate n → ℝ) (center : ℝ) (σ : Spin n) :
    |nativeCenteredProjectedDeletedOverlap n as q x center σ|^m≤
    (ClockTree.single (S := Spin n) as).expect (restWeight n) (restFeature n) q
      (fun τ=>|deletedOverlap n (joinSpin (σ,false))
        (joinSpin (ClockTree.singleEquiv (S := Spin n) as τ,false))-center|^m) x := by
  let T := ClockTree.single (S := Spin n) as
  let w := fun τ=>T.weight (restWeight n) (restFeature n) q τ x
  let F := fun τ=>deletedOverlap n (joinSpin (σ,false))
    (joinSpin (ClockTree.singleEquiv (S := Spin n) as τ,false))-center
  have hw := T.weight_probability (restWeight_pos n) (restFeature n) ho q x
  have hJ:=finite_weighted_mean_abs_pow_le w F hw.1 hw.2 m
  have hmean : (∑ τ, w τ*F τ)=nativeCenteredProjectedDeletedOverlap n as q x center σ := by
    dsimp only [F]
    simp only [mul_sub,Finset.sum_sub_distrib]
    unfold nativeCenteredProjectedDeletedOverlap nativeProjectedDeletedOverlap ClockTree.expect
    rw [←Finset.sum_mul,hw.2,one_mul]
  rw [hmean] at hJ
  exact hJ

theorem native_projected_target_power_moment_le (n m : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as) (s : T.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) (center : ℝ) :
    T.expect (restWeight n) (restFeature n) q
      (fun σ=>|nativeCenteredProjectedDeletedOverlap n as q x center (T.atSlot σ s)|^m) x≤
    ClockTree.pairMean (restWeight n) (restFeature n) as q 0
      (fun σ τ=>|deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-center|^m) x := by
  have hp : T.expect (restWeight n) (restFeature n) q
      (fun σ=>|nativeCenteredProjectedDeletedOverlap n as q x center (T.atSlot σ s)|^m) x≤
    T.expect (restWeight n) (restFeature n) q
      (fun σ=>ClockTree.singleMean (restWeight n) (restFeature n) as q
        (fun τ=>|deletedOverlap n (joinSpin (T.atSlot σ s,false))
          (joinSpin (τ,false))-center|^m) x) x := by
    unfold ClockTree.expect
    apply Finset.sum_le_sum
    intro σ hσ
    exact mul_le_mul_of_nonneg_left
      (native_centered_projected_power_le_fresh n m as ho q x center (T.atSlot σ s))
      ((T.weight_probability (restWeight_pos n) (restFeature n) ho q x).1 σ)
  apply hp.trans_eq
  simpa only [ClockTree.pairMean] using T.expect_atSlot (restWeight_pos n) (restFeature n) ho q s
    (fun σ=>ClockTree.singleMean (restWeight n) (restFeature n) as q
      (fun τ=>|deletedOverlap n (joinSpin (σ,false)) (joinSpin (τ,false))-center|^m) x) x

end OAI.SKFluctuations.Cavity
