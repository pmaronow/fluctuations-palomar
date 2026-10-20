module

public import ComparisonSignedCavitySecondLowFullClockPairSymmetry
public import CavityRetainedFrozenExpansion

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators NNReal
set_option maxHeartbeats 30000000

def nativeSecondLowActualFieldDirection (n U : ℕ) (b h : ℕ → ℝ)
    (j : ℕ) (σ : Spin n) : FullCoordinate n → ℝ :=
  if j < U then Sum.elim (fun _ => 0)
    (Sum.elim (fun i => b j * spinValue (σ i) / Real.sqrt (n+1 : ℕ)) (fun _ => h j))
  else 0

theorem fullFeature_native_second_low_actual_field_direction
    (n U : ℕ) (b h : ℕ → ℝ) (j : ℕ) (σ : Spin n) (τ : Spin n × Bool) :
    fullFeature n τ (nativeSecondLowActualFieldDirection n U b h j σ) =
      spinValue τ.2 * restLowKernel n U b h j σ τ.1 := by
  by_cases Hj : j < U
  · simp only [nativeSecondLowActualFieldDirection,Hj,ite_true,fullFeature_apply,
      Sum.elim_inl,Sum.elim_inr]
    rw [show (fun _ : RestCoordinate n => (0:ℝ)) = 0 from rfl,
      show (fun _ : Fin 1 => (0:ℝ)) = 0 from rfl,map_zero,map_zero,zero_add,zero_add]
    simp only [dormantFeature_apply,Fintype.sum_sum_type,dormantCoefficient,
      Sum.elim_inl,Sum.elim_inr,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      restLowKernel,Hj,ite_true]
    have hs : (Real.sqrt (n+1 : ℕ))^2 = (n+1 : ℕ) := Real.sq_sqrt (by positivity)
    have he (i : Fin n) :
        spinValue τ.2 * spinValue (τ.1 i) / Real.sqrt (n+1 : ℕ) *
          (b j * spinValue (σ i) / Real.sqrt (n+1 : ℕ)) =
        (spinValue τ.2 * b j / (n+1 : ℕ)) * (spinValue (σ i) * spinValue (τ.1 i)) := by
      rw [div_mul_div_comm,← pow_two,hs]
      ring
    simp_rw [he]
    rw [←Finset.mul_sum]
    ring
  · simp only [nativeSecondLowActualFieldDirection,Hj,ite_false,map_zero,
      restLowKernel,mul_zero]

theorem native_second_low_actual_full_clock_pair_edge_order_symm
    (n U : ℕ) (b h : ℕ → ℝ) (i j : ℕ) (σ τ : Spin n)
    {as : List PositiveMass} (T : ClockTree (Spin n × Bool) as) {a : ℝ}
    (ho : MassOrdered a as) (q : ℕ → FullCoordinate n → ℝ≥0)
    (P : T.Assignment → ℝ) (x : FullCoordinate n → ℝ) :
    T.profilePair (fullWeight n) (fullFeature n) a q P
      (fun _ s t => (spinValue s.2 * restLowKernel n U b h i σ s.1) *
        (spinValue t.2 * restLowKernel n U b h j τ t.1)) x =
    T.profilePair (fullWeight n) (fullFeature n) a q P
      (fun _ s t => (spinValue s.2 * restLowKernel n U b h j τ s.1) *
        (spinValue t.2 * restLowKernel n U b h i σ t.1)) x := by
  simpa only [fullFeature_native_second_low_actual_field_direction] using
    native_second_low_full_clock_field_pair_symm (fullWeight_pos n) (fullFeature n) T ho q P
      (nativeSecondLowActualFieldDirection n U b h i σ)
      (nativeSecondLowActualFieldDirection n U b h j τ) x

end OAI.SKFluctuations.Cavity
