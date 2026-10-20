module

public import ComparisonSignedCavityRestBoundarySchedule
public import ComparisonSignedCavityObservedStarClockTransport
public import ComparisonSignedCavityCanonicalRestMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 7000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem native_original_rest_resampling_eq_physical (n l : ℕ) (hn : 0<n)
    {as : List PositiveMass} (T : ClockTree (Spin n) as) (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (b s e : T.Slot) (hse : s≠e)
    (hlow : T.splitIndex b s=T.splitIndex b e)
    (hgap : T.splitIndex b s<T.splitIndex s e) :
    T.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|deletedOverlap n (joinSpin (T.atSlot σ b,false)) (joinSpin (T.atSlot σ s,false))-
        deletedOverlap n (joinSpin (T.atSlot σ b,false)) (joinSpin (T.atSlot σ e,false))|^(2*l)) 0=
      ((n:ℝ)/(n+1:ℕ))^(2*l)*originalBoundaryResamplingMoment n l as
        (fun j=>restFiniteRealVariance n (q j)) (T.splitIndex b s) (T.splitIndex s e) := by
  have hv : restFiniteRealVariance n 0=0 := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i <;> simp [restFiniteRealVariance]
  have hx : restFiniteState n 0=0 := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i <;> simp [restFiniteState]
  rw [restFinite_clockTree_disorderExpect n hn,hv,hx,
    original_boundary_resampling_eq_full_tree n l T ho _ b s e hse hlow hgap]
  unfold ClockTree.disorderExpect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [deleted_overlap_join_eq_scaled,←mul_sub,abs_mul,mul_pow,
    abs_of_nonneg (show 0≤(n:ℝ)/(n+1:ℕ) by positivity)]
  ring

theorem native_original_full_rest_resampling_eq_physical (n l : ℕ) (hn : 0<n)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (q : ℕ→RestCoordinate n→ℝ) (b s e : T.Slot) (hse : s≠e)
    (hlow : T.splitIndex b s=T.splitIndex b e)
    (hgap : T.splitIndex b s<T.splitIndex s e) :
    T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (fun σ=>|deletedOverlap n
        (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot b),false))
        (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot s),false))-
        deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot b),false))
        (joinSpin (T.cavityLeft.atSlot σ (T.cavityLeftSlot e),false))|^(2*l)) 0=
      ((n:ℝ)/(n+1:ℕ))^(2*l)*originalBoundaryResamplingMoment n l as
        (fun j=>restFiniteRealVariance n (q j)) (T.splitIndex b s) (T.splitIndex s e) := by
  have hse' : T.cavityLeftSlot s≠T.cavityLeftSlot e:=fun H=>hse (T.cavityLeftSlot.injective H)
  simpa only [ClockTree.cavityLeft_splitIndex] using
    native_original_rest_resampling_eq_physical n l hn T.cavityLeft ho q
      (T.cavityLeftSlot b) (T.cavityLeftSlot s) (T.cavityLeftSlot e) hse'
      (by simpa only [ClockTree.cavityLeft_splitIndex] using hlow)
      (by simpa only [ClockTree.cavityLeft_splitIndex] using hgap)

end OAI.SKFluctuations.Cavity
