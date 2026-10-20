module

public import ComparisonSignedCavityActualOriginalHighMarginal
public import ComparisonSignedCavityActualOriginalObservedHigh
public import ComparisonSignedCavityFreshGraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree MeasureTheory ProbabilityTheory Set LaplaceWindowFormalization
open scoped BigOperators NNReal
set_option maxHeartbeats 16000000

theorem native_original_longitudinal_eq_observed_sub
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a : T.Slot)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU0 : 0 < U) (hU : U ≤ as.length) :
    nativeOriginalLongitudinalPairing n v q x U K b C T P a=
      nativeOriginalObservedHigh n v q x U K b C T P a-
      (scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0*
        nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] T P [] := by
  rw [native_original_longitudinal_eq_connected_rows n v q x U K b C T ho P a hU]
  unfold nativeOriginalConnectedHighResponse
  have H : (T.markedAttach 0).map (fun p=>p.coeff*
      (nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] p.tree
        (fun σ=>P (p.restrict σ)) [p.embed a,p.mark]-
       fullScalarCutGamma p.tree U K (p.embed a) p.mark*
       nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] p.tree
        (fun σ=>P (p.restrict σ)) []))=
    (T.markedAttach 0).map (fun p=>p.coeff*
      nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] p.tree
        (fun σ=>P (p.restrict σ)) [p.embed a,p.mark]-
      (p.coeff*fullScalarCutGamma p.tree U K (p.embed a) p.mark)*
        nativeOriginalSignedJets n v q x U K [nativeOriginalHighKernel n U b C] T P []) := by
    apply List.map_congr_left
    intro p hp
    rw [native_original_high_marked_preserves n v q x U K b C T ho P p hp hq hq0 hK hKm]
    ring
  rw [H,sum_map_sub_explicit,List.sum_map_mul_right,
    native_full_gamma_row_hessian n T ho 0 ho U hU0 K a]
  rfl

theorem native_original_longitudinal_marked_preserves
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU0 : 0 < U) (hU : U ≤ as.length) :
    nativeOriginalLongitudinalPairing n v q x U K b C p.tree
      (fun σ=>P (p.restrict σ)) (p.embed a)=
    nativeOriginalLongitudinalPairing n v q x U K b C T P a := by
  rw [native_original_longitudinal_eq_observed_sub n v q x U K b C p.tree ho _ _
      hq hq0 hK hKm hU0 hU,
    native_original_longitudinal_eq_observed_sub n v q x U K b C T ho _ _
      hq hq0 hK hKm hU0 hU,
    native_original_observed_high_marked_preserves n v q x U K b C T ho hq hq0 hK hKm P a p hp,
    native_original_high_marked_preserves n v q x U K b C T ho P p hp hq hq0 hK hKm]

theorem native_original_longitudinal_fresh_star_preserves
    (n : ℕ) (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ)
    (x : FullCoordinate n→ℝ) (U : ℕ) (K b C : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a trunk : T.Slot) (star : ℕ)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU0 : 0 < U) (hU : U ≤ as.length) :
    nativeOriginalLongitudinalPairing n v q x U K b C (nativeFreshAtSlot T 0 trunk star).tree
      (fun σ=>P ((nativeFreshAtSlot T 0 trunk star).restrict σ))
      ((nativeFreshAtSlot T 0 trunk star).embed a)=
    nativeOriginalLongitudinalPairing n v q x U K b C T P a :=
  native_original_longitudinal_marked_preserves n v q x U K b C T ho P a
    (nativeFreshAtSlot T 0 trunk star) (nativeFreshAtSlot_mem T 0 trunk star)
    hq hq0 hK hKm hU0 hU

end OAI.SKFluctuations.Cavity
