module

public import ComparisonSignedCavityActualOriginalGPairRestoration
public import ComparisonSignedCavityActualOriginalLongitudinalGhost

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem native_original_high_pairing_eq_connected_response (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length) :
    nativeOriginalHighPairing n v q x U K b C T P a c=
      nativeOriginalConnectedHighResponse n v q x U K b C T
        (fun σ=>P (T.cavityAssignment σ).1) a c := by
  have H:=native_original_G_rows_eq_connected_response n v q x U K b C T ho
    (fun σ=>P (T.cavityAssignment σ).1) a c hU
  unfold nativeOriginalHighPairing
  simpa only [MarkedPlacement.restRestrict_actual] using H

theorem native_original_high_pairing_marked_preserves (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a c : T.Slot)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (hq : ∀i,Monotone (fun j=>q j i)) (hq0 : ∀i,v i ≤ q 0 i)
    (hK : ∀j,0 ≤ K j) (hKm : Monotone K) (hU : U ≤ as.length) :
    nativeOriginalHighPairing n v q x U K b C p.tree
      (fun σ=>P (p.restRestrict σ)) (p.embed a) (p.embed c)=
      nativeOriginalHighPairing n v q x U K b C T P a c := by
  rw [native_original_high_pairing_eq_connected_response n v q x U K b C p.tree ho _ _ _ hU,
    native_original_high_pairing_eq_connected_response n v q x U K b C T ho P a c hU]
  simp_rw [←p.restRestrict_actual]
  exact native_original_connected_high_marked_preserves n v q x U K b C T ho
    (fun σ=>P (T.cavityAssignment σ).1) a c p hp hq hq0 hK hKm

theorem native_original_longitudinal_eq_pair_rows (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K b C : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (_ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ) (a : T.Slot) :
    nativeOriginalLongitudinalPairing n v q x U K b C T
      (fun σ=>P (T.cavityAssignment σ).1) a=
      ((T.markedAttach 0).map (fun p=>p.coeff*
        nativeOriginalHighPairing n v q x U K b C p.tree
          (fun σ=>P (p.restRestrict σ)) (p.embed a) p.mark)).sum := by
  unfold nativeOriginalLongitudinalPairing nativeOriginalHighPairing
  simp_rw [MarkedPlacement.restRestrict_actual]

end OAI.SKFluctuations.Cavity
