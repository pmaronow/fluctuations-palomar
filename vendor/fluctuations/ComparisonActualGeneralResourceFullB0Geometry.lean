module

public import ComparisonSignedCavitySecondLowGeneratedFullB0Geometry
public import ComparisonActualGeneralResourceFullB0Readout

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem actual_general_resource_canonical_source_radius_gate
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as} {i star : ℕ}
    (radius : ℝ→ℝ) (P : NativeResourceMonomial i star T)
    (hi : i ≤ star) (hs : star < as.length)
    (bound : ℝ) (Hi : radius (partitionPoint 0 as i) ≤ bound)
    (Hs : radius (partitionPoint 0 as star) ≤ bound) (e : Fin P.factors.length) :
    radius ((nativeActualResourceCanonicalShape P hi hs).sourceLowMass e) ≤ bound := by
  rcases native_actual_resource_canonical_source_mass_initial_or_star P hi hs e with H | H
  · rw [H];exact Hi
  · rw [H];exact Hs

end OAI.SKFluctuations.Cavity
