module

public import ComparisonSignedCavityRestBoundarySchedule

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped NNReal BigOperators

theorem actual_general_sampled_field_duration_dimension_transport
    (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (bf hf : ℝ→ℝ≥0)
    (hbf : MonotoneOn bf (Icc (0:ℝ) 1)) (hhf : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (j : ℕ) (hj : j ≤ as.length) :
    physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hn⟩))
      ((nativeSampledPhysicalSteps n bf hf as).take j)=
    physicalFieldDuration (fun st=>st.2 (Sum.inl ⟨0,hN⟩))
      ((sampleClockSteps (completedPathClock N bf hf) 0 as).take j) := by
  rw [native_sampled_field_duration_take_eq_completed]
  have Hn:=sampledFieldDuration_index n hn bf hf hbf hhf as ho j hj
  have HN:=sampledFieldDuration_index N hN bf hf hbf hhf as ho j hj
  dsimp only at Hn HN
  rw [physicalCutMass_sampleClockSteps _ _ _ _ hj] at Hn HN
  exact Hn.trans HN.symm

end OAI.SKFluctuations.Cavity
