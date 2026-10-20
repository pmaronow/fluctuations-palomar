module

public import WallSampledFieldGap

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy
open scoped NNReal

theorem sampleMassDurations_append (a : ℝ) (before after : List PositiveMass) :
    sampleMassDurations a (before++after) = sampleMassDurations a before ++
      sampleMassDurations (partitionEnd a before) after := by
  induction before generalizing a with
  | nil => rfl
  | cons b bs ih => simp only [List.cons_append,sampleMassDurations,partitionEnd,ih]

theorem sampleMassDurations_internal_mesh {a c mesh : ℝ}
    (before band after : List PositiveMass)
    (ha : MassOrdered a (before++band++after))
    (hm : PartitionMesh mesh a (before++band++after))
    (hc : partitionEnd a before = c) :
    ∀ (w:ℝ≥0), w ∈ sampleMassDurations c band → (w:ℝ) ≤ mesh := by
  intro w hw
  apply sampleMassDurations_mesh (before++band++after) ha hm w
  rw [List.append_assoc,sampleMassDurations_append,hc,sampleMassDurations_append]
  exact List.mem_append_right _ (List.mem_append_left _ hw)

end OAI.SKFluctuations.LaplaceWindowFormalization
