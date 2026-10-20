module

public import QuantileLaw
public import ActualMacroOptimizerDefect

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Measure.Subtype.measureSpace

theorem uniformOrderMass_atMost {m : ℝ} (hm : m ∈ Icc (0:ℝ) 1) :
    (uniformOrderMass : Measure ParisiFinite.OrderPoint).real
      {u | (u:ℝ) ≤ m} = m := by
  have himage : ((↑) : ParisiFinite.OrderPoint → ℝ) '' {u | (u:ℝ) ≤ m} = Icc 0 m := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨u.property.1,hu⟩
    · intro hx
      exact ⟨⟨x,hx.1,hx.2.trans hm.2⟩,hx.2,rfl⟩
  change (volume {u : ParisiFinite.OrderPoint | (u:ℝ) ≤ m}).toReal = _
  rw [← volume_image_subtype_coe measurableSet_Icc,himage]
  simp [Real.volume_Icc,Real.toNNReal_of_nonneg hm.1,hm.1]

theorem macroInverseQuantile_spec {η Q : ℝ} (hη : 0 < η) (hQ : 1 < Q)
    (α : MacroInverseClass η Q) {u : ℝ} (hu : u ∈ Icc (0:ℝ) 1) :
    α.val.val (macroInverseQuantile hη hQ α u) = u := by
  unfold macroInverseQuantile inverseMassQuantile
  rw [projIcc_of_mem zero_le_one hu]
  exact constrainedQuantile_spec zero_le_one hη continuousOn_const (fun _ _ => le_rfl)
    (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le α ⟨u,hu⟩

theorem macroInverseProfile_mem {η Q : ℝ} (α : MacroInverseClass η Q) :
    α.val ∈ scalarProfiles := by
  constructor
  · intro r hr
    apply le_antisymm
    · simpa only [α.property.1] using α.val.property.2 hr.le
    · exact (α.val.property.1 r).1
  · intro r hr
    apply le_antisymm
    · exact (α.val.property.1 r).2
    · simpa only [α.property.2.1] using α.val.property.2 hr.le

theorem macroInverseQuantile_cdf_eq {η Q : ℝ} (hη : 0 < η) (hQ : 1 < Q)
    (α : MacroInverseClass η Q) {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    (quantileMassProfile (macroInverseQuantile hη hQ α)
      (fun u _ => macroInverseQuantile_bounds hη hQ α u)).val r = α.val.val r := by
  rw [quantileMassProfile_cdf _ (macroInverseQuantile_monotone hη hQ α)]
  have he : {u : ParisiFinite.OrderPoint | macroInverseQuantile hη hQ α u ≤ r} =
      {u : ParisiFinite.OrderPoint | (u:ℝ) ≤ α.val.val r} := by
    apply Set.ext
    intro u
    change (macroInverseQuantile hη hQ α u ≤ r) ↔ ((u:ℝ) ≤ α.val.val r)
    constructor
    · intro hu
      have hh := α.val.property.2 hu
      rwa [macroInverseQuantile_spec hη hQ α u.property] at hh
    · intro hu
      have hh := macroInverseQuantile_monotone hη hQ α u.property (α.val.property.1 r) hu
      rwa [macroInverseQuantile_inverse hη hQ α r hr] at hh
  rw [he]
  exact uniformOrderMass_atMost (α.val.property.1 r)

theorem macroInverseQuantile_massProfile_eq {η Q : ℝ} (hη : 0 < η) (hQ : 1 < Q)
    (α : MacroInverseClass η Q) :
    quantileMassProfile (macroInverseQuantile hη hQ α)
      (fun u _ => macroInverseQuantile_bounds hη hQ α u) = α.val := by
  apply Subtype.ext
  funext r
  by_cases hr0 : r < 0
  · rw [(quantileMassProfile_mem _ _).1 r hr0,(macroInverseProfile_mem α).1 r hr0]
  · by_cases hr1 : 1 < r
    · rw [(quantileMassProfile_mem _ _).2 r hr1,(macroInverseProfile_mem α).2 r hr1]
    · exact macroInverseQuantile_cdf_eq hη hQ α ⟨not_lt.mp hr0,not_lt.mp hr1⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
