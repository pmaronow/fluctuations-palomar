module

public import ActualMacroMinimum

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem exists_actual_macro_optimizer {η Q W : ℝ}
    (hη : 0 < η) (hη1 : η < 1) (hQ : 1 < Q)
    (n : ℕ) (hn : 0 < n) (b h w : ℝ → ℝ) (hW : 0 ≤ W)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hw : MonotoneOn w (Icc (0 : ℝ) 1)) (hwm : Measurable w)
    (hwp : ∀ u ∈ Icc (0 : ℝ) 1, 0 < w u)
    (hwb : ∀ u ∈ Icc (0 : ℝ) 1, w u ≤ W)
    (hbn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ b u)
    (hhn : ∀ u ∈ Icc (0 : ℝ) 1, 0 ≤ h u) :
    ∃ α : MacroInverseClass η Q,
      (∀ β : MacroInverseClass η Q,
        macroInverseObjective hη hQ n b h w α ≤ macroInverseObjective hη hQ n b h w β) ∧
      (let q := macroInverseQuantile hη hQ α
       let S := orderedPathS n (fun u => (b u).toNNReal)
         (fun u => (h u + w u * q u).toNNReal)
       (∫ u in (0 : ℝ)..1, (S u - q u)^2) ≤ η + (1 / Q)^2) := by
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  obtain ⟨α, hα⟩ := macroInverseObjective_minimum hη hη1 hQ n hn b h w hW hb hh hw
    (fun u hu => ⟨(hwp u hu).le, hwb u hu⟩) (hbn 0 h00) (hhn 0 h00)
  exact ⟨α, hα, macro_inverse_minimum_mass_defect hη hη1 hQ n hn b h w hW hb hh hw hwm
    hwp hwb hbn hhn α hα⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
