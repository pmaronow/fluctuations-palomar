module

public import ActualMacroMinimum
public import ShortComparisonError

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.LaplaceWindowFormalization

open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

section
variable {η Q : ℝ} (hη : 0 < η) (hQ : 1 < Q)

theorem macroInverseQuantile_gap_lower (α : MacroInverseClass η Q)
    {u v : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (huv : u ≤ v) :
    (v-u)/Q ≤ macroInverseQuantile hη hQ α v - macroInverseQuantile hη hQ α u := by
  have hg := constrainedQuantile_gap_lower zero_le_one hη continuousOn_const
    (fun _ _ => le_rfl) (fun _ _ _ _ _ => le_rfl) (zero_lt_one.trans hQ).le
    (zero_lt_one.trans hQ) α (⟨u, hu⟩ : Icc (0 : ℝ) 1) ⟨v, hv⟩ huv
  unfold macroInverseQuantile inverseMassQuantile
  rw [projIcc_of_mem zero_le_one hu, projIcc_of_mem zero_le_one hv]
  exact hg

theorem macro_inverse_field_gap (α : MacroInverseClass η Q) (b h : ℝ → ℝ)
    {t bstar u v : ℝ} (ht : 0 ≤ t) (hbstar : 0 ≤ bstar)
    (hb : MonotoneOn b (Icc (0 : ℝ) 1))
    (hh : MonotoneOn h (Icc (0 : ℝ) 1))
    (hbb : ∀ x ∈ Icc (0 : ℝ) 1, bstar ≤ b x)
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) (huv : u ≤ v) :
    (t * bstar / Q) * (v-u) ≤
      (h v + t*b v*macroInverseQuantile hη hQ α v) -
        (h u + t*b u*macroInverseQuantile hη hQ α u) := by
  have hgap := macroInverseQuantile_gap_lower hη hQ α hu hv huv
  have hmono := macroInverseQuantile_monotone hη hQ α hu hv huv
  have hq0 := (macroInverseQuantile_bounds hη hQ α u).1
  have hbuv := hb hu hv huv
  have hhvu := hh hu hv huv
  have hscale := mul_le_mul_of_nonneg_left hgap (mul_nonneg ht hbstar)
  have hbst := mul_le_mul_of_nonneg_right (hbb v hv) (sub_nonneg.mpr hmono)
  have hbst' := mul_le_mul_of_nonneg_left hbst ht
  have hcost := mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hbuv)) hq0
  have he : (t*bstar/Q)*(v-u) = (t*bstar)*((v-u)/Q) := by ring
  rw [he]
  nlinarith

end

end OAI.SKFluctuations.LaplaceWindowFormalization
