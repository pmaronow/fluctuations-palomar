module

public import SKBarriers2.Corner.FrozenRowsMixedValue3

@[expose] public section

noncomputable section
open scoped BigOperators
open Set
namespace SKBarriers2.Corner
local notation "X" => (Fin 3 → ℝ)

theorem movingAffineFirstCoefficient_uniform_orders (dmax : ℕ) (B K L : ℝ) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ r ≤ dmax, ∀ p ≤ 5,
      ∀ A U : X →L[ℝ] X, ∀ b d v w : X,
        ‖A‖ ≤ K → ‖U‖ ≤ K → ‖b‖ ≤ K → ‖d‖ ≤ K → ‖v‖ ≤ K → ‖w‖ ≤ K →
          movingAffineFirstCoefficient r p B K L A U b d v w ≤ T := by
  classical
  let I := Fin (dmax + 1) × Fin 6
  choose T _hT hbound using (fun i : I =>
    movingAffineFirstCoefficient_uniform i.1.val i.2.val B K L)
  refine ⟨1 + ∑ i : I, |T i|,
    le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
  intro r hr p hp A U b d v w hA hU hb hd hv hw
  let i : I := (⟨r, by omega⟩, ⟨p, by omega⟩)
  calc
    _ ≤ T i := hbound i A U b d v w hA hU hb hd hv hw
    _ ≤ |T i| := le_abs_self _
    _ ≤ ∑ j : I, |T j| := Finset.single_le_sum
      (fun j _ => abs_nonneg (T j)) (Finset.mem_univ i)
    _ ≤ 1 + ∑ j : I, |T j| := by linarith

end SKBarriers2.Corner
