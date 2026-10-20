module

public import ComparisonSignedCavityRestPhysicalRawTransport

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem physical_raw_root_square_le {z a : ℝ} (hI : 0 ≤ z) (ha : 0 ≤ a)
    (l : ℕ) (hl : 0 < l) (H : z ≤ a^(2*l)) :
    (z^(((4*l:ℕ):ℝ)⁻¹))^2 ≤ a := by
  rw [←Real.rpow_mul_natCast hI]
  have he : (((4*l:ℕ):ℝ)⁻¹)*(2:ℕ) = (((2*l:ℕ):ℝ)⁻¹) := by
    have hlr : (l:ℝ) ≠ 0 := by exact_mod_cast hl.ne'
    push_cast
    field_simp
    ring
  rw [he]
  exact (Real.rpow_le_rpow hI H (by positivity)).trans_eq
    (Real.pow_rpow_inv_natCast ha (by omega))

end OAI.SKFluctuations.Cavity
