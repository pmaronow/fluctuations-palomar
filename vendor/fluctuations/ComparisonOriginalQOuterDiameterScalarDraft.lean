module

public import ConcreteWallPowerBounds

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 10000000

namespace OriginalQOuterDiameterDraft

theorem concrete_error_div_cube_eq_small_wall_product_draft
    (m : ℝ) {k : ℕ} (hk : 0 < k) :
    wallHighError m k/(wallHighD m k)^3 =
      comparisonSmallMass (k:ℝ) (wallHighError m k)*
        wallHighMass m k := by
  have hkp : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  rw [wallHighSmallMass_eq m hk,wallHighError_eq m hk]
  unfold wallHighD wallHighMass
  rw [←Real.rpow_natCast,←Real.rpow_mul hkp.le,
    ←Real.rpow_sub hkp,←Real.rpow_add hkp]
  congr 1
  ring

theorem squared_diameter_atom_of_energy_and_wall_draft
    {e v K L d Dloc t U H : ℝ}
    (he : 0 ≤ e) (hv : 0 < v) (hK : 0 ≤ K)
    (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hDloc : 0 ≤ Dloc) (ht : 0 ≤ t) (hU : 0 ≤ U)
    (henergy : e*v ≤ 2*L*d^3)
    (hdiam : Dloc ≤ 9*K*L*t*U)
    (hcritical : d^3*U^2 ≤ H) :
    e*(K*v)*Dloc^2 ≤ 162*K^3*L^3*t^2*H := by
  have hR : 0 ≤ 9*K*L*t*U := by positivity
  have hDsq := pow_le_pow_left₀ hDloc hdiam 2
  have hfirst := mul_le_mul_of_nonneg_right henergy
    (show 0 ≤ K*Dloc^2 by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hDsq
    (show 0 ≤ 2*K*L*d^3 by positivity)
  have hthird := mul_le_mul_of_nonneg_left hcritical
    (show 0 ≤ 162*K^3*L^3*t^2 by positivity)
  calc
    e*(K*v)*Dloc^2 = (e*v)*(K*Dloc^2) := by ring
    _ ≤ (2*L*d^3)*(K*Dloc^2) := hfirst
    _ = (2*K*L*d^3)*Dloc^2 := by ring
    _ ≤ (2*K*L*d^3)*(9*K*L*t*U)^2 := hsecond
    _ = (162*K^3*L^3*t^2)*(d^3*U^2) := by ring
    _ ≤ 162*K^3*L^3*t^2*H := by
      simpa only [mul_assoc] using hthird

end OriginalQOuterDiameterDraft
end OAI.SKFluctuations.LaplaceWindowFormalization
