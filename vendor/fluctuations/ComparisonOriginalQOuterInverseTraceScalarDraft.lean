module

public import ConcreteWallPowers
public import ComparisonConditionalErrorSize

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace OriginalQOuterInverseTraceDraft

theorem concrete_small_mass_eq_decay_wall_mass_draft
    (m : ℝ) {k : ℕ} (hk : 0 < k) :
    comparisonSmallMass (k:ℝ) (wallHighError m k) =
      (k:ℝ)^(-30*m)*wallHighMass m k := by
  have hkp : 0 < (k:ℝ) := Nat.cast_pos.mpr hk
  rw [wallHighSmallMass_eq m hk]
  unfold wallHighMass
  rw [←Real.rpow_add hkp]
  congr 1
  ring

theorem inverse_trace_atom_of_endpoint_and_wall_mass_draft
    {N E U v K J e ez m : ℝ}
    (hN : 0 < N) (hE : 0 < E) (hU : U = comparisonSmallMass N E)
    (hv : 0 < v) (hK : 1 ≤ K) (hJ : 0 ≤ J)
    (he : 0 ≤ e) (hez : 0 < ez) (hshape : e ≤ J*ez)
    (hwall : U ≤ N^(-30*m)*v) :
    e*(K*v)*(3/(N*ez*(K*v)^2)) ≤
      3*J*N^(-30*m)*E := by
  have hKp : 0 < K := zero_lt_one.trans_le hK
  have hKv : 0 < K*v := mul_pos hKp hv
  have hNv : 0 < N*v := mul_pos hN hv
  have hNKv : 0 < N*K*v := by positivity
  have hratio : e/ez ≤ J := (div_le_iff₀ hez).mpr (by
    simpa only [mul_comm] using hshape)
  have hratio0 : 0 ≤ e/ez := div_nonneg he hez.le
  have hden : 1/(N*K*v) ≤ 1/(N*v) := by
    apply one_div_le_one_div_of_le hNv
    have H := mul_le_mul_of_nonneg_right hK hv.le
    have Hmul := mul_le_mul_of_nonneg_left H hN.le
    nlinarith only [Hmul]
  have hUdecay : comparisonSmallMass N E ≤ N^(-30*m)*v := by
    rwa [hU] at hwall
  have hNvRate : 1/(N*v) ≤ N^(-30*m)*E := by
    have hUv : comparisonSmallMass N E/v ≤ N^(-30*m) :=
      (div_le_iff₀ hv).mpr hUdecay
    have hidentity : 1/(N*v)=E*(comparisonSmallMass N E/v) := by
      unfold comparisonSmallMass
      field_simp [hN.ne',hE.ne',hv.ne']
    rw [hidentity]
    calc
      E*(comparisonSmallMass N E/v) ≤ E*N^(-30*m) :=
        mul_le_mul_of_nonneg_left hUv hE.le
      _ = N^(-30*m)*E := mul_comm _ _
  have hratioBound : 3*(e/ez)*(1/(N*K*v)) ≤
      3*J*(1/(N*v)) := by
    have H1 := mul_le_mul_of_nonneg_right hratio
      (show 0 ≤ 3*(1/(N*K*v)) by positivity)
    have H2 := mul_le_mul_of_nonneg_left hden
      (show 0 ≤ 3*J by positivity)
    nlinarith only [H1,H2]
  have hident : e*(K*v)*(3/(N*ez*(K*v)^2)) =
      3*(e/ez)*(1/(N*K*v)) := by
    field_simp [hN.ne',hez.ne',hv.ne',hKp.ne']
  rw [hident]
  exact hratioBound.trans (by
    have H := mul_le_mul_of_nonneg_left hNvRate
      (show 0 ≤ 3*J by positivity)
    nlinarith only [H])

end OriginalQOuterInverseTraceDraft
end OAI.SKFluctuations.LaplaceWindowFormalization
