module

public import ComparisonOriginalQOuterInverseTraceScalarDraft
public import ComparisonOriginalQOuterTraceGeometryImportFirstDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m cl cu Az C0 Ct D Bclock : ℝ}
variable (Q : ActualThetaZeroOverlapMinimum
  (n+1) m (m/10000) cl cu Az C0 Ct D Bclock)

theorem outer_trace_import_first_small_mass_eq_wall_mass_draft
    (hE : Q.data.E = wallHighError m (n+1))
    (hs : Q.data.s = wallHighMass m (n+1)) :
    comparisonSmallMass Q.data.N Q.data.E =
      Q.data.N^(-30*m)*Q.data.s := by
  rw [hE,hs]
  simpa only [ActualHighWallData.N] using
    _root_.OAI.SKFluctuations.LaplaceWindowFormalization.OriginalQOuterInverseTraceDraft.concrete_small_mass_eq_decay_wall_mass_draft m
        (show 0 < n+1 by omega)

theorem outer_trace_import_first_atom_rate_draft
    (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az)
    (hE : Q.data.E = wallHighError m (n+1))
    (hs : Q.data.s = wallHighMass m (n+1))
    {lo K v : ℝ} (hK : 4 ≤ K)
    (hv : v ∈ Ioc (0:ℝ) 1)
    (houter : 2*cu*(Az+1)*Q.xs ≤ lo)
    (hgroup : (cl/(4*cu))*lo ≤ v)
    (hstart : 2*Q.data.s ≤ (cl/(4*cu))*lo) :
    let z := min (K*v) 1
    let J := max 1 ((Az+1/cl)*(2/cl+K))
    let e := laplaceComparisonStrength Q.data.d Q.lam v
    let ez := laplaceComparisonStrength Q.data.d Q.lam
      (Q.shiftedNativeModel.R z)
    e*(K*v)*(3/(Q.data.N*ez*(K*v)^2)) ≤
      3*J*Q.data.N^(-30*m)*Q.data.E := by
  let z := min (K*v) 1
  let J := max 1 ((Az+1/cl)*(2/cl+K))
  let e := laplaceComparisonStrength Q.data.d Q.lam v
  let ez := laplaceComparisonStrength Q.data.d Q.lam
    (Q.shiftedNativeModel.R z)
  have hxs := Q.outer_trace_import_first_carrier_le_group_draft
    hcl hcu hAz houter hgroup
  have hJ : 0 ≤ J := zero_le_one.trans (le_max_left _ _)
  have hshape : e ≤ J*ez := by
    simpa only [z,J,e,ez] using
      (Q.outer_trace_import_first_endpoint_strength_le_draft
        hcl hAz (K:=K) (H:=2/cl)
        (by linarith) (by positivity) hv hxs)
  have hwallEq := Q.outer_trace_import_first_small_mass_eq_wall_mass_draft hE hs
  have hwall : comparisonSmallMass Q.data.N Q.data.E ≤
      Q.data.N^(-30*m)*v := by
    rw [hwallEq]
    have Hs : Q.data.s ≤ v := by linarith only [hstart,hgroup,Q.data.hs.1]
    exact mul_le_mul_of_nonneg_left Hs
      (Real.rpow_pos_of_pos Q.data.hN _).le
  have H := _root_.OAI.SKFluctuations.LaplaceWindowFormalization.OriginalQOuterInverseTraceDraft.inverse_trace_atom_of_endpoint_and_wall_mass_draft
      Q.data.hN Q.data.hE rfl hv.1 (by linarith : 1 ≤ K) hJ
      (laplaceComparisonStrength_pos Q.data.d Q.hlam v).le
      (laplaceComparisonStrength_pos Q.data.d Q.hlam _)
      hshape hwall
  simpa only [z,J,e,ez] using H

theorem outer_trace_import_first_five_atom_input_draft
    (hm : 0 < m) (hcl : 0 < cl) (hcu : 0 < cu)
    (hAz : 0 ≤ Az)
    (hE : Q.data.E = wallHighError m (n+1))
    (hs : Q.data.s = wallHighMass m (n+1))
    (hL : 1 ≤ Real.log Q.data.N)
    {lo K v : ℝ} (hK : 4 ≤ K)
    (hv : v ∈ Ioc (0:ℝ) 1)
    (houter : 2*cu*(Az+1)*Q.xs ≤ lo)
    (hgroup : (cl/(4*cu))*lo ≤ v)
    (hstart : 2*Q.data.s ≤ (cl/(4*cu))*lo) :
    let z := min (K*v) 1
    let J := max 1 ((Az+1/cl)*(2/cl+K))
    let e := laplaceComparisonStrength Q.data.d Q.lam v
    let P := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam
      (Q.shiftedNativeModel.R z)
    let M := K*v
    e*M*(3/(P*M^2)) ≤
      (3*J)*(Real.log Q.data.N)^3*
        Q.data.N^(-(m/10000)/2)*Q.data.E := by
  let J := max 1 ((Az+1/cl)*(2/cl+K))
  have H := Q.outer_trace_import_first_atom_rate_draft
    hm hcl hcu hAz hE hs hK hv houter hgroup hstart
  have hN : 1 ≤ Q.data.N := by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hpow : Q.data.N^(-30*m) ≤
      Q.data.N^(-(m/10000)/2) :=
    Real.rpow_le_rpow_of_exponent_le hN (by linarith [hm])
  have hL3 : 1 ≤ (Real.log Q.data.N)^3 := one_le_pow₀ hL
  have hJ : 0 ≤ J := zero_le_one.trans (le_max_left _ _)
  have hE0 : 0 ≤ Q.data.E := Q.data.hE.le
  have Hpow := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ 3*J*Q.data.E by positivity)
  have Hlog := mul_le_mul_of_nonneg_left hL3
    (show 0 ≤ 3*J*Q.data.N^(-(m/10000)/2)*Q.data.E by positivity)
  dsimp only [J] at H Hpow Hlog ⊢
  nlinarith only [H,Hpow,Hlog]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
