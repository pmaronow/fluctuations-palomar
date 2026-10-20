module

public import ComparisonActualHighWallWholeThermalCore
public import ComparisonActualHighWallStarFloorRate
public import ComparisonActualHighWallOuterThermal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000

theorem eventually_actual_high_wall_regular_mass_slab_polynomial
    {m delta cl cu Az C0 Ct D Bclock A B : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hA : cu*Az< A) (hAB : A< B)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxsd : ∀n,(M n).xs≤(M n).data.d) (hdW : ∀n,(M n).data.d≤ W n)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0)) :
    ∀ᶠn in atTop,
      (∫u in Ioo (A*W n) (B*W n),orderedPathB (n+1) (M n).bf (M n).hf u-
        (orderedPathS (n+1) (M n).bf (M n).hf u)^2)≤
          (M n).data.N^(-(actualMassSavingExponent m delta/2))*(W n)^3 := by
  have hD : 0< D:=(M 0).data.hd.trans_le (M 0).hdD
  have hxs n : (M n).xs≤ W n:=(hxsd n).trans (hdW n)
  have HA:=eventually_actual_high_wall_outer_cap_contact_thermal hm hdelta hroom
    hcl hcu hAz hC0 hCt hD hA hAB M W hxsd hdW hWlim hsRatio
  have HF:=eventually_actual_high_wall_regular_floor_slab_small Bclock hm hdelta hroom
    hcl hcu hAz hC0 hCt hA hAB M W hxs hWlim hsRatio
  have HP:=eventually_actual_high_wall_star_band_parameters hm hdelta hcl hcu hAz hC0 hA
    M W hxs hsRatio
  have HB:=(hWlim.const_mul B).eventually (eventually_le_nhds (show B*(0:ℝ)<1 by simp))
  have Hnum:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=B-A) (d:=1/2)
      (q:=-(5*actualMassSavingExponent m delta/8))
      (r:=-(actualMassSavingExponent m delta/2)) (by norm_num)
      (by linarith [actualMassSavingExponent_pos hm hdelta]))
  filter_upwards [HA,HF,HP,HB,Hnum] with n ha hf hp hb hnum
  obtain ⟨P⟩:=(M n).exists_potential
  have hW : 0< W n:=(M n).data.hd.trans_le (hdW n)
  have hABW : A*W n≤ B*W n:=mul_le_mul_of_nonneg_right hAB.le hW.le
  have HC : (B-A)*(M n).data.N^(-(5*actualMassSavingExponent m delta/8))≤
      (1/2)*(M n).data.N^(-(actualMassSavingExponent m delta/2)):=by
    simpa only [ActualHighWallData.N] using hnum
  have HCW : (M n).data.N^(-(5*actualMassSavingExponent m delta/8))*(W n)^2*(B*W n-A*W n)≤
      (1/2)*(M n).data.N^(-(actualMassSavingExponent m delta/2))*(W n)^3:=by
    have HH:=mul_le_mul_of_nonneg_right HC (pow_pos hW 3).le
    convert HH using 1;ring
  have HD:=P.mass_thermal_slab_decomposition hp.1.le hABW hb
  change (∫u in Ioo (A*W n) (B*W n),(M n).shiftedNativeModel.thermal u)≤_
  rw [HD]
  exact (add_le_add (hf P) ((ha P).trans HCW)).trans (by ring_nf;exact le_rfl)

end OAI.SKFluctuations.LaplaceWindowFormalization
