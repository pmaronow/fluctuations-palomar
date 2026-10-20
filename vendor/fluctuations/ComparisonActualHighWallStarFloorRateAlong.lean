module

public import ComparisonActualHighWallStarFloorRate
public import ComparisonActualHighWallStarBandParametersAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

end ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_regular_floor_slab_small_along
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D A B : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hA : cu*Az< A) (hAB : A< B)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0)) :
    ∀ᶠn in atTop,∀P : (M n).Potential,
      (∫u in Ioo (A*W n) (B*W n),P.positiveMassMask u*
        (orderedPathB (dim n+1) (M n).bf (M n).hf u-(orderedPathS (dim n+1) (M n).bf (M n).hf u)^2))≤
        (1/2)*(M n).data.N^(-(actualMassSavingExponent m delta/2))*(W n)^3 := by
  have ha : 0< A:=(mul_nonneg hcu.le hAz).trans_lt hA
  have hb : 0< B:=ha.trans hAB
  obtain ⟨K,hK,HF⟩:=eventually_actual_high_wall_outer_floor_thermal_on_band (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=K*(1+B)^2*cu/A*C0^6
  have HB:=(hWlim.const_mul B).eventually (gt_mem_nhds (by simp : B*(0:ℝ)<1))
  have HP:=eventually_actual_high_wall_star_band_parameters_along (D:=D) (Bclock:=Bclock)
    hm hdelta hcl hcu hAz hC0 hA dim hdim M W hxs hsRatio
  have hEta:=actualMassSavingExponent_bounds m delta
  have Hnum:=((tendsto_add_atTop_nat 1).comp hdim).eventually
    (eventually_coefficient_rpow_le (c:=C) (d:=1/2) (q:=delta-6*m)
      (r:=-(actualMassSavingExponent m delta/2)) (by norm_num) (by linarith [hEta.2.1]))
  filter_upwards [(hdim.eventually HF),HB,HP,Hnum] with n hf hbW hp hnum
  intro P
  have hW : 0< W n:=(M n).hxs.trans_le (hxs n)
  have hlh : A*W n≤ B*W n:=mul_le_mul_of_nonneg_right hAB.le hW.le
  have Hfloor:=hf (M n) P (A*W n) (B*W n) hp.1.le hlh hbW.le hp.2.1
  have Hnorm:=(M n).sharp_floor_budget_normalization hC0 ha hb.le hW hK.le hcu (hxs n)
  have HC : C*(M n).data.N^(delta-6*m)≤(1/2)*(M n).data.N^(-(actualMassSavingExponent m delta/2)):=by
    simpa only [Function.comp_apply,ActualHighWallData.N] using hnum
  exact Hfloor.trans (Hnorm.trans (mul_le_mul_of_nonneg_right HC (pow_pos hW 3).le))

end OAI.SKFluctuations.LaplaceWindowFormalization
