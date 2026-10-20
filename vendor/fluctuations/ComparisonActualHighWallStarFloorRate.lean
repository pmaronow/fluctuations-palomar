module

public import ComparisonActualHighWallStarBandParameters

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem sharp_floor_budget_normalization
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0< C0) {A B W K : ℝ} (hA : 0< A) (hB : 0≤ B) (hW : 0< W)
    (hK : 0≤ K) (hcu : 0< cu) (hxs : M.xs≤ W) :
    K*(M.xs+B*W)^2*M.data.N^delta*(comparisonSmallMass M.data.N M.data.E)^2/(A*W/cu)≤
      (K*(1+B)^2*cu/A*C0^6)*M.data.N^(delta-6*m)*W^3 := by
  let U:=comparisonSmallMass M.data.N M.data.E
  have HR : U/W≤ C0^3*M.data.N^(-3*m):=
    (div_le_div_of_nonneg_left M.data.hU.le M.hxs hxs).trans (M.high_mass_small_ratio hC0)
  have HS:=pow_le_pow_left₀ (div_nonneg M.data.hU.le hW.le) HR 2
  have HEpow : (C0^3*M.data.N^(-3*m))^2=C0^6*M.data.N^(-6*m):=by
    rw [mul_pow,←pow_mul,←Real.rpow_mul_natCast M.data.hN.le]
    congr 1;congr 1;ring
  rw [HEpow] at HS
  have Hsize : (M.xs+B*W)^2≤((1+B)*W)^2:=by
    apply pow_le_pow_left₀ (add_nonneg M.hxs.le (mul_nonneg hB hW.le))
    nlinarith only [hxs]
  have Hraw : K*(M.xs+B*W)^2*M.data.N^delta*U^2/(A*W/cu)≤
      K*((1+B)*W)^2*M.data.N^delta*U^2/(A*W/cu):=by
    apply div_le_div_of_nonneg_right _ (div_nonneg (mul_nonneg hA.le hW.le) hcu.le)
    gcongr
  have HE : K*((1+B)*W)^2*M.data.N^delta*U^2/(A*W/cu)=
      (K*(1+B)^2*cu/A)*M.data.N^delta*(U/W)^2*W^3:=by
    field_simp
  rw [HE] at Hraw
  have HM:=mul_le_mul_of_nonneg_left HS (show 0≤(K*(1+B)^2*cu/A)*M.data.N^delta*W^3 by positivity)
  have HP : M.data.N^delta*M.data.N^(-6*m)=M.data.N^(delta-6*m):=by
    rw [←Real.rpow_add M.data.hN];congr 1;ring
  have Hfinal : (K*(1+B)^2*cu/A)*M.data.N^delta*(C0^6*M.data.N^(-6*m))*W^3=
      (K*(1+B)^2*cu/A*C0^6)*M.data.N^(delta-6*m)*W^3:=by
    calc
      _=(K*(1+B)^2*cu/A*C0^6)*(M.data.N^delta*M.data.N^(-6*m))*W^3:=by ring
      _=_:=by rw [HP]
  exact Hraw.trans (by nlinarith only [HM,Hfinal])

end ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_regular_floor_slab_small
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D A B : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct)
    (hA : cu*Az< A) (hAB : A< B)
    (M : (n : ℕ)→ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hxs : ∀n,(M n).xs≤ W n) (hWlim : Tendsto W atTop (𝓝 0))
    (hsRatio : Tendsto (fun n=>(M n).data.s/W n) atTop (𝓝 0)) :
    ∀ᶠn in atTop,∀P : (M n).Potential,
      (∫u in Ioo (A*W n) (B*W n),P.positiveMassMask u*
        (orderedPathB (n+1) (M n).bf (M n).hf u-(orderedPathS (n+1) (M n).bf (M n).hf u)^2))≤
        (1/2)*(M n).data.N^(-(actualMassSavingExponent m delta/2))*(W n)^3 := by
  have ha : 0< A:=(mul_nonneg hcu.le hAz).trans_lt hA
  have hb : 0< B:=ha.trans hAB
  obtain ⟨K,hK,HF⟩:=eventually_actual_high_wall_outer_floor_thermal_on_band (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=K*(1+B)^2*cu/A*C0^6
  have HB:=(hWlim.const_mul B).eventually (gt_mem_nhds (by simp : B*(0:ℝ)<1))
  have HP:=eventually_actual_high_wall_star_band_parameters (D:=D) (Bclock:=Bclock)
    hm hdelta hcl hcu hAz hC0 hA M W hxs hsRatio
  have hEta:=actualMassSavingExponent_bounds m delta
  have Hnum:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C) (d:=1/2) (q:=delta-6*m)
      (r:=-(actualMassSavingExponent m delta/2)) (by norm_num) (by linarith [hEta.2.1]))
  filter_upwards [HF,HB,HP,Hnum] with n hf hbW hp hnum
  intro P
  have hW : 0< W n:=(M n).hxs.trans_le (hxs n)
  have hlh : A*W n≤ B*W n:=mul_le_mul_of_nonneg_right hAB.le hW.le
  have Hfloor:=hf (M n) P (A*W n) (B*W n) hp.1.le hlh hbW.le hp.2.1
  have Hnorm:=(M n).sharp_floor_budget_normalization hC0 ha hb.le hW hK.le hcu (hxs n)
  have HC : C*(M n).data.N^(delta-6*m)≤(1/2)*(M n).data.N^(-(actualMassSavingExponent m delta/2)):=by
    simpa only [ActualHighWallData.N] using hnum
  exact Hfloor.trans (Hnorm.trans (mul_le_mul_of_nonneg_right HC (pow_pos hW 3).le))

end OAI.SKFluctuations.LaplaceWindowFormalization
