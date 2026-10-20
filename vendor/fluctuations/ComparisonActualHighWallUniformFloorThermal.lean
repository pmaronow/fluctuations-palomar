module

public import ComparisonActualHighWallOuterFloorThermal
public import ComparisonActualHighWallStarFloorRate

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped BigOperators Topology NNReal ENNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem ActualHighWallOverlapMinimum.outer_floor_budget_at_native_scale
    {m delta cl cu Az C0 Ct D Bclock : ℝ} {n : ℕ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    {c K v : ℝ} (hC0 : 0 < C0) (hc : 0 < c) (hcu : 0 < cu) (hK : 0 ≤ K)
    (hxs : M.xs ≤ M.data.d) (hvd : c*M.data.d ≤ v) :
    K*(M.xs+2*v)^2*M.data.N^delta*(comparisonSmallMass M.data.N M.data.E)^2/(v/cu) ≤
      (K*(1/c+2)^2*cu*C0^6)*M.data.N^(delta-6*m)*M.data.d^2*v := by
  let U:=comparisonSmallMass M.data.N M.data.E
  have hv : 0 < v:=(mul_pos hc M.data.hd).trans_le hvd
  have Hd : M.data.d ≤ v/c:=(le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hvd)
  have HR : U/M.data.d ≤ C0^3*M.data.N^(-3*m):=
    (div_le_div_of_nonneg_left M.data.hU.le M.hxs hxs).trans (M.high_mass_small_ratio hC0)
  have HS:=pow_le_pow_left₀ (div_nonneg M.data.hU.le M.data.hd.le) HR 2
  have HEpow : (C0^3*M.data.N^(-3*m))^2=C0^6*M.data.N^(-6*m):=by
    rw [mul_pow,←pow_mul,←Real.rpow_mul_natCast M.data.hN.le]
    congr 1
    congr 1
    ring
  rw [HEpow,div_pow] at HS
  have HU : U^2 ≤ (C0^6*M.data.N^(-6*m))*M.data.d^2:=
    (div_le_iff₀ (sq_pos_of_pos M.data.hd)).mp HS
  have Hsize : (M.xs+2*v)^2 ≤ ((1/c+2)*v)^2:=by
    apply pow_le_pow_left₀ (add_nonneg M.hxs.le (by positivity))
    have Hd' : M.data.d ≤ (1/c)*v:=by simpa only [one_div,div_eq_mul_inv,mul_comm,mul_one,one_mul] using Hd
    nlinarith only [hxs,Hd']
  have Hraw : K*(M.xs+2*v)^2*M.data.N^delta*U^2/(v/cu) ≤
      K*((1/c+2)*v)^2*M.data.N^delta*((C0^6*M.data.N^(-6*m))*M.data.d^2)/(v/cu):=by
    apply div_le_div_of_nonneg_right _ (div_nonneg hv.le hcu.le)
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hsize hK)
        (Real.rpow_nonneg M.data.hN.le _)
    · exact HU
    · exact sq_nonneg U
    · positivity
  have HP : M.data.N^delta*M.data.N^(-6*m)=M.data.N^(delta-6*m):=by
    rw [←Real.rpow_add M.data.hN]
    congr 1
    ring
  apply Hraw.trans_eq
  calc
    _=(K*(1/c+2)^2*cu*C0^6)*(M.data.N^delta*M.data.N^(-6*m))*M.data.d^2*v:=by
      field_simp
    _=_:=by rw [HP]

theorem eventually_actual_high_wall_uniform_outer_floor_thermal
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hc : 0 < c) (hcout : cu*Az < c) :
    ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs ≤ M.data.d → ∀P : M.Potential,∀v : ℝ,
        c*M.data.d ≤ v → M.data.s ≤ v → 2*v ≤ 1 →
        (∫u in Ioo v (2*v),P.positiveMassMask u*
          (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2)) ≤
          (1/2)*M.data.N^(-(actualMassSavingExponent m delta/2))*M.data.d^2*v := by
  obtain ⟨K,hK,HF⟩:=eventually_actual_high_wall_outer_floor_thermal_on_band
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=K*(1/c+2)^2*cu*C0^6
  have Heta:=actualMassSavingExponent_bounds m delta
  have Hnum:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C) (d:=1/2) (q:=delta-6*m)
      (r:=-(actualMassSavingExponent m delta/2)) (by norm_num) (by linarith [Heta.2.1]))
  filter_upwards [HF,Hnum] with n hnFloor hnNum
  intro M hxs P v hvd hsv hv1
  have hv : 0 < v:=(mul_pos hc M.data.hd).trans_le hvd
  have hlohi : v ≤ 2*v:=by linarith only [hv]
  have Hscale : cu*Az*M.xs < v:=by
    have H1:=mul_le_mul_of_nonneg_left hxs (mul_nonneg hcu.le hAz)
    have H2:=mul_lt_mul_of_pos_right hcout M.data.hd
    linarith only [H1,H2,hvd]
  have HF':=hnFloor M P v (2*v) hsv hlohi hv1 Hscale
  have Hnorm:=M.outer_floor_budget_at_native_scale hC0 hc hcu hK.le hxs hvd
  have Hcoef : C*M.data.N^(delta-6*m) ≤
      (1/2)*M.data.N^(-(actualMassSavingExponent m delta/2)):=by
    simpa only [ActualHighWallData.N] using hnNum
  have Hfinal:=mul_le_mul_of_nonneg_right Hcoef (mul_nonneg (sq_nonneg M.data.d) hv.le)
  exact HF'.trans (Hnorm.trans (by simpa only [C,mul_assoc] using Hfinal))

end OAI.SKFluctuations.LaplaceWindowFormalization
