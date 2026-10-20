module

public import ComparisonActualHighWallLowDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000

theorem eventually_actual_high_wall_omitted_product_cubic_cost
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → (1:ℝ)/((n+1:ℕ)*M.data.d)≤M.data.d^3 := by
  have H:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^4) (d:=1) (q:=-(1:ℝ))
      (r:=-(2:ℝ)/3+4*m) zero_lt_one (by linarith))
  filter_upwards [H] with n hn
  intro M hwork
  have hN : 0<((n+1:ℕ):ℝ):=by positivity
  have HR:=actual_high_wall_original_boundary_critical_radius hC0 M
  rw [hwork] at HR
  have HR4:=pow_le_pow_left₀ (Real.rpow_pos_of_pos M.data.hN _).le HR 4
  have Heq : (((n+1:ℕ):ℝ)^(-(1:ℝ)/6+m))^4=
      ((n+1:ℕ):ℝ)^(-(2:ℝ)/3+4*m):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hN.le]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  rw [Heq,mul_pow] at HR4
  rw [Real.rpow_neg_one,one_mul] at hn
  have HC : C0^4*(1/((n+1:ℕ):ℝ))≤C0^4*M.data.d^4:=by
    have Hn : C0^4*(1/((n+1:ℕ):ℝ))≤((n+1:ℕ):ℝ)^(-(2:ℝ)/3+4*m):=by
      simpa only [one_div,div_eq_mul_inv,mul_comm,one_mul,mul_one] using hn
    exact Hn.trans HR4
  have HC' : (1:ℝ)/((n+1:ℕ):ℝ)≤M.data.d^4:=
    (mul_le_mul_iff_right₀ (pow_pos hC0 4)).mp (by simpa only [mul_comm] using HC)
  apply (div_le_iff₀ (mul_pos hN M.data.hd)).mpr
  have HN:=mul_le_mul_of_nonneg_left HC' hN.le
  have HN' : (1:ℝ)≤((n+1:ℕ):ℝ)*M.data.d^4:=by simpa only [mul_one_div_cancel hN.ne'] using HN
  convert HN' using 1; ring

end OAI.SKFluctuations.Cavity
