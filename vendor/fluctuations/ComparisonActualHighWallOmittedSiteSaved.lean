module

public import ComparisonActualHighWallLowDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 12000000

theorem eventually_actual_high_wall_omitted_product_saved_cost
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → (1:ℝ)/((n+1:ℕ)*M.data.d)≤((n+1:ℕ):ℝ)^(-m)*M.data.d^3 := by
  have H:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=C0^4) (d:=1) (q:=-(1:ℝ)+m)
      (r:=-(2:ℝ)/3+4*m) zero_lt_one (by linarith [hm]))
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
  have Hn : C0^4*(((n+1:ℕ):ℝ)^(-(1:ℝ)+m))≤((n+1:ℕ):ℝ)^(-(2:ℝ)/3+4*m):=by
    simpa only [one_mul] using hn
  have HC : C0^4*(((n+1:ℕ):ℝ)^(-(1:ℝ)+m))≤C0^4*M.data.d^4:=Hn.trans HR4
  have HC' : ((n+1:ℕ):ℝ)^(-(1:ℝ)+m)≤M.data.d^4:=
    (mul_le_mul_iff_right₀ (pow_pos hC0 4)).mp HC
  have Hmul:=mul_le_mul_of_nonneg_left HC' (Real.rpow_nonneg hN.le (-m))
  have Heq : ((n+1:ℕ):ℝ)^(-m)*((n+1:ℕ):ℝ)^(-(1:ℝ)+m)=
      (1:ℝ)/((n+1:ℕ):ℝ) := by
    rw [←Real.rpow_add hN]
    rw [show -m+(-(1:ℝ)+m)=(-1:ℝ) by ring,Real.rpow_neg_one]
    ring
  rw [Heq] at Hmul
  rw [show (1:ℝ)/((n+1:ℕ)*M.data.d)=((1:ℝ)/(n+1:ℕ))/M.data.d by ring]
  apply (div_le_iff₀ M.data.hd).mpr
  convert Hmul using 1; ring

theorem eventually_actual_high_wall_omitted_site_saved_cost
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → (1:ℝ)/((n+1:ℕ):ℝ)≤((n+1:ℕ):ℝ)^(-m)*M.data.d^4 := by
  filter_upwards [eventually_actual_high_wall_omitted_product_saved_cost (delta:=delta)
    (cl:=cl) (cu:=cu) (Az:=Az) (Ct:=Ct) (D:=D) (Bclock:=Bclock) hm hC0] with n hn
  intro M hwork
  have H:=mul_le_mul_of_nonneg_right (hn M hwork) M.data.hd.le
  have hN : (((n+1:ℕ):ℝ))≠0:=by positivity
  convert H using 1 <;> field_simp [hN,M.data.hd.ne']

end OAI.SKFluctuations.Cavity
