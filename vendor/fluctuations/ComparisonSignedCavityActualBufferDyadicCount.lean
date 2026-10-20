module

public import ComparisonSignedCavityActualSlowWindowSequence

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity
set_option maxHeartbeats 6000000

theorem exists_actual_buffer_dyadic_count {N exponent s Rmacro : ℝ}
    (hN : 1 < N) (hlog : 1 ≤ Real.log N) (hs : 0 < s) (hmacro : 0 < Rmacro)
    (hsR : 2*s ≤ Rmacro) (hRone : Rmacro ≤ 1)
    (hlower : N^(-exponent) ≤ s) :
    ∃J : ℕ,1 ≤ J ∧ Rmacro ≤ (2:ℝ)^J*s ∧ (2:ℝ)^J*s < 2*Rmacro ∧
      ((J+3:ℕ):ℝ) ≤ (exponent/Real.log 2+4)*Real.log N := by
  let X := Rmacro/s
  let J := PositiveLaplaceAssembly.logarithmicCount 2 X
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hX : 0 < X := div_pos hmacro hs
  have hX2 : 2 ≤ X := (le_div_iff₀ hs).mpr hsR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : 0 < Real.log X := Real.log_pos (lt_of_lt_of_le (by norm_num : (1:ℝ) < 2) hX2)
  have hceil := Nat.le_ceil (Real.log X/Real.log 2)
  have hJ : 1 ≤ J := by
    by_contra hnot
    have hJ0 : J=0 := by omega
    change Real.log X/Real.log 2 ≤ (J:ℝ) at hceil
    rw [hJ0] at hceil
    simp only [Nat.cast_zero] at hceil
    exact not_le_of_gt (div_pos hlogX hlog2) hceil
  have hreach := PositiveLaplaceAssembly.pow_logarithmicCount_ge (by norm_num : (1:ℝ) < 2) hX
  have hreach' : Rmacro ≤ (2:ℝ)^J*s := (div_le_iff₀ hs).mp hreach
  have hclt := Nat.ceil_lt_add_one (div_nonneg hlogX.le hlog2.le)
  change (J:ℝ) < Real.log X/Real.log 2+1 at hclt
  have hupper : (2:ℝ)^J < 2*X := by
    apply (Real.log_lt_log_iff (by positivity : 0 < (2:ℝ)^J) (by positivity : 0 < 2*X)).mp
    rw [Real.log_pow,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hX.ne']
    have H := mul_lt_mul_of_pos_right hclt hlog2
    have he : (Real.log X/Real.log 2+1)*Real.log 2=Real.log X+Real.log 2 := by field_simp
    rw [he] at H
    linarith
  have hupper' : (2:ℝ)^J*s < 2*Rmacro := by
    have H := mul_lt_mul_of_pos_right hupper hs
    have he : (2*X)*s=2*Rmacro := by dsimp only [X];field_simp
    simpa only [he] using H
  have hXpower : X ≤ N^exponent := by
    apply (div_le_iff₀ hs).mpr
    have H := mul_le_mul_of_nonneg_left hlower (Real.rpow_nonneg hN0.le exponent)
    rw [←Real.rpow_add hN0,add_neg_cancel,Real.rpow_zero] at H
    exact hRone.trans H
  have hlogbound := Real.log_le_log hX hXpower
  rw [Real.log_rpow hN0] at hlogbound
  have hcount : (J:ℝ) ≤ exponent/Real.log 2*Real.log N+1 := by
    have H := div_le_div_of_nonneg_right hlogbound hlog2.le
    have he : (exponent*Real.log N)/Real.log 2=exponent/Real.log 2*Real.log N := by ring
    rw [he] at H
    linarith
  refine ⟨J,hJ,hreach',hupper',?_⟩
  simp only [Nat.cast_add,Nat.cast_ofNat]
  nlinarith only [hcount,hlog]

namespace NativeOverlapMinimum

theorem eventually_actual_minimum_scale_polynomial_lower
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (hm : 0 < m) (hC0 : 0 < C0) :
    ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.context.N^(-(2:ℝ)) ≤ M.xs := by
  have Hcoef := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=1) (d:=1/C0) (q:=-(2:ℝ)) (r:=-(1:ℝ))
      (by positivity) (by norm_num))
  filter_upwards [Hcoef] with n hn
  intro M
  have hupper : M.context.E ≤ M.context.d^2/Real.sqrt M.context.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr M.context.hN)).mpr (by simpa only [mul_comm] using M.hupper)
  have hlower : (1/C0)*M.context.N^(-(2:ℝ)/3+m)*M.context.d ≤ M.context.E := by
    have H : (M.context.N^(-(2:ℝ)/3+m)*M.context.d)/C0 ≤ M.context.E :=
      (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using M.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  have Hparent := comparison_parent_scale_lower_bounds M.context.hN (one_div_pos.mpr hC0)
    M.context.hd hlower hupper
  have Hpow : M.context.N^(-(1:ℝ)) ≤ M.context.N^(-(1:ℝ)/6+m) :=
    Real.rpow_le_rpow_of_exponent_le (by
      dsimp only [NativeOverlapContext.N]
      exact_mod_cast Nat.succ_pos n) (by linarith)
  have Hx := (mul_le_mul_of_nonneg_left Hpow (one_div_pos.mpr hC0).le).trans
    (Hparent.2.2.trans M.hscale)
  exact (show M.context.N^(-(2:ℝ)) ≤ (1/C0)*M.context.N^(-(1:ℝ)) by
    simpa only [NativeOverlapContext.N,one_mul] using hn).trans Hx

end NativeOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
