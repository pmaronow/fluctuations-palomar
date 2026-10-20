module

public import SKProof.Port.ComparisonActualOriginalQClocks
public import ComparisonSignedCavityActualTerminalDepth

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
theorem canonical_high_mass_scale_critical_lower
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0) :
    (1/C0)*a.data.N^(-(1:ℝ)/6+m) ≤ a.xs := by
  have Hupper : a.data.E ≤ a.data.d^2/Real.sqrt a.data.N :=
    (le_div_iff₀ (Real.sqrt_pos.mpr a.data.hN)).mpr (by simpa only [mul_comm] using a.hupper)
  have Hlower : (1/C0)*a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ a.data.E := by
    have H := (div_le_iff₀ hC0).mpr (by simpa only [mul_comm] using a.hlower)
    simpa only [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc,one_mul] using H
  exact (comparison_parent_scale_lower_bounds a.data.hN (one_div_pos.mpr hC0)
    a.data.hd Hlower Hupper).2.2.trans a.hscale

theorem canonical_high_mass_inverse_power
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0) (k : ℕ) :
    1/(a.data.N^((k:ℝ)/6)*a.xs^k) ≤ C0^k*a.data.N^(-(k:ℝ)*m) :=
  mass_critical_inverse_power a.data.hN a.hxs hC0 (a.canonical_high_mass_scale_critical_lower hC0) k

theorem actual_terminal_power_over_scale {n : ℕ}
    (a : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hC0 : 0<C0) {C gamma : ℝ} (hC : 0≤C) (k : ℕ) :
    C*a.data.N^(-gamma*(k:ℝ))/a.xs^2 ≤
      (C*C0^2)*a.data.N^(-(gamma*(k:ℝ)-(1:ℝ)/3+2*m)) := by
  have H:=a.canonical_high_mass_inverse_power hC0 2
  norm_num only [Nat.cast_ofNat] at H
  have Hmul:=mul_le_mul_of_nonneg_left H
    (show 0≤C*a.data.N^((1:ℝ)/3-gamma*(k:ℝ)) by positivity)
  have HEleft : C*a.data.N^((1:ℝ)/3-gamma*(k:ℝ))*
      (1/(a.data.N^((1:ℝ)/3)*a.xs^2))=C*a.data.N^(-gamma*(k:ℝ))/a.xs^2 := by
    calc
      _=C*(a.data.N^((1:ℝ)/3-gamma*(k:ℝ))/a.data.N^((1:ℝ)/3))/a.xs^2 := by ring
      _=_ := by rw [←Real.rpow_sub a.data.hN];congr 2;congr 1;ring
  have HEright : C*a.data.N^((1:ℝ)/3-gamma*(k:ℝ))*(C0^2*a.data.N^(-(2:ℝ)*m))=
      (C*C0^2)*a.data.N^(-(gamma*(k:ℝ)-(1:ℝ)/3+2*m)) := by
    calc
      _=(C*C0^2)*(a.data.N^((1:ℝ)/3-gamma*(k:ℝ))*a.data.N^(-(2:ℝ)*m)) := by ring
      _=_ := by rw [←Real.rpow_add a.data.hN];congr 1;congr 1;ring
  rwa [HEleft,HEright] at Hmul

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal
theorem actual_omitted_product_cubic_ratio_le_original_q
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock) (hC0 : 0 < C0)
    (W : ℝ) (hxW : M.xs ≤ W) :
    (1/(n+1:ℕ):ℝ)/(M.xs^3*W) ≤ C0^4*M.data.N^(-((1:ℝ)/3+4*m)) := by
  have H:=M.canonical_high_mass_inverse_power hC0 4
  simp only [Nat.cast_ofNat,show (4:ℝ)/6=(2:ℝ)/3 by norm_num] at H
  have HM:=mul_le_mul_of_nonneg_left H (Real.rpow_nonneg M.data.hN.le (-((1:ℝ)/3)))
  have Hpow : M.data.N^(-((1:ℝ)/3))=M.data.N^((2:ℝ)/3)/M.data.N := by
    calc
      _=M.data.N^(((2:ℝ)/3)-1):=by congr 1;ring
      _=M.data.N^((2:ℝ)/3)/M.data.N^((1:ℝ)):=Real.rpow_sub M.data.hN _ _
      _=_:=by rw [Real.rpow_one]
  have HE : M.data.N^(-((1:ℝ)/3))*(1/(M.data.N^((2:ℝ)/3)*M.xs^4))=
      (1/(n+1:ℕ):ℝ)/M.xs^4 := by
    rw [Hpow]
    have hP:=(Real.rpow_pos_of_pos M.data.hN ((2:ℝ)/3)).ne'
    have hx:=M.hxs.ne'
    have hN:=M.data.hN.ne'
    change _=(1/M.data.N)/M.xs^4
    field_simp
  have HR : M.data.N^(-((1:ℝ)/3))*(C0^4*M.data.N^(-(4:ℝ)*m))=
      C0^4*M.data.N^(-((1:ℝ)/3+4*m)) := by
    rw [mul_left_comm,←Real.rpow_add M.data.hN]
    congr 2
    ring
  rw [HE,HR] at HM
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hx:=M.hxs
  have HX : M.xs^4 ≤ M.xs^3*W := by
    calc
      _=M.xs^3*M.xs:=by ring
      _≤_:=mul_le_mul_of_nonneg_left hxW (pow_nonneg M.hxs.le 3)
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) HX).trans HM

theorem eventually_actual_omitted_product_cubic_cost_saved_original_q
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (hm : 0 < m) (hC0 : 0 < C0) (A : ℝ) (hA : 0 ≤ A) :
    ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀ W : ℝ,M.xs ≤ W →
        A/((n+1:ℕ)*M.xs) ≤ ((n+1:ℕ):ℝ)^(-(1:ℝ)/6)*(W*M.xs^2) := by
  have H:=(tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=A*C0^4) (d:=1)
      (q:=-((1:ℝ)/3+4*m)) (r:=-(1:ℝ)/6) zero_lt_one (by linarith))
  filter_upwards [H] with n hn
  intro M W hxW
  have hx:=M.hxs
  have hW:=hx.trans_le hxW
  have HR:=mul_le_mul_of_nonneg_left (actual_omitted_product_cubic_ratio_le_original_q M hC0 W hxW) hA
  have HN : A*((1/(n+1:ℕ):ℝ)/(M.xs^3*W)) ≤ ((n+1:ℕ):ℝ)^(-(1:ℝ)/6) := by
    apply HR.trans
    simpa only [ActualHighWallData.N,mul_assoc,one_mul] using hn
  have HE : A/((n+1:ℕ)*M.xs)/(W*M.xs^2)=A*((1/(n+1:ℕ):ℝ)/(M.xs^3*W)) := by
    field_simp
  rw [←HE] at HN
  exact (div_le_iff₀ (show 0 < W*M.xs^2 by positivity)).mp HN

end OAI.SKFluctuations.Cavity
