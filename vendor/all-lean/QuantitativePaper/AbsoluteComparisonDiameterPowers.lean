module

public import QuantitativePaper.P2QuantileDiameter

@[expose] public section

/-! Square-root extraction of the actual essential diameter estimate. -/
noncomputable section
open Set
namespace QuantitativePaper
set_option maxHeartbeats 1000000

theorem absolute_diameter_half_bound (d C r u η : ℝ)
    (hd : d ∈ Icc (0 : ℝ) 1) (hC : 0 ≤ C) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hu : 0 ≤ u) (hη : 0 ≤ η)
    (h : d ≤ C*(r^(-3/5 : ℝ)*u+r^(-7/11 : ℝ)*η^(2/11 : ℝ))) :
    d^(2/3 : ℝ) ≤ Real.sqrt C*r^(-7/22 : ℝ)*(u^(1/2 : ℝ)+η^(1/11 : ℝ)) := by
  have hhalf : d^(2/3 : ℝ) ≤ Real.sqrt d := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_ge' hd.1 hd.2 (by norm_num) (by norm_num)
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul hC] at hs
  have ha : 0 ≤ r^(-3/5 : ℝ)*u := mul_nonneg (Real.rpow_nonneg hr.1.le _) hu
  have hb : 0 ≤ r^(-7/11 : ℝ)*η^(2/11 : ℝ) := mul_nonneg (Real.rpow_nonneg hr.1.le _) (Real.rpow_nonneg hη _)
  have hadd : Real.sqrt (r^(-3/5 : ℝ)*u+r^(-7/11 : ℝ)*η^(2/11 : ℝ)) ≤
      Real.sqrt (r^(-3/5 : ℝ)*u)+Real.sqrt (r^(-7/11 : ℝ)*η^(2/11 : ℝ)) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _),?_⟩
    nlinarith only [Real.sq_sqrt ha,Real.sq_sqrt hb,
      mul_nonneg (Real.sqrt_nonneg (r^(-3/5 : ℝ)*u)) (Real.sqrt_nonneg (r^(-7/11 : ℝ)*η^(2/11 : ℝ)))]
  have he₀ : Real.sqrt (r^(-3/5 : ℝ)*u) = r^(-3/10 : ℝ)*u^(1/2 : ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.mul_rpow (Real.rpow_nonneg hr.1.le _) hu,
      ←Real.rpow_mul hr.1.le]
    norm_num
  have he₁ : Real.sqrt (r^(-7/11 : ℝ)*η^(2/11 : ℝ)) = r^(-7/22 : ℝ)*η^(1/11 : ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.mul_rpow (Real.rpow_nonneg hr.1.le _) (Real.rpow_nonneg hη _),
      ←Real.rpow_mul hr.1.le,←Real.rpow_mul hη]
    norm_num
  rw [he₀,he₁] at hadd
  have hp : r^(-3/10 : ℝ) ≤ r^(-7/22 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2 (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hu (1/2))
  have hsum : r^(-3/10 : ℝ)*u^(1/2 : ℝ)+r^(-7/22 : ℝ)*η^(1/11 : ℝ) ≤
      r^(-7/22 : ℝ)*u^(1/2 : ℝ)+r^(-7/22 : ℝ)*η^(1/11 : ℝ) :=
    add_le_add hm le_rfl
  have hh := mul_le_mul_of_nonneg_left (hadd.trans hsum) (Real.sqrt_nonneg C)
  calc
    d^(2/3 : ℝ) ≤ Real.sqrt d := hhalf
    _ ≤ Real.sqrt C*Real.sqrt (r^(-3/5 : ℝ)*u+r^(-7/11 : ℝ)*η^(2/11 : ℝ)) := hs
    _ ≤ _ := by
      convert hh using 1 <;> ring

end QuantitativePaper
