module

public import QuantitativePaper.AbsoluteComparisonDiameterPowers

@[expose] public section

/-! Exact r^(−65/66) normalization of the sharper diameter contribution. -/
noncomputable section
open Set
namespace QuantitativePaper
set_option maxHeartbeats 1000000

def absoluteDyadicPieceRate (u : ℝ) : ℝ :=
  if u ≤ 1 then u^(1/6 : ℝ) else u^(-1/3 : ℝ)

theorem absolute_diameter_weighted_power_bound (N r u η P d : ℝ)
    (hN : 0 < N) (hr : r ∈ Ioc (0 : ℝ) 1) (hu : 0 < u) (hη : 0 ≤ η) (hP : 0 ≤ P)
    (hd : d ∈ Icc (0 : ℝ) 1)
    (hbound : u ≤ 1 → d ≤ P*(r^(-3/5 : ℝ)*u+r^(-7/11 : ℝ)*η^(2/11 : ℝ))) :
    (N*r)^(-2/3 : ℝ)*u^(-1/3 : ℝ)*d^(2/3 : ℝ) ≤
      (1+Real.sqrt P)*N^(-2/3 : ℝ)*r^(-65/66 : ℝ)*
        (absoluteDyadicPieceRate u+u^(-1/3 : ℝ)*η^(1/11 : ℝ)) := by
  have hcoeff : 0 ≤ (N*r)^(-2/3 : ℝ)*u^(-1/3 : ℝ) := by positivity [hr.1]
  have hnorm : (N*r)^(-2/3 : ℝ)*u^(-1/3 : ℝ)*r^(-7/22 : ℝ)*
      (u^(1/2 : ℝ)+η^(1/11 : ℝ)) =
      N^(-2/3 : ℝ)*r^(-65/66 : ℝ)*(u^(1/6 : ℝ)+u^(-1/3 : ℝ)*η^(1/11 : ℝ)) := by
    rw [Real.mul_rpow hN.le hr.1.le]
    calc
      _ = N^(-2/3 : ℝ)*(r^(-2/3 : ℝ)*r^(-7/22 : ℝ))*
        (u^(-1/3 : ℝ)*u^(1/2 : ℝ)+u^(-1/3 : ℝ)*η^(1/11 : ℝ)) := by ring
      _ = _ := by rw [←Real.rpow_add hr.1,←Real.rpow_add hu];norm_num
  by_cases hsmall : u ≤ 1
  · have hh := absolute_diameter_half_bound d P r u η hd hP hr hu.le hη (hbound hsmall)
    have hm := mul_le_mul_of_nonneg_left hh hcoeff
    have he : ((N*r)^(-2/3 : ℝ)*u^(-1/3 : ℝ))*(Real.sqrt P*r^(-7/22 : ℝ)*
        (u^(1/2 : ℝ)+η^(1/11 : ℝ))) =
        Real.sqrt P*(N^(-2/3 : ℝ)*r^(-65/66 : ℝ)*(u^(1/6 : ℝ)+u^(-1/3 : ℝ)*η^(1/11 : ℝ))) := by
      rw [←hnorm]
      ring
    rw [he] at hm
    refine hm.trans ?_
    unfold absoluteDyadicPieceRate
    rw [if_pos hsmall]
    have hc := mul_le_mul_of_nonneg_right (show Real.sqrt P ≤ 1+Real.sqrt P by linarith)
      (show 0 ≤ N^(-2/3 : ℝ)*r^(-65/66 : ℝ)*(u^(1/6 : ℝ)+u^(-1/3 : ℝ)*η^(1/11 : ℝ)) by positivity [hr.1])
    convert hc using 1 <;> ring
  · have hd1 := Real.rpow_le_one hd.1 hd.2 (by norm_num : (0 : ℝ) ≤ 2/3)
    have hm := mul_le_mul_of_nonneg_left hd1 hcoeff
    have hrpow : r^(-2/3 : ℝ) ≤ r^(-65/66 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hr.1 hr.2 (by norm_num)
    have hnr : (N*r)^(-2/3 : ℝ) ≤ N^(-2/3 : ℝ)*r^(-65/66 : ℝ) := by
      rw [Real.mul_rpow hN.le hr.1.le]
      exact mul_le_mul_of_nonneg_left hrpow (by positivity)
    have hbase := mul_le_mul_of_nonneg_right hnr (Real.rpow_nonneg hu.le (-1/3))
    have hsum : u^(-1/3 : ℝ) ≤ absoluteDyadicPieceRate u+u^(-1/3 : ℝ)*η^(1/11 : ℝ) := by
      unfold absoluteDyadicPieceRate
      rw [if_neg hsmall]
      have hh : 0 ≤ u^(-1/3 : ℝ)*η^(1/11 : ℝ) := by positivity
      linarith
    have hh := mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ N^(-2/3 : ℝ)*r^(-65/66 : ℝ) by positivity [hr.1])
    have hfactor := mul_le_mul_of_nonneg_left (show 1 ≤ 1+Real.sqrt P by linarith [Real.sqrt_nonneg P])
      (show 0 ≤ N^(-2/3 : ℝ)*r^(-65/66 : ℝ)*(absoluteDyadicPieceRate u+u^(-1/3 : ℝ)*η^(1/11 : ℝ)) from
        mul_nonneg (by positivity [hr.1]) ((Real.rpow_nonneg hu.le _).trans hsum))
    simp only [mul_one] at hm
    calc
      _ ≤ (N*r)^(-2/3 : ℝ)*u^(-1/3 : ℝ) := hm
      _ ≤ N^(-2/3 : ℝ)*r^(-65/66 : ℝ)*u^(-1/3 : ℝ) := hbase
      _ ≤ N^(-2/3 : ℝ)*r^(-65/66 : ℝ)*(absoluteDyadicPieceRate u+u^(-1/3 : ℝ)*η^(1/11 : ℝ)) := hh
      _ ≤ _ := by convert hfactor using 1 <;> ring

end QuantitativePaper
