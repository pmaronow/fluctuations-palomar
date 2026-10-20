module

public import ComparisonActualHighWallThetaZeroStrongScaleGeometry
public import ComparisonShiftedNativeThermalGeometry
public import ComparisonNativeActualIntermediateMassScale
public import ComparisonNativeCavityRadiusGoodPoint

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal BigOperators

def OriginalQIntermediateDyadSaving
    (m delta cl cu Az C0 Ct D Bclock Cs c C : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∀ Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      Q.data.s ≤ Q.xs → 64*Q.data.s ≤ c*Q.xs →
      Q.xs^2 ≤ Cs*laplaceComparisonStrength Q.data.d Q.lam Q.xs →
      Q.directTestWorkingScale ≤ 1 →
      ∀ v, 0 < v → 2*v ≤ 1 → c*Q.xs ≤ v → v ≤ C*Q.directTestWorkingScale →
        (∫ u in v..2*v, orderedPathB (n+1) Q.sweepBf Q.sweepHf u -
          (orderedPathS (n+1) Q.sweepBf Q.sweepHf u)^2) /
          (Q.xs^4*v/(actualIntermediateMassEffectiveScale Q.directTestWorkingScale v)^2)
        ≤ Q.data.N^(-(actualMassSavingExponent m delta/2))

theorem original_q_strong_high_mass_band_of_dyads_original_q
    {m delta cl cu Az C0 Ct D Bclock Cs A B : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta)
    (hA : 0 < A) (hA1 : 1 ≤ A) (hAB : A ≤ B)
    (Hdyad : OriginalQIntermediateDyadSaving m delta cl cu Az C0 Ct D Bclock Cs A B) :
    ∀ᶠ n : ℕ in atTop,
      ∀ Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        Q.data.s ≤ Q.xs → 64*Q.data.s ≤ A*Q.xs →
        Q.xs^2 ≤ Cs*laplaceComparisonStrength Q.data.d Q.lam Q.xs →
        Q.directTestWorkingScale ≤ 1 → 2*B*Q.directTestWorkingScale ≤ 1 →
        (∫ u in A*Q.directTestWorkingScale..B*Q.directTestWorkingScale,
          orderedPathB (n+1) Q.sweepBf Q.sweepHf u -
            (orderedPathS (n+1) Q.sweepBf Q.sweepHf u)^2) ≤
          Q.data.N^(-(3*actualMassSavingExponent m delta/8)) *
            (Q.xs^4/Q.directTestWorkingScale) := by
  have hratio : 1 ≤ B/A := (one_le_div hA).mpr hAB
  obtain ⟨K,hKlo,hKhi⟩ := exists_nat_pow_near hratio (show (1:ℝ) < 2 by norm_num)
  have hAK : A*(2:ℝ)^K ≤ B := by
    simpa only [mul_comm] using (le_div_iff₀ hA).mp hKlo
  have hBK : B < A*(2:ℝ)^(K+1) := by
    have HH := (div_lt_iff₀ hA).mp hKhi
    nlinarith
  let eta := actualMassSavingExponent m delta
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have Hcoefficient := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=(K+1:ℕ)*B) (d:=1)
      (q:=-eta/2) (r:=-(3*eta/8)) zero_lt_one (by linarith))
  filter_upwards [Hdyad,Hcoefficient] with n hnDyad hnCoef
  intro Q hsXs hsHigh hsmall hW1 hbandSmall
  let W := Q.directTestWorkingScale
  let z := fun j : ℕ=>A*(2:ℝ)^j*W
  let f := fun u=>orderedPathB (n+1) Q.sweepBf Q.sweepHf u-(orderedPathS (n+1) Q.sweepBf Q.sweepHf u)^2
  have hW : 0 < W := Q.direct_test_working_scale_pos
  have hB : 0 < B := hA.trans_le hAB
  have hzPos j : 0 < z j := by dsimp [z]; positivity
  have hzNext j : z (j+1)=2*z j := by dsimp [z]; rw [pow_succ]; ring
  have hzUpper j (hj : j ≤ K) : z j ≤ B*W := by
    have hp := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hj
    have HH := mul_le_mul_of_nonneg_left hp hA.le
    exact mul_le_mul_of_nonneg_right (HH.trans hAK) hW.le
  have hzLower j : A*W ≤ z j := by
    have hp : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num)
    have HH := mul_le_mul_of_nonneg_left hp (mul_pos hA hW).le
    calc
      A*W = A*W*1 := (mul_one _).symm
      _ ≤ A*W*(2:ℝ)^j := HH
      _ = z j := by dsimp [z]; ring
  have hzLast : z (K+1) ≤ 2*B*W := by
    rw [hzNext]
    have HH := mul_le_mul_of_nonneg_left (hzUpper K le_rfl) (show (0:ℝ) ≤ 2 by norm_num)
    convert HH using 1
    ring
  have hBandLast : B*W ≤ z (K+1) := mul_le_mul_of_nonneg_right hBK.le hW.le
  have hfi : IntervalIntegrable f volume 0 1 :=
    physicalOrderedThermal_intervalIntegrable n Q.sweepBf Q.sweepHf
      Q.sweep_bf_monotone Q.sweep_hf_monotone
  have hIntegral j (hj : j < K+1) : IntervalIntegrable f volume (z j) (z (j+1)) := by
    apply hfi.mono_set
    have hm : z j ≤ z (j+1) := by rw [hzNext]; linarith [hzPos j]
    have hmax : z (j+1) ≤ 1 := by
      rw [hzNext]
      have HH := mul_le_mul_of_nonneg_left (hzUpper j (by omega)) (show (0:ℝ) ≤ 2 by norm_num)
      nlinarith
    rw [uIcc_of_le hm,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (hzPos j).le hmax
  have Hpart j (hj : j∈Finset.range (K+1)) :
      (∫u in z j..z (j+1),f u) ≤
        Q.data.N^(-eta/2)*(Q.xs^4/W)*(A*(2:ℝ)^j) := by
    have hju : j ≤ K := by have := Finset.mem_range.mp hj; omega
    have hzTwo : 2*z j ≤ 1 := by
      have HH := mul_le_mul_of_nonneg_left (hzUpper j hju) (show (0:ℝ) ≤ 2 by norm_num)
      nlinarith
    have HH := hnDyad Q hsXs hsHigh hsmall hW1 (z j) (hzPos j) hzTwo
      ((mul_le_mul_of_nonneg_left Q.target_le_direct_test_working_scale hA.le).trans (hzLower j))
      (hzUpper j hju)
    have heff : 0 < actualIntermediateMassEffectiveScale W (z j):=
      actualIntermediateMassEffectiveScale_pos hW (hzPos j)
    have hWz : W ≤ z j:= (by nlinarith only [hA1,hW] : W ≤ A*W).trans (hzLower j)
    have heffLower : W ≤ actualIntermediateMassEffectiveScale W (z j):=by
      apply (pow_le_pow_iff_left₀ hW.le heff.le (by norm_num : (3:ℕ) ≠ 0)).mp
      rw [actualIntermediateMassEffectiveScale_cube hW.le (hzPos j).le]
      nlinarith only [mul_le_mul_of_nonneg_left hWz (sq_nonneg W)]
    have htarget : 0 < Q.xs^4*z j/(actualIntermediateMassEffectiveScale W (z j))^2:=by
      have := Q.hxs;positivity
    have HI0:=(div_le_iff₀ htarget).mp HH
    have Hnorm : Q.xs^4*z j/(actualIntermediateMassEffectiveScale W (z j))^2 ≤ Q.xs^4*z j/W^2:=
      div_le_div_of_nonneg_left (by have := Q.hxs;positivity) (sq_pos_of_pos hW)
        (pow_le_pow_left₀ hW.le heffLower 2)
    have HI:=HI0.trans (mul_le_mul_of_nonneg_left Hnorm (Real.rpow_nonneg Q.data.hN.le _))
    rw [hzNext]
    convert HI using 1
    dsimp [z]
    field_simp
    ring
  have Hsum := Finset.sum_le_sum (s:=Finset.range (K+1)) Hpart
  rw [intervalIntegral.sum_integral_adjacent_intervals hIntegral] at Hsum
  have HsumScalar : (∑j∈Finset.range (K+1),
      Q.data.N^(-eta/2)*(Q.xs^4/W)*(A*(2:ℝ)^j)) ≤
        Q.data.N^(-eta/2)*(Q.xs^4/W)*((K+1:ℕ)*B) := by
    have HH := Finset.sum_le_sum (s:=Finset.range (K+1)) (fun j hj=>
      mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num)
          (show j ≤ K by have := Finset.mem_range.mp hj; omega)) hA.le).trans hAK)
        (show 0 ≤ Q.data.N^(-eta/2)*(Q.xs^4/W) by have := Q.hxs; positivity))
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at HH
    calc
      _ ≤ (K+1:ℕ)*(Q.data.N^(-eta/2)*(Q.xs^4/W)*B) := HH
      _ = _ := by ring
  have hbigInt : IntervalIntegrable f volume (A*W) (z (K+1)) := by
    apply hfi.mono_set
    have hm : A*W ≤ z (K+1) := hzLower _
    rw [uIcc_of_le hm,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (mul_pos hA hW).le (hzLast.trans hbandSmall)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (A*W) (z (K+1)))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu01 : u∈Icc (0:ℝ) 1 := ⟨(mul_pos hA hW).le.trans hu.1.le,hu.2.trans (hzLast.trans hbandSmall)⟩
    change 0 ≤ Q.shiftedNativeModel.thermal u
    exact Q.shiftedNativeModel.thermal_nonneg ⟨hu.1.trans_le' (mul_pos hA hW).le, hu01.2⟩
  have Hmono := intervalIntegral.integral_mono_interval (a:=A*W) (b:=B*W)
    (c:=A*W) (d:=z (K+1)) le_rfl (mul_le_mul_of_nonneg_right hAB hW.le) hBandLast hnonneg hbigInt
  have Hcover : (∫u in A*W..B*W,f u) ≤
      Q.data.N^(-eta/2)*(Q.xs^4/W)*((K+1:ℕ)*B) := by
    have Hsum' : (∫u in A*W..z (K+1),f u) ≤
        (∑j∈Finset.range (K+1),
          Q.data.N^(-eta/2)*(Q.xs^4/W)*(A*(2:ℝ)^j)) := by
      simpa only [z,pow_zero,mul_one] using Hsum
    apply Hmono.trans
    exact Hsum'.trans HsumScalar
  have Hcoef : ((K+1:ℕ)*B)*Q.data.N^(-eta/2) ≤ Q.data.N^(-(3*eta/8)) := by
    simpa only [ActualHighWallData.N,mul_one,one_mul,neg_div] using hnCoef
  have HH := mul_le_mul_of_nonneg_right Hcoef (show 0 ≤ Q.xs^4/W by have := Q.hxs; positivity)
  apply Hcover.trans
  convert HH using 1
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
