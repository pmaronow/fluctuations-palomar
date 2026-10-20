module

public import ComparisonNativeActualHighMassPhysicalDyad
public import ComparisonNativeCavityRadiusGoodPoint

@[expose] public section

noncomputable section
set_option maxHeartbeats 13000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_minimum_strong_high_mass_band
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D Cs A B : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hA : 0 < A) (hAB : A ≤ B) (hAouter : 2*cu*(Az+1) ≤ A) :
    ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (T H : ℝ), (∀u,M.b u=T) → (∀u,M.h u=H) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 → 2*B*M.canonicalDirectTestBandScale ≤ 1 →
        (∫u in A*M.canonicalDirectTestBandScale..B*M.canonicalDirectTestBandScale,
          orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2) ≤
          M.context.N^(-(3*actualMassSavingExponent m delta/8))*(M.xs^4/M.canonicalDirectTestBandScale) := by
  have hratio : 1 ≤ B/A := (one_le_div hA).mpr hAB
  obtain ⟨K,hKlo,hKhi⟩ := exists_nat_pow_near hratio (show (1:ℝ) < 2 by norm_num)
  have hAK : A*(2:ℝ)^K ≤ B := by
    simpa only [mul_comm] using (le_div_iff₀ hA).mp hKlo
  have hBK : B < A*(2:ℝ)^(K+1) := by
    have HH := (div_lt_iff₀ hA).mp hKhi
    nlinarith
  have Hdyad := eventually_actual_minimum_strong_high_mass_dyad
    (D:=D) (Cs:=Cs) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt hCs hA hAouter
  let eta := actualMassSavingExponent m delta
  have heta : 0 < eta := actualMassSavingExponent_pos hm hdelta
  have Hcoefficient := (tendsto_add_atTop_nat 1).eventually
    (eventually_coefficient_rpow_le (c:=(K+1:ℕ)*B) (d:=1)
      (q:=-eta/2) (r:=-(3*eta/8)) zero_lt_one (by linarith))
  filter_upwards [Hdyad,Hcoefficient] with n hnDyad hnCoef
  intro M T H hb hh hsmall hW1 hbandSmall
  let W := M.canonicalDirectTestBandScale
  let z := fun j : ℕ=>A*(2:ℝ)^j*W
  let f := fun u=>orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2
  have hW : 0 < W := M.canonical_direct_test_band_pos
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
    simpa only [z,mul_one,one_mul,mul_assoc,mul_left_comm,mul_comm] using HH
  have hzLast : z (K+1) ≤ 2*B*W := by
    rw [hzNext]
    have HH := mul_le_mul_of_nonneg_left (hzUpper K le_rfl) (show (0:ℝ) ≤ 2 by norm_num)
    convert HH using 1
    ring
  have hBandLast : B*W ≤ z (K+1) := mul_le_mul_of_nonneg_right hBK.le hW.le
  have hfi := native_comparison_thermal_intervalIntegrable M
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
        M.context.N^(-eta/2)*(M.xs^4/W)*(A*(2:ℝ)^j) := by
    have hju : j ≤ K := by have := Finset.mem_range.mp hj; omega
    have hzTwo : 2*z j ≤ 1 := by
      have HH := mul_le_mul_of_nonneg_left (hzUpper j hju) (show (0:ℝ) ≤ 2 by norm_num)
      nlinarith
    have HH := hnDyad M T H hb hh hsmall hW1 (z j) (hzPos j) hzTwo (hzLower j)
    have htarget : 0 < M.xs^4*z j/W^2 := by have := M.hxs; positivity
    have HI := (div_le_iff₀ htarget).mp HH
    rw [hzNext]
    convert HI using 1
    dsimp [z]
    field_simp
    ring
  have Hsum := Finset.sum_le_sum (s:=Finset.range (K+1)) Hpart
  rw [intervalIntegral.sum_integral_adjacent_intervals hIntegral] at Hsum
  have HsumScalar : (∑j∈Finset.range (K+1),
      M.context.N^(-eta/2)*(M.xs^4/W)*(A*(2:ℝ)^j)) ≤
        M.context.N^(-eta/2)*(M.xs^4/W)*((K+1:ℕ)*B) := by
    have HH := Finset.sum_le_sum (s:=Finset.range (K+1)) (fun j hj=>
      mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num)
          (show j ≤ K by have := Finset.mem_range.mp hj; omega)) hA.le).trans hAK)
        (show 0 ≤ M.context.N^(-eta/2)*(M.xs^4/W) by have := M.hxs; positivity))
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using HH
  have hbigInt : IntervalIntegrable f volume (A*W) (z (K+1)) := by
    apply hfi.mono_set
    have hm : A*W ≤ z (K+1) := hzLower _
    rw [uIcc_of_le hm,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (mul_pos hA hW).le (hzLast.trans hbandSmall)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (A*W) (z (K+1)))] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu01 : u∈Icc (0:ℝ) 1 := ⟨(mul_pos hA hW).le.trans hu.1.le,hu.2.trans (hzLast.trans hbandSmall)⟩
    have hr := comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha u
    have HD := M.cavityRadiusPointDefect_nonneg hr
    change 0 ≤ f u
    simpa only [f,NativeOverlapMinimum.cavityRadiusPointDefect,comparisonSweepQuantile_mass_spec
      M.context.hc M.context.hk M.context.hkc M.context.hm M.context.hM M.alpha hu01] using HD
  have Hmono := intervalIntegral.integral_mono_interval (a:=A*W) (b:=B*W)
    (c:=A*W) (d:=z (K+1)) le_rfl (mul_le_mul_of_nonneg_right hAB hW.le) hBandLast hnonneg hbigInt
  have Hcover : (∫u in A*W..B*W,f u) ≤
      M.context.N^(-eta/2)*(M.xs^4/W)*((K+1:ℕ)*B) := by
    have Hsum' : (∫u in A*W..z (K+1),f u) ≤
        (∑j∈Finset.range (K+1),
          M.context.N^(-eta/2)*(M.xs^4/W)*(A*(2:ℝ)^j)) := by
      simpa only [z,pow_zero,mul_one] using Hsum
    apply Hmono.trans
    exact Hsum'.trans HsumScalar
  have Hcoef : ((K+1:ℕ)*B)*M.context.N^(-eta/2) ≤ M.context.N^(-(3*eta/8)) := by
    simpa only [NativeOverlapContext.N,mul_one,one_mul,neg_div] using hnCoef
  have HH := mul_le_mul_of_nonneg_right Hcoef (show 0 ≤ M.xs^4/W by have := M.hxs; positivity)
  apply Hcover.trans
  convert HH using 1
  ring

end OAI.SKFluctuations.LaplaceWindowFormalization
