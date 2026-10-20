module

public import ComparisonNativeActualHighMassPhysicalBand

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators

theorem native_high_tail_integral_le_dyadic_budget
    {f : ℝ→ℝ} (hf : IntervalIntegrable f volume 0 1)
    (hf0 : ∀u∈Icc (0:ℝ) 1,0≤f u)
    {lo A : ℝ} (hlo : 0<lo) (hlohalf : lo≤1/2) (hA : 0≤A)
    (hdyad : ∀v : ℝ,0<v → 2*v≤1 → lo≤v → (∫u in v..2*v,f u)≤A*v) :
    (∫u in lo..1,f u)≤2*A := by
  have hratio : 1≤(1/2:ℝ)/lo := (one_le_div hlo).mpr hlohalf
  obtain ⟨K,hKlo,hKhi⟩:=exists_nat_pow_near hratio (show (1:ℝ)<2 by norm_num)
  let z:=fun j : ℕ=>lo*(2:ℝ)^j
  have hzPos j : 0<z j:=by dsimp [z];positivity
  have hzNext j : z (j+1)=2*z j := by dsimp [z];rw [pow_succ];ring
  have hzK : z K≤1/2 := by
    have H:=(le_div_iff₀ hlo).mp hKlo
    simpa only [z,mul_comm] using H
  have hzLower j : lo≤z j := by
    have H:=mul_le_mul_of_nonneg_left (one_le_pow₀ (by norm_num : (1:ℝ)≤2) : (1:ℝ)≤(2:ℝ)^j) hlo.le
    simpa only [z,mul_one] using H
  have hzUpper j (hj : j≤K) : z j≤1/2 := by
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj) hlo.le).trans hzK
  have hlastLower : (1/2:ℝ)≤z (K+1) := by
    have H:=(div_lt_iff₀ hlo).mp hKhi
    simpa only [z,mul_comm] using H.le
  have hlastUpper : z (K+1)≤1 := by rw [hzNext];linarith only [hzK]
  have hi j (hj : j<K+1) : IntervalIntegrable f volume (z j) (z (j+1)) := by
    apply hf.mono_set
    rw [uIcc_of_le (by rw [hzNext];linarith [hzPos j]),uIcc_of_le zero_le_one]
    have Hupper : z (j+1)≤1 := by rw [hzNext];linarith [hzUpper j (by omega)]
    exact Icc_subset_Icc (hzPos j).le Hupper
  have Hsum:=Finset.sum_le_sum (s:=Finset.range (K+1)) (fun j hj=>
    hdyad (z j) (hzPos j) (by linarith [hzUpper j (by have :=Finset.mem_range.mp hj;omega)]) (hzLower j))
  simp_rw [←hzNext] at Hsum
  rw [intervalIntegral.sum_integral_adjacent_intervals hi] at Hsum
  have Hgeom : (∑j∈Finset.range (K+1),z j)≤1 := by
    have H:=geom_sum_mul (2:ℝ) (K+1)
    have HE : (∑j∈Finset.range (K+1),z j)=z (K+1)-lo := by
      simp only [z]
      rw [←Finset.mul_sum]
      have Hsum2 : (∑j∈Finset.range (K+1),(2:ℝ)^j)=(2:ℝ)^(K+1)-1 := by
        norm_num at H
        exact H
      rw [Hsum2]
      ring
    rw [HE]
    linarith only [hlastUpper,hlo]
  have Hfirst : (∫u in lo..1/2,f u)≤A := by
    have hin : IntervalIntegrable f volume (z 0) (z (K+1)):=by
      apply hf.mono_set
      rw [uIcc_of_le (by simpa only [z,pow_zero,mul_one] using (hzLower (K+1))),uIcc_of_le zero_le_one]
      exact Icc_subset_Icc (hzPos 0).le hlastUpper
    have hin' : IntervalIntegrable f volume lo (z (K+1)) := by
      simpa only [z,pow_zero,mul_one] using hin
    have hnonneg : 0≤ᵐ[volume.restrict (Ioc lo (z (K+1)))] f := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact hf0 u ⟨hlo.le.trans hu.1.le,hu.2.trans hlastUpper⟩
    have Hmono:=intervalIntegral.integral_mono_interval le_rfl hlohalf hlastLower hnonneg hin'
    have Hscalar:=mul_le_mul_of_nonneg_left Hgeom hA
    simp only [z,pow_zero,mul_one,←Finset.mul_sum] at Hsum
    have Hscalar' : A*(lo*∑j∈Finset.range (K+1),(2:ℝ)^j)≤A := by
      simpa only [z,←Finset.mul_sum,mul_one] using Hscalar
    exact Hmono.trans (Hsum.trans Hscalar')
  have Hlast:=hdyad (1/2) (by norm_num) (by norm_num) hlohalf
  have hleft : IntervalIntegrable f volume lo (1/2) := by
    apply hf.mono_set
    rw [uIcc_of_le hlohalf,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hlo.le (by norm_num)
  have hright : IntervalIntegrable f volume (1/2) 1 := by
    apply hf.mono_set
    rw [uIcc_of_le (by norm_num : (1/2:ℝ)≤1),uIcc_of_le zero_le_one]
    exact Icc_subset_Icc (by norm_num) le_rfl
  rw [←intervalIntegral.integral_add_adjacent_intervals hleft hright]
  norm_num at Hlast
  linarith only [Hfirst,Hlast,hA]

end OAI.SKFluctuations.LaplaceWindowFormalization
