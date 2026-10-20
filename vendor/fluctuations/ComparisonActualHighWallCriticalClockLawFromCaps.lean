module

public import ComparisonLocalTemperatureClockLawIdentification
public import ComparisonQuantileLinearLimit
public import ComparisonNativeActualOriginalMassMismatch

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 10000000

theorem comparison_local_clock_laws_ae_of_cdf_caps_and_l1
    (q r : ℕ→ℝ→ℝ) (x : ℕ→ℝ) (U V : ℝ→ℝ)
    (hq : ∀n,MonotoneOn (q n) (Icc (0:ℝ) 1))
    (hr : ∀n,MonotoneOn (r n) (Icc (0:ℝ) 1))
    (hqb : ∀n u,u∈Icc (0:ℝ) 1 → q n u∈Icc (0:ℝ) 1)
    (hrb : ∀n u,u∈Icc (0:ℝ) 1 → r n u∈Icc (0:ℝ) 1)
    (hx : ∀n,0<x n) (hxlim : Tendsto x atTop (𝓝 0))
    (hVm : Monotone V)
    (hU : ∀t : ℝ,Tendsto (fun n=>(quantileMassProfile (q n) (hqb n)).val
      (x n*t)/x n) atTop (𝓝 (U t)))
    (hV : ∀t : ℝ,Tendsto (fun n=>(quantileMassProfile (r n) (hrb n)).val
      (x n*t)/x n) atTop (𝓝 (V t)))
    (hqc : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧ ∀ᶠn in atTop,
      (quantileMassProfile (q n) (hqb n)).val (x n*R)≤A*x n)
    (hrc : ∀R : ℝ,0<R→∃A : ℝ,0≤A ∧ ∀ᶠn in atTop,
      (quantileMassProfile (r n) (hrb n)).val (x n*R)≤A*x n)
    (hL1 : ∀C : ℝ,1≤C→Tendsto (fun n=>(∫u in 0..C*x n,
      |q n u-r n u|)/(x n)^2) atTop (𝓝 0)) :
    U=ᵐ[volume] V := by
  apply comparison_actual_local_temperature_clock_laws_ae_identified
    q r 1 x U V zero_lt_one hq hr hqb hrb hx hVm
    (by simpa only [one_mul] using hU) hV
  intro R hR
  obtain ⟨Aq,hAq0,Hq⟩:=hqc R hR
  obtain ⟨Ar,hAr0,Hr⟩:=hrc R hR
  let C:=max Aq Ar+1
  have hAq : Aq<C := by dsimp only [C]; linarith [le_max_left Aq Ar]
  have hAr : Ar<C := by dsimp only [C]; linarith [le_max_right Aq Ar]
  have hC : 0<C := by dsimp only [C]; linarith [le_max_left Aq Ar]
  have hC1 : 1≤C := by dsimp only [C]; linarith [le_max_left Aq Ar]
  let v : ℕ→ℝ:=fun n=>min (C*x n) 1
  have hv : ∀n,v n∈Icc (0:ℝ) 1 := fun n=>
    ⟨le_min (mul_nonneg hC.le (hx n).le) zero_le_one,min_le_right _ _⟩
  have Hunit := (hxlim.const_mul C).eventually
    (eventually_le_nhds (show C*(0:ℝ)<1 by simp))
  have Hcut : ∀ᶠn in atTop,x n*R<q n (v n) ∧ x n*R<r n (v n) := by
    filter_upwards [Hq,Hr,Hunit] with n hnq hnr hnunit
    have hveq : v n=C*x n := min_eq_left hnunit
    constructor
    · by_contra hn
      have HC:=comparison_quantile_cdf_ge_of_clock_le (q n) (hq n) (hqb n)
        (hv n) (le_of_not_gt hn)
      rw [hveq] at HC
      have Hlt:=mul_lt_mul_of_pos_right hAq (hx n)
      exact (not_lt_of_ge HC) (hnq.trans_lt (by simpa only [mul_comm] using Hlt))
    · by_contra hn
      have HC:=comparison_quantile_cdf_ge_of_clock_le (r n) (hr n) (hrb n)
        (hv n) (le_of_not_gt hn)
      rw [hveq] at HC
      have Hlt:=mul_lt_mul_of_pos_right hAr (hx n)
      exact (not_lt_of_ge HC) (hnr.trans_lt (by simpa only [mul_comm] using Hlt))
  refine ⟨v,hv,?_,?_⟩
  · simpa only [one_mul] using Hcut
  · apply (hL1 C hC1).congr'
    filter_upwards [Hunit] with n hnunit
    have hveq : v n=C*x n := min_eq_left hnunit
    have hvunit : C*x n∈Icc (0:ℝ) 1 := ⟨mul_nonneg hC.le (hx n).le,hnunit⟩
    rw [hveq]
    simp only [div_one]
    exact congrArg (fun z : ℝ=>z/(x n)^2)
      (comparison_original_retained_integral_eq_interval hvunit
        (fun u=>|q n u-r n u|)).symm

end OAI.SKFluctuations.LaplaceWindowFormalization
