module

public import WallEnvelope

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.WallSweep

open MeasureTheory Filter Set
open scoped Topology NNReal

theorem minimum_sweep_logarithmic_bound {α : Type*} (J : ℝ → α → ℝ)
    (v : ℝ → ℝ) {tau A B : ℝ} (htau : 0 < tau) (htau1 : tau ≤ 1)
    (hA : 0 ≤ A) {K : ℝ≥0}
    (hv : LipschitzOnWith K v (uIcc (0 : ℝ) 1))
    (hmin : ∀ t ∈ Ioo tau 1,
      ∃ z, J t z = v t ∧ (∀ᶠ x in 𝓝 t, v x ≤ J x z) ∧
        ∃ d, HasDerivAt (fun x => J x z) d t ∧ d ≤ A + B * t⁻¹) :
    v 1 - v 0 ≤ A + B * (-Real.log tau) + (K : ℝ) * tau := by
  have hsubset : uIcc tau 1 ⊆ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le htau1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc htau.le le_rfl
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume tau 1 := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_id.inv₀
    intro t ht
    rw [uIcc_of_le htau1] at ht
    exact (htau.trans_le ht.1).ne'
  have hg : IntervalIntegrable (fun t : ℝ => A + B * t⁻¹) volume tau 1 :=
    intervalIntegrable_const.add (hinv.const_mul B)
  have hlarge := minimum_sub_le_integral htau1 J v
    (fun t => A + B * t⁻¹) (hv.mono hsubset) hmin hg
  have hintegral : (∫ t : ℝ in tau..1, A + B * t⁻¹) =
      (1 - tau) * A + B * (-Real.log tau) := by
    rw [intervalIntegral.integral_add intervalIntegrable_const (hinv.const_mul B),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      integral_inv_of_pos htau (by norm_num)]
    simp only [one_div, Real.log_inv, smul_eq_mul]
  rw [hintegral] at hlarge
  have htau_mem : tau ∈ uIcc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact ⟨htau.le, htau1⟩
  have hzero_mem : (0 : ℝ) ∈ uIcc (0 : ℝ) 1 := left_mem_uIcc
  have hsmall := (hv.dist_le_mul tau htau_mem 0 hzero_mem)
  simp only [Real.dist_eq, sub_zero, abs_of_pos htau] at hsmall
  have hsmall' := (le_abs_self (v tau - v 0)).trans hsmall
  nlinarith [mul_nonneg htau.le hA]

end OAI.SKFluctuations.WallSweep
