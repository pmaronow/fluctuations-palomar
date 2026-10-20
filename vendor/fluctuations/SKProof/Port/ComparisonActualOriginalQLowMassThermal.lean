module

public import SKProof.Port.ComparisonActualOriginalQInitialMassMismatch

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace ActualThetaZeroOverlapMinimum

theorem eventually_actual_low_mass_thermal_original_q
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.data.s ≤ 1/4 → M.data.s ≤ M.xs → ∀v∈Icc (0:ℝ) 1,
      (∫u in 0..v,orderedPathB (n+1) M.sweepBf M.sweepHf u-(orderedPathS (n+1) M.sweepBf M.sweepHf u)^2) ≤
        K*(M.xs+v)^2*v := by
  obtain ⟨K,hK,Hamp⟩:=eventually_actual_B_normalized_original_q (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hamp] with n hn
  intro M hs hsxs v hv
  have hi := M.original_thermal_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hv.2)
  have H:=intervalIntegral.integral_mono_ae_restrict hv.1 hi intervalIntegrable_const
    (by
      filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae (volume.ae_ne (0:ℝ))]
        with u hu hu0
      have HB:=hn M hs hsxs u ⟨lt_of_le_of_ne hu.1 hu0.symm,hu.2.trans hv.2⟩
      have Hsq:=pow_le_pow_left₀ (add_nonneg M.hxs.le hu.1)
        (by linarith only [hu.2] : M.xs+u ≤ M.xs+v) 2
      have Hmul:=mul_le_mul_of_nonneg_left Hsq hK.le
      exact (sub_le_self _ (sq_nonneg _)).trans (HB.trans Hmul))
  simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,mul_comm v] using H

theorem eventually_actual_initial_wall_thermal_original_q
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.data.s ≤ 1/4 → M.data.s ≤ M.xs →
      let L:=max M.data.U M.data.s
      (∫u in 0..min (8*L) 1,orderedPathB (n+1) M.sweepBf M.sweepHf u-
        (orderedPathS (n+1) M.sweepBf M.sweepHf u)^2) ≤ 8*K*(M.xs+8*L)^2*L := by
  obtain ⟨K,hK,Hlow⟩:=eventually_actual_low_mass_thermal_original_q (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [Hlow] with n hn
  intro M hs hsxs
  dsimp only
  let L:=max M.data.U M.data.s
  let v:=min (8*L) 1
  have hL : 0<L:=M.data.hU.trans_le (le_max_left _ _)
  have hv : v∈Icc (0:ℝ) 1:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have Hv:=hn M hs hsxs v hv
  have hsq:=pow_le_pow_left₀ (add_nonneg M.hxs.le hv.1)
    (by have H:=min_le_left (8*L) 1;linarith : M.xs+v ≤ M.xs+8*L) 2
  have Hmul:=mul_le_mul (mul_le_mul_of_nonneg_left hsq hK.le) (min_le_left (8*L) 1)
    hv.1 (mul_nonneg hK.le (sq_nonneg _))
  exact Hv.trans (by convert Hmul using 1; ring)

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
