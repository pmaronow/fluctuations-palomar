module

public import ComparisonActualHighOnlyLowMassThermal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem Potential.initial_floor_thermal_le
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (P : M.Potential) {v K : ℝ} (hv : v∈Icc (0:ℝ) 1) (hK : 0 ≤ K)
    (hamp : ∀u∈Ioc (0:ℝ) v,orderedPathB (n+1) M.bf M.hf u ≤ K*(M.xs+u)^2) :
    (∫u in 0..v,P.positiveMassMask u*(orderedPathB (n+1) M.bf M.hf u-
      (orderedPathS (n+1) M.bf M.hf u)^2)) ≤
      K*(M.xs+v)^2*(M.data.s+M.data.N^(-delta)*M.data.U) := by
  let f:=fun u=>orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2
  have hiF:=M.original_thermal_intervalIntegrable.mono_set (by
    rw [uIcc_of_le hv.1,uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hv.2)
  have hiMask : IntervalIntegrable P.positiveMassMask volume 0 v :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mpr
      (P.positiveMassMask_integrable.mono_set (Icc_subset_Icc le_rfl hv.2))
  have hmask u : P.positiveMassMask u∈Icc (0:ℝ) 1 := by
    unfold Potential.positiveMassMask
    by_cases hu : M.R u∈P.positiveRadiusSet
    · rw [indicator_of_mem hu];norm_num
    · rw [indicator_of_notMem hu];norm_num
  have hiProd : IntervalIntegrable (fun u=>P.positiveMassMask u*f u) volume 0 v := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mpr
    exact ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mp hiF).bdd_mul
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hv.1).mp hiMask).aestronglyMeasurable
      (ae_of_all _ (fun u=>by
        rw [Real.norm_eq_abs,abs_of_nonneg (hmask u).1]
        exact (hmask u).2))
  have Hpoint : ∀ᵐu∂volume.restrict (Icc (0:ℝ) v),
      P.positiveMassMask u*f u ≤ (K*(M.xs+v)^2)*P.positiveMassMask u := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,ae_restrict_of_ae (volume.ae_ne (0:ℝ))]
      with u hu hu0
    have HB:=hamp u ⟨lt_of_le_of_ne hu.1 hu0.symm,hu.2⟩
    have Hsq:=pow_le_pow_left₀ (add_nonneg M.hxs.le hu.1)
      (by linarith only [hu.2] : M.xs+u ≤ M.xs+v) 2
    have HF : f u ≤ K*(M.xs+v)^2 :=
      (sub_le_self _ (sq_nonneg _)).trans (HB.trans (mul_le_mul_of_nonneg_left Hsq hK))
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left HF (hmask u).1
  have HI:=intervalIntegral.integral_mono_ae_restrict hv.1 hiProd (hiMask.const_mul _) Hpoint
  rw [intervalIntegral.integral_const_mul] at HI
  have Hmask : (∫u in 0..v,P.positiveMassMask u) ≤ M.data.s+M.data.N^(-delta)*M.data.U := by
    rw [intervalIntegral.integral_of_le hv.1,←integral_Icc_eq_integral_Ioc]
    exact (setIntegral_mono_set P.positiveMassMask_integrable
      (ae_of_all _ (fun u=>(hmask u).1))
      (Eventually.of_forall (Icc_subset_Icc le_rfl hv.2))).trans P.positiveMassMask_mass_le
  exact HI.trans (mul_le_mul_of_nonneg_left Hmask (mul_nonneg hK (sq_nonneg _)))

theorem eventually_actual_high_only_initial_floor_thermal
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.data.s ≤ 1/4 → M.data.s ≤ M.xs → ∀P : M.Potential,∀v∈Icc (0:ℝ) 1,
      (∫u in 0..v,P.positiveMassMask u*(orderedPathB (n+1) M.bf M.hf u-
        (orderedPathS (n+1) M.bf M.hf u)^2)) ≤
        K*(M.xs+v)^2*(M.data.s+M.data.N^(-delta)*M.data.U) := by
  obtain ⟨K,hK,Hamp⟩:=eventually_actual_high_only_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hamp] with n hn
  intro M hs hsxs P v hv
  exact P.initial_floor_thermal_le hv hK.le
    (fun u hu=>hn M hs hsxs u ⟨hu.1,hu.2.trans hv.2⟩)

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
