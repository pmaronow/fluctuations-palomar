module

public import SKProof.Port.ComparisonActualOriginalQInitialMassMismatch

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
namespace ActualThetaZeroOverlapMinimum

theorem eventually_actual_initial_mismatch_amplitude_original_q
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.data.s ≤ 1/4 → M.data.s ≤ M.xs → ∀u∈Ioc (0:ℝ) 1,
      (orderedPathS (n+1) M.sweepBf M.sweepHf u-M.sweepRadius u)^2 ≤ K*(M.xs+u)^2 := by
  obtain ⟨B,hB,Hamp⟩:=eventually_actual_B_normalized_original_q (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cr:=Az+1/cl
  let K:=2*(B+Cr^2)
  have hK : 0<K:=by dsimp only [K];nlinarith [sq_nonneg Cr]
  refine ⟨K,hK,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hamp] with n hn
  intro M hs hsxs u hu
  have hui : u∈Icc (0:ℝ) 1:=Ioc_subset_Icc_self hu
  have HB:=hn M hs hsxs u hu
  have HS:=M.actual_thermal_nonneg_on_unit hui
  have HR:=M.inverse_radius_le_source_mass hcl hAz hui
  have HR0 : 0 ≤ M.sweepRadius u := (M.sweepRadius_bounds0 u).1
  have hCr : 0≤Cr:=add_nonneg hAz (one_div_nonneg.mpr hcl.le)
  have henv : 0≤Cr*(M.xs+u):=mul_nonneg hCr (add_nonneg M.hxs.le hui.1)
  have HRsq:=pow_le_pow_left₀ HR0 HR 2
  dsimp only [K,Cr] at HRsq ⊢
  rw [mul_pow] at HRsq
  nlinarith only [HB,HS,HRsq,sq_nonneg (orderedPathS (n+1) M.sweepBf M.sweepHf u+M.sweepRadius u)]

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
