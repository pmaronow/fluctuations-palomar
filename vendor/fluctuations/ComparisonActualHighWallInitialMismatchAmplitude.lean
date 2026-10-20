module

public import ComparisonActualHighWallHighMassNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 8000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem full_radius_le_source_envelope
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) {u : ℝ} (hu : u∈Icc (0:ℝ) 1) :
    M.data.wallRadius M.alpha u ≤ (Az+1/cl)*(M.xs+u) := by
  have H := M.high_radius_le_threshold_add_mass hcl hu
  apply H.trans
  have H' : M.z+u/cl ≤ Az*M.xs+u/cl := by linarith [M.hzxs]
  apply H'.trans
  have HE : (Az+1/cl)*(M.xs+u)=Az*M.xs+u/cl+Az*u+(1/cl)*M.xs := by ring
  rw [HE]
  linarith [mul_nonneg hAz hu.1,mul_nonneg (one_div_nonneg.mpr hcl.le) M.hxs.le]

end ActualHighWallOverlapMinimum

theorem eventually_actual_high_wall_initial_mismatch_amplitude
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀u∈Ioc (0:ℝ) 1,
      (orderedPathS (n+1) M.bf M.hf u-M.data.wallRadius M.alpha u)^2 ≤ K*(M.xs+u)^2 := by
  obtain ⟨B,hB,Hamp⟩ := eventually_actual_high_wall_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cr := Az+1/cl
  let K := 2*(B+Cr^2)
  have hK : 0 < K := by dsimp only [K]; nlinarith [sq_nonneg Cr]
  refine ⟨K,hK,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hamp] with n hn
  intro M u hu
  have hui : u∈Icc (0:ℝ) 1 := Ioc_subset_Icc_self hu
  have HB := hn M u hu
  have HS := (orderedPath_SK_bounds (n+1) M.data.hn M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) hu).2.2.1
  have HR := M.full_radius_le_source_envelope hcl hAz hui
  have HR0 := M.data.hrbounds.1.le.trans (M.data.wallRadius_bounds M.alpha u).1
  have HRsq := pow_le_pow_left₀ HR0 HR 2
  dsimp only [K,Cr] at HRsq ⊢
  rw [mul_pow] at HRsq
  nlinarith only [HB,HS,HRsq,
    sq_nonneg (orderedPathS (n+1) M.bf M.hf u+M.data.wallRadius M.alpha u)]

end OAI.SKFluctuations.LaplaceWindowFormalization
