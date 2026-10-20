module

public import ComparisonActualHighWallStarSelectionDistinct

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 7000000

theorem eventually_actual_high_wall_floor_thermal_on_band
    (Bclock : ℝ) {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃K : ℝ,0 < K ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀p : M.Potential,∀lo hi : ℝ,M.data.s≤lo → lo≤hi → hi≤1 →
      (∫u in Ioo lo hi,p.positiveMassMask u*
        (orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2))≤
        K*(M.xs+hi)^2*M.data.N^(-delta)*comparisonSmallMass M.data.N M.data.E := by
  obtain ⟨K,hK,Hamp⟩ := eventually_actual_high_wall_B_normalized (D:=D)
    Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨K,hK,?_⟩
  filter_upwards [(tendsto_add_atTop_nat 1).eventually Hamp] with n hn
  intro M p lo hi hlo hlohi hhi
  let F := fun u=>orderedPathB (n+1) M.bf M.hf u-(orderedPathS (n+1) M.bf M.hf u)^2
  let C := K*(M.xs+hi)^2
  have hsub : Ioo lo hi⊆Icc (0:ℝ) 1 :=
    fun u hu=>⟨M.data.hs.1.le.trans (hlo.trans hu.1.le),hu.2.le.trans hhi⟩
  have hiF : IntegrableOn F (Ioo lo hi) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (physicalOrderedThermal_intervalIntegrable n M.bf M.hf
        (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha))).mono_set hsub
  have hmaskmeas : Measurable p.positiveMassMask := by
    rw [p.positiveMassMask_extended]
    apply measurable_const.indicator
    exact measurableSet_lt measurable_const
      (p.starExtendedH_continuous.comp (M.data.wallRadius_lipschitz M.alpha).continuous).measurable
  have hmask01 u : p.positiveMassMask u=0 ∨ p.positiveMassMask u=1 := by
    dsimp [ActualHighWallOverlapMinimum.Potential.positiveMassMask]
    by_cases h:u∈comparisonCalibrationFloor p.H (M.data.wallRadius M.alpha) <;> simp [h]
  have himul : IntegrableOn (fun u=>p.positiveMassMask u*F u) (Ioo lo hi) := by
    apply hiF.bdd_mul (c:=(1:ℝ)) hmaskmeas.aestronglyMeasurable.restrict
    filter_upwards [] with u
    rcases hmask01 u with h|h <;> simp [h]
  obtain ⟨himask,hmass⟩ := p.positiveMassMask_on_band hlo hlohi hhi
  have hiC : IntegrableOn (fun u=>p.positiveMassMask u*C) (Ioo lo hi) := himask.mul_const C
  have Hbound : (∫u in Ioo lo hi,p.positiveMassMask u*F u)≤
      ∫u in Ioo lo hi,p.positiveMassMask u*C := by
    apply integral_mono_ae himul hiC
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    have hum : u∈Ioc (0:ℝ) 1 := ⟨M.data.hs.1.trans_le (hlo.trans hu.1.le),hu.2.le.trans hhi⟩
    have H := hn M u hum
    have Hscale := pow_le_pow_left₀ (add_pos M.hxs hum.1).le
      (add_le_add_right hu.2.le M.xs) 2
    have Hupper : F u≤C :=
      (sub_le_self _ (sq_nonneg _)).trans
        (H.trans (mul_le_mul_of_nonneg_left Hscale hK.le))
    have hmask0 : 0≤p.positiveMassMask u := by
      rcases hmask01 u with h|h <;> simp [h]
    exact mul_le_mul_of_nonneg_left Hupper hmask0
  rw [integral_mul_const] at Hbound
  have Hmass := mul_le_mul_of_nonneg_right hmass (show 0≤C from by dsimp [C];positivity)
  exact Hbound.trans (Hmass.trans_eq (by dsimp [C];ring))

end OAI.SKFluctuations.LaplaceWindowFormalization
