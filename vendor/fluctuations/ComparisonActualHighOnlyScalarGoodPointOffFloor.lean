module

public import ComparisonActualHighOnlyOriginalFloorMass
public import ComparisonNativeActualScalarGoodPointOffFloor

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
namespace ActualHighOnlyOverlapMinimum
set_option maxHeartbeats 6000000

theorem Potential.exists_scalar_good_point_off_floor
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    {M : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    (p : M.Potential) (f : ℝ→ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b*M.xs ≤ 1)
    (hf : IntervalIntegrable f volume 0 (b*M.xs))
    (hsmall : (∫u in 0..b*M.xs,|f u|) <
      M.xs^3*((b-a)*M.xs-(M.data.s+M.context.N^(-delta)*M.context.U)))
    (P : ℝ→Prop) (hP : ∀ᵐu,u∈Ioo (a*M.xs) (b*M.xs) → P u) :
    ∃u∈Ioo (a*M.xs) (b*M.xs),p.H (M.R u) ≤ 0 ∧ |f u| ≤ M.xs^3 ∧ P u := by
  have hax : 0 ≤ a*M.xs := mul_nonneg ha M.hxs.le
  have hband : a*M.xs < b*M.xs := mul_lt_mul_of_pos_right hab M.hxs
  have hbx : 0 ≤ b*M.xs := hax.trans hband.le
  have hsub : Ioo (a*M.xs) (b*M.xs) ⊆ Icc (0:ℝ) 1 :=
    fun u hu=>⟨hax.trans hu.1.le,hu.2.le.trans hb⟩
  have hsubb : Ioo (a*M.xs) (b*M.xs) ⊆ Icc (0:ℝ) (b*M.xs) :=
    fun u hu=>⟨hax.trans hu.1.le,hu.2.le⟩
  have hfi0 : IntegrableOn (fun u=>|f u|) (Icc (0:ℝ) (b*M.xs)) :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hbx).mp hf).abs
  have hfi : IntegrableOn (fun u=>|f u|) (Ioo (a*M.xs) (b*M.xs)) :=
    hfi0.mono_set hsubb
  have hmask0 u : 0 ≤ p.positiveMassMask u := by
    dsimp only [Potential.positiveMassMask]
    by_cases H:M.R u∈p.positiveRadiusSet <;> simp [H]
  have hmass : (∫u in Ioo (a*M.xs) (b*M.xs),p.positiveMassMask u) ≤
      (M.data.s+M.context.N^(-delta)*M.context.U) :=
    (setIntegral_mono_set p.positiveMassMask_integrable
      (Eventually.of_forall hmask0) (Eventually.of_forall hsub)).trans p.positiveMassMask_mass_le
  have Hup : (∫u in Ioo (a*M.xs) (b*M.xs),|f u|) ≤ ∫u in 0..b*M.xs,|f u| := by
    rw [←integral_Ioc_eq_integral_Ioo,←intervalIntegral.integral_of_le hband.le]
    exact intervalIntegral.integral_mono_interval hax hband.le le_rfl
      (ae_of_all _ (fun _=>abs_nonneg _)) hf.abs
  have Hbudget : (∫u in Ioo (a*M.xs) (b*M.xs),|f u|) <
      M.xs^3*((b*M.xs-a*M.xs)-(∫u in Ioo (a*M.xs) (b*M.xs),p.positiveMassMask u)) := by
    apply (Hup.trans_lt hsmall).trans_le
    apply mul_le_mul_of_nonneg_left _ (pow_pos M.hxs 3).le
    nlinarith only [hmass]
  obtain ⟨u,hu,hm,hf,hp⟩ := exists_good_point_off_mask_ae hband (pow_pos M.hxs 3).le
    hfi (p.positiveMassMask_integrable.mono_set hsub)
    (Eventually.of_forall (fun u _=>abs_nonneg (f u)))
    (Eventually.of_forall (fun u _=>by
      dsimp only [Potential.positiveMassMask]
      by_cases H:M.R u∈p.positiveRadiusSet <;> simp [H])) hP Hbudget
  exact ⟨u,hu,(p.positiveMassMask_zero_iff u).mp hm,hf,hp⟩

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
