module

public import OmittedForwardFeasibility

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal
section
variable {r0 u0 c : ℝ} {k M : ℝ → ℝ}
variable (hr : r0 ≤ 1) (hu : u0 ∈ Icc (0 : ℝ) 1)
variable (hc : 0 < c) (hk : ContinuousOn k (Icc r0 1))
variable (hkc : ∀ r ∈ Icc r0 1, c ≤ k r)
variable (hm : MonotoneOn M (Icc (0 : ℝ) 1)) (hM : 0 ≤ M 1)

def omittedSweepQuantile (α : inverseIntegralConstraints r0 u0 k M) : ℝ → ℝ :=
  IccExtend hu.2 (constrainedQuantileMap hr hc hk hkc hm hM α)

theorem omittedSweepQuantile_eq (α : inverseIntegralConstraints r0 u0 k M)
    {u : ℝ} (hum : u ∈ Icc u0 1) :
    omittedSweepQuantile hr hu hc hk hkc hm hM α u =
      constrainedQuantile hr hc hk hkc hm hM α ⟨u, hum⟩ := by
  simp [omittedSweepQuantile, IccExtend, constrainedQuantileMap, projIcc_of_mem hu.2 hum]

theorem omittedSweepQuantile_bounds (α : inverseIntegralConstraints r0 u0 k M) (u : ℝ) :
    omittedSweepQuantile hr hu hc hk hkc hm hM α u ∈ Icc r0 1 :=
  (constrainedQuantile hr hc hk hkc hm hM α (projIcc u0 1 hu.2 u)).property

theorem omittedSweepQuantile_spec (α : inverseIntegralConstraints r0 u0 k M)
    {u : ℝ} (hum : u ∈ Icc u0 1) :
    α.val.val (omittedSweepQuantile hr hu hc hk hkc hm hM α u) = u := by
  rw [omittedSweepQuantile_eq hr hu hc hk hkc hm hM α hum]
  exact constrainedQuantile_spec hr hc hk hkc hm hM α ⟨u, hum⟩

theorem omittedSweepQuantile_inverse (α : inverseIntegralConstraints r0 u0 k M)
    {r : ℝ} (hrm : r ∈ Icc r0 1) :
    omittedSweepQuantile hr hu hc hk hkc hm hM α (α.val.val r) = r := by
  have hum : α.val.val r ∈ Icc u0 1 := (inverseConstraintMap α ⟨r, hrm⟩).property
  apply (inverseConstraint_strictMonoOn hc hk hkc α.property).injOn
    (omittedSweepQuantile_bounds hr hu hc hk hkc hm hM α _) hrm
  exact omittedSweepQuantile_spec hr hu hc hk hkc hm hM α hum

theorem omittedSweepQuantile_left (α : inverseIntegralConstraints r0 u0 k M) :
    omittedSweepQuantile hr hu hc hk hkc hm hM α u0 = r0 := by
  simpa only [α.property.1] using omittedSweepQuantile_inverse hr hu hc hk hkc hm hM α
    (r := r0) ⟨le_rfl, hr⟩

theorem omittedSweepQuantile_one (α : inverseIntegralConstraints r0 u0 k M) :
    omittedSweepQuantile hr hu hc hk hkc hm hM α 1 = 1 := by
  simpa only [α.property.2.1] using omittedSweepQuantile_inverse hr hu hc hk hkc hm hM α
    (r := 1) ⟨hr, le_rfl⟩

theorem omittedSweepQuantile_lipschitz (α : inverseIntegralConstraints r0 u0 k M) :
    LipschitzWith ⟨1/c, div_nonneg zero_le_one hc.le⟩ (omittedSweepQuantile hr hu hc hk hkc hm hM α) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hh := (constrainedQuantile_lipschitz hr hc hk hkc hm hM α).dist_le_mul
    (projIcc u0 1 hu.2 x) (projIcc u0 1 hu.2 y)
  change dist (omittedSweepQuantile hr hu hc hk hkc hm hM α x)
      (omittedSweepQuantile hr hu hc hk hkc hm hM α y) ≤
      (1/c)*dist (projIcc u0 1 hu.2 x) (projIcc u0 1 hu.2 y) at hh
  apply hh.trans
  have hp := (LipschitzWith.projIcc hu.2).dist_le_mul x y
  change dist _ _ ≤ (1 : ℝ)*dist x y at hp
  change (1/c)*dist (projIcc u0 1 hu.2 x) (projIcc u0 1 hu.2 y) ≤ (1/c)*dist x y
  simpa only [one_mul] using mul_le_mul_of_nonneg_left hp (div_nonneg zero_le_one hc.le)

theorem omittedSweepQuantile_ae_slope (α : inverseIntegralConstraints r0 u0 k M)
    (hMc : Continuous M) (hMp : ∀ u ∈ Icc u0 1, 0 < M u) :
    ∀ᵐ u ∂volume, u ∈ Icc u0 1 →
      (M u)⁻¹ ≤ deriv (omittedSweepQuantile hr hu hc hk hkc hm hM α) u ∧
      deriv (omittedSweepQuantile hr hu hc hk hkc hm hM α) u ≤
        (k (omittedSweepQuantile hr hu hc hk hkc hm hM α u))⁻¹ := by
  let q := omittedSweepQuantile hr hu hc hk hkc hm hM α
  have hal := inverseIntegralConstraints_lipschitz hm hM α.property
  have had : α.val ∈ inverseDifferentialConstraints r0 u0 k M := by
    rw [inverseDifferentialConstraints_eq r0 u0 hr k M hk hMc hm hM]
    exact α.property
  obtain ⟨_, _, _, _, hder⟩ := had
  have hac : AbsolutelyContinuousOnInterval α.val.val r0 1 := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := ⟨M 1, hM⟩)
    simpa only [uIcc_of_le hr] using hal
  have hdiff : ∀ᵐ r ∂volume, r ∈ Icc r0 1 → DifferentiableAt ℝ α.val.val r := by
    simpa only [uIcc_of_le hr] using hac.ae_differentiableAt
  have hboth : ∀ᵐ r ∂volume, r ∈ Icc r0 1 → DifferentiableAt ℝ α.val.val r ∧
      k r ≤ deriv α.val.val r ∧ deriv α.val.val r ≤ M (α.val.val r) := by
    filter_upwards [hdiff, hder] with r hd hb hrm
    exact ⟨hd hrm, hb hrm⟩
  have hpull := ae_inverse_pullback hal
    (fun u (_ : u ∈ Icc u0 1) => omittedSweepQuantile_bounds hr hu hc hk hkc hm hM α u)
    (fun u hum => omittedSweepQuantile_spec hr hu hc hk hkc hm hM α hum) hboth
  filter_upwards [hpull, volume.ae_ne u0, volume.ae_ne (1 : ℝ)] with u hp hu0 hu1 hum
  have hui : u ∈ Ioo u0 1 :=
    ⟨lt_of_le_of_ne hum.1 (Ne.symm hu0), lt_of_le_of_ne hum.2 hu1⟩
  have hspec : α.val.val (q u) = u := omittedSweepQuantile_spec hr hu hc hk hkc hm hM α hum
  have hbd := (hp hum).2
  have hkp : 0 < k (q u) := hc.trans_le (hkc (q u) (omittedSweepQuantile_bounds hr hu hc hk hkc hm hM α u))
  have hdp : 0 < deriv α.val.val (q u) := hkp.trans_le hbd.1
  have hleft : ∀ᶠ v in 𝓝 u, α.val.val (q v) = v := by
    filter_upwards [Icc_mem_nhds hui.1 hui.2] with v hv
    exact omittedSweepQuantile_spec hr hu hc hk hkc hm hM α hv
  have hd := ((hp hum).1.hasDerivAt.of_local_left_inverse
    (omittedSweepQuantile_lipschitz hr hu hc hk hkc hm hM α).continuous.continuousAt hdp.ne' hleft).deriv
  change deriv q u = (deriv α.val.val (q u))⁻¹ at hd
  change (M u)⁻¹ ≤ deriv q u ∧ deriv q u ≤ (k (q u))⁻¹
  rw [hd]
  rw [hspec] at hbd
  exact ⟨(inv_le_inv₀ (hMp u hum) hdp).mpr hbd.2,
    (inv_le_inv₀ hdp hkp).mpr hbd.1⟩
end
end OAI.SKFluctuations.LaplaceWindowFormalization
