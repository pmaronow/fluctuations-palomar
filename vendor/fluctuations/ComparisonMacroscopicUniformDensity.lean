module

public import ComparisonMacroscopicMovingDensity
public import ComparisonMacroscopicInitialDensityBounds
public import BoundedMassProfileHelly

@[expose] public section

noncomputable section
set_option maxHeartbeats 2000000
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy GaussianCalculus Scalar
open scoped Topology NNReal

theorem macro_scalar_minimizers_uniform_initial_ratio {β : ℝ≥0} (hβ : 0 < β)
    (hT : 1 < (β : ℝ)^2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ α : boundedMassProfiles,
      α ∈ scalarProfiles →
      (∀ γ ∈ scalarProfiles,
        scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α ≤
          scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) γ) →
      (∀ x, ContinuousWithinAt α.val (Ici x) x) →
      ∀ q : ℝ, 0 < q → q < ρ →
        (β : ℝ)^2 * Real.exp (-12*(β : ℝ)^2) ≤ α.val q / q ∧
        α.val q / q ≤ (β : ℝ)^2 * (ReplicaTree.attachmentCount 1 3 : ℝ)^2 /
          Real.exp (-12*(β : ℝ)^2) := by
  let ht : 0 < (β : ℝ)^2 := sq_pos_of_pos (NNReal.coe_pos.mpr hβ)
  let lo : ℝ := (β : ℝ)^2 * Real.exp (-12*(β : ℝ)^2)
  let hi : ℝ := (β : ℝ)^2 * (ReplicaTree.attachmentCount 1 3 : ℝ)^2 /
    Real.exp (-12*(β : ℝ)^2)
  change ∃ ρ : ℝ, 0 < ρ ∧ ∀ α : boundedMassProfiles,
    α ∈ scalarProfiles →
    (∀ γ ∈ scalarProfiles, scalarParisiValue ht α ≤ scalarParisiValue ht γ) →
    (∀ x, ContinuousWithinAt α.val (Ici x) x) →
    ∀ q : ℝ, 0 < q → q < ρ → lo ≤ α.val q / q ∧ α.val q / q ≤ hi
  by_contra h
  push Not at h
  choose α hprofiles hmin hc q hqp hqsmall hbad using
    fun n : ℕ => h (1 / (n+1 : ℕ)) (by positivity)
  have hq : Tendsto q atTop (𝓝 0) :=
    squeeze_zero (fun n => (hqp n).le) (fun n => (hqsmall n).le)
      SKCavity.tendsto_succ_reciprocal
  obtain ⟨a, φ, hφ, hα⟩ := boundedMassProfiles_tendsto_subseq α
  have hlim := macro_scalar_minimizers_moving_density hβ hT
    (fun n => hprofiles (φ n)) (fun n => hmin (φ n))
    (fun n => hc (φ n)) hα (hq.comp hφ.tendsto_atTop)
    (Eventually.of_forall fun n => hqp (φ n))
  have hb := macroScalarInitialDensityConstant_uniform_bounds ht a
  have hpos : 0 < scalarInitialDensityConstant ht a :=
    scalarInitialDensityConstant_pos ht a
  have hlo : lo < scalarInitialDensityConstant ht a := by
    dsimp [lo] at *
    linarith [mul_pos ht (Real.exp_pos (-12*(β : ℝ)^2))]
  have hhi : scalarInitialDensityConstant ht a < hi := by
    dsimp [hi]
    have hbound : 2 * scalarInitialDensityConstant ht a ≤
        (β : ℝ)^2 * (ReplicaTree.attachmentCount 1 3 : ℝ)^2 /
          Real.exp (-12*(β : ℝ)^2) := by
      have hh := mul_le_mul_of_nonneg_left hb.2 (by norm_num : (0 : ℝ) ≤ 2)
      convert hh using 1
      all_goals field_simp
    linarith
  obtain ⟨n, hnlo, hnhi⟩ :=
    ((hlim.eventually (lt_mem_nhds hlo)).and
      (hlim.eventually (gt_mem_nhds hhi))).exists
  exact (hbad (φ n) hnlo.le).not_ge hnhi.le

theorem macro_scalar_minimizers_uniform_initial_cdf {β : ℝ≥0} (hβ : 0 < β)
    (hT : 1 < (β : ℝ)^2) :
    ∃ c C ρ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ρ ∧
      ∀ α : boundedMassProfiles, α ∈ scalarProfiles →
      (∀ γ ∈ scalarProfiles,
        scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α ≤
          scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) γ) →
      (∀ x, ContinuousWithinAt α.val (Ici x) x) →
      ∀ q ∈ Ioo (0 : ℝ) ρ, c*q ≤ α.val q ∧ α.val q ≤ C*q := by
  obtain ⟨ρ, hρ, hb⟩ := macro_scalar_minimizers_uniform_initial_ratio hβ hT
  let c : ℝ := (β : ℝ)^2 * Real.exp (-12*(β : ℝ)^2)
  let C : ℝ := (β : ℝ)^2 * (ReplicaTree.attachmentCount 1 3 : ℝ)^2 /
    Real.exp (-12*(β : ℝ)^2)
  have ht : 0 < (β : ℝ)^2 := sq_pos_of_pos (NNReal.coe_pos.mpr hβ)
  have hC : 0 < C := by
    have ha : 0 < (ReplicaTree.attachmentCount 1 3 : ℝ) := by
      norm_num [ReplicaTree.attachmentCount]
    dsimp [C]
    positivity
  refine ⟨c, C, ρ, by dsimp [c]; positivity, hC, hρ, ?_⟩
  intro α hp hm hc q hq
  have hh := hb α hp hm hc q hq.1 hq.2
  exact ⟨(le_div_iff₀ hq.1).mp hh.1, (div_le_iff₀ hq.1).mp hh.2⟩

theorem macro_scalar_minimizers_uniform_quantile {β : ℝ≥0} (hβ : 0 < β)
    (hT : 1 < (β : ℝ)^2) :
    ∃ cR CR : ℝ, 0 < cR ∧ 0 < CR ∧
      ∀ α : boundedMassProfiles, α ∈ scalarProfiles →
      (∀ γ ∈ scalarProfiles,
        scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α ≤
          scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) γ) →
      (∀ x, ContinuousWithinAt α.val (Ici x) x) →
      ∀ u ∈ Ioo (0 : ℝ) 1, cR*u ≤ scalarQuantile α u ∧
        scalarQuantile α u ≤ CR*u := by
  obtain ⟨c, C, ρ, hcp, hCp, hρ, hcdf⟩ :=
    macro_scalar_minimizers_uniform_initial_cdf hβ hT
  let a0 : ℝ := min (c*ρ/2) (1/2)
  have ha0 : 0 < a0 := lt_min (by positivity) (by norm_num)
  obtain ⟨c1, C1, ε, hc1, hC1, hε, hfixed⟩ :=
    scalar_near_minimizers_fixed_band hβ hT ha0
  refine ⟨min (1/C) c1, max (1/c) C1,
    lt_min (by positivity) hc1, (by positivity), ?_⟩
  intro α hp hm hrc u hu
  have huc : u ∈ Ioc (0 : ℝ) 1 := ⟨hu.1, hu.2.le⟩
  by_cases hs : u < a0
  · have hxu : 0 < u/c := div_pos hu.1 hcp
    have hxρ : u/c < ρ := by
      apply (div_lt_iff₀ hcp).mpr
      have hsmall := hs.trans_le (min_le_left (c*ρ/2) (1/2))
      nlinarith [mul_pos hcp hρ]
    have hq_upper : scalarQuantile α u ≤ u/c := by
      apply (scalarQuantile_le_iff hp huc).mpr
      rw [profileStieltjes_eq_of_rightContinuous α hrc]
      have hh := (hcdf α hp hm hrc (u/c) ⟨hxu, hxρ⟩).1
      calc
        u = c*(u/c) := by field_simp
        _ ≤ _ := hh
    have hqpos : 0 < scalarQuantile α u :=
      scalarQuantile_pos hp (scalarMinimizer_cdf_zero hT α hp hm) huc
    have hqρ : scalarQuantile α u < ρ := hq_upper.trans_lt hxρ
    have hq_lower : u/C ≤ scalarQuantile α u := by
      apply (div_le_iff₀ hCp).mpr
      have hge := scalarQuantile_cdf_ge hp huc
      rw [profileStieltjes_eq_of_rightContinuous α hrc] at hge
      have hb := (hcdf α hp hm hrc (scalarQuantile α u) ⟨hqpos, hqρ⟩).2
      nlinarith
    constructor
    · calc
        min (1/C) c1 * u ≤ (1/C)*u :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hu.1.le
        _ = u/C := by ring
        _ ≤ _ := hq_lower
    · calc
        scalarQuantile α u ≤ u/c := hq_upper
        _ = (1/c)*u := by ring
        _ ≤ max (1/c) C1 * u :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hu.1.le
  · have hv : scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α ≤
        normalizedScalarParisiReference β+ε := by
      rw [scalar_minimizer_value_eq_normalizedScalarParisiReference hβ α hm]
      linarith
    have hb := hfixed α hp hv u hu (le_of_not_gt hs)
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) hu.1.le).trans hb.1,
      hb.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hu.1.le)⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
