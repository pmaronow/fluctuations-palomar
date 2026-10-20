module

public import ScalarFiniteParisiBridge
public import SKFluctuationsOAI.Probability.SKFluctuations.ScalarFlattenedContinuity

@[expose] public section

noncomputable section

namespace OAI.SKFluctuations.Hierarchy

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal

def scalarReferenceMinimizers (β : ℝ≥0) (hβ : 0 < β) : Set boundedMassProfiles :=
  scalarProfiles ∩ {α | scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α =
    normalizedScalarParisiReference β}

theorem scalarReferenceMinimizers_compact (β : ℝ≥0) (hβ : 0 < β) :
    IsCompact (scalarReferenceMinimizers β hβ) := by
  let _ : CompactSpace boundedMassProfiles :=
    isCompact_iff_compactSpace.mp boundedMassProfiles_compact
  exact (scalarProfiles_closed.inter (isClosed_eq (scalarParisiValue_continuous _)
    continuous_const)).isCompact

theorem scalarReferenceMinimizers_nonempty (β : ℝ≥0) (hβ : 0 < β) :
    (scalarReferenceMinimizers β hβ).Nonempty := by
  obtain ⟨α, hα, hv, _⟩ := exists_scalarProfile_eq_normalizedScalarParisiReference hβ
  exact ⟨α, hα, hv⟩

theorem scalarReferenceMinimizers_isMinimizer {β : ℝ≥0} {hβ : 0 < β}
    {α : boundedMassProfiles} (hα : α ∈ scalarReferenceMinimizers β hβ) :
    ∀ γ ∈ scalarProfiles,
      scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α ≤
        scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) γ := by
  intro γ _
  rw [hα.2]
  exact normalizedScalarParisiReference_le_value hβ γ

theorem scalarReferenceMinimizers_uniform_origin {β : ℝ≥0} (hβ : 0 < β)
    (hT : 1 < (β : ℝ) ^ 2) {a : ℝ} (ha : 0 < a) :
    ∃ d : ℝ, 0 < d ∧ ∀ α ∈ scalarReferenceMinimizers β hβ, α.val d < a := by
  let q : ℕ → ℝ := fun n => 1 / (n + 1 : ℕ)
  have hq (n : ℕ) : 0 < q n := by dsimp [q]; positivity
  have ht : Tendsto q atTop (𝓝[>] 0) := by
    exact tendsto_nhdsWithin_iff.mpr ⟨SKCavity.tendsto_succ_reciprocal,
      Eventually.of_forall hq⟩
  let U : ℕ → Set boundedMassProfiles := fun n => {α | α.val (q n) < a}
  have hU (n : ℕ) : IsOpen (U n) := by
    exact isOpen_lt ((continuous_apply (q n)).comp continuous_subtype_val) continuous_const
  have hcover : scalarReferenceMinimizers β hβ ⊆ ⋃ n, U n := by
    intro α hα
    have hz := scalarMinimizer_cdf_zero hT α hα.1
      (scalarReferenceMinimizers_isMinimizer hα)
    have hc := α.property.2.tendsto_rightLim 0 |>.comp ht
    change Tendsto (fun n => α.val (q n)) atTop (𝓝 (profileStieltjes α 0)) at hc
    rw [hz] at hc
    obtain ⟨n, hn⟩ := (hc.eventually (gt_mem_nhds ha)).exists
    exact mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨s, hs⟩ := (scalarReferenceMinimizers_compact β hβ).elim_finite_subcover U hU hcover
  refine ⟨q (s.sup id), hq _, ?_⟩
  intro α hα
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hs hα)
  obtain ⟨hns, hval⟩ := mem_iUnion.mp hn
  have hN : n ≤ s.sup id := by simpa using (Finset.le_sup (f := id) hns)
  have hsmall : q (s.sup id) ≤ q n := by
    dsimp only [q]
    gcongr
  exact (α.property.2 hsmall).trans_lt hval

theorem scalar_near_minimizers_uniform_origin {β : ℝ≥0} (hβ : 0 < β)
    (hT : 1 < (β : ℝ) ^ 2) {a : ℝ} (ha : 0 < a) :
    ∃ d ε : ℝ, 0 < d ∧ 0 < ε ∧ ∀ α ∈ scalarProfiles,
      scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α ≤
        normalizedScalarParisiReference β + ε → α.val d < a := by
  obtain ⟨d, hd, hdm⟩ := scalarReferenceMinimizers_uniform_origin hβ hT ha
  let K : Set boundedMassProfiles := scalarProfiles ∩ {α | a ≤ α.val d}
  let _ : CompactSpace boundedMassProfiles :=
    isCompact_iff_compactSpace.mp boundedMassProfiles_compact
  have hK : IsCompact K := by
    exact (scalarProfiles_closed.inter (isClosed_le continuous_const
      ((continuous_apply d).comp continuous_subtype_val))).isCompact
  by_cases hne : K.Nonempty
  · obtain ⟨α₀, hα₀, hmin⟩ := hK.exists_isMinOn hne
      (scalarParisiValue_continuous (sq_pos_of_pos (NNReal.coe_pos.mpr hβ))).continuousOn
    have hvne : scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α₀ ≠
        normalizedScalarParisiReference β := by
      intro hv
      exact (not_lt_of_ge hα₀.2) (hdm α₀ ⟨hα₀.1, hv⟩)
    have hv : normalizedScalarParisiReference β <
        scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α₀ :=
      lt_of_le_of_ne (normalizedScalarParisiReference_le_value hβ α₀) (Ne.symm hvne)
    refine ⟨d, (scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α₀ -
      normalizedScalarParisiReference β) / 2, hd, by linarith, ?_⟩
    intro α hα hval
    by_contra hn
    have hbad : α ∈ K := ⟨hα, le_of_not_gt hn⟩
    have hm : scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α₀ ≤
        scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α := hmin hbad
    linarith
  · refine ⟨d, 1, hd, by norm_num, ?_⟩
    intro α hα _
    by_contra hn
    exact hne ⟨α, hα, le_of_not_gt hn⟩

theorem scalar_near_minimizers_fixed_band {β : ℝ≥0} (hβ : 0 < β)
    (hT : 1 < (β : ℝ) ^ 2) {a : ℝ} (ha : 0 < a) :
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧ ∀ α ∈ scalarProfiles,
      scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) α ≤
        normalizedScalarParisiReference β + ε →
      ∀ u ∈ Ioo (0 : ℝ) 1, a ≤ u →
        c * u ≤ scalarQuantile α u ∧ scalarQuantile α u ≤ C * u := by
  obtain ⟨d, ε, hd, hε, hmass⟩ := scalar_near_minimizers_uniform_origin hβ hT ha
  refine ⟨d / 2, 1 / a, ε, by linarith, one_div_pos.mpr ha, hε, ?_⟩
  intro α hα hv u hu hau
  have hsmall := hmass α hα hv
  have hlim : profileStieltjes α (d / 2) ≤ α.val d :=
    α.property.2.rightLim_le (by linarith)
  have hquant : d / 2 ≤ scalarQuantile α u := by
    by_contra hn
    have hqle : scalarQuantile α u ≤ d / 2 := (lt_of_not_ge hn).le
    have hcdf := (scalarQuantile_le_iff hα ⟨hu.1, hu.2.le⟩).mp hqle
    linarith
  constructor
  · exact (mul_le_of_le_one_right (by linarith : 0 ≤ d / 2) hu.2.le).trans hquant
  · have hq : scalarQuantile α u ≤ 1 :=
      (scalarQuantile_le_iff hα ⟨hu.1, hu.2.le⟩).mpr (by
        rw [profileStieltjes_one hα]
        exact hu.2.le)
    have hone : (1 : ℝ) ≤ 1 / a * u := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ ha]
      simpa using hau
    exact hq.trans hone

theorem eventually_scalar_near_minimizers_fixed_band {β : ℝ≥0} (hβ : 0 < β)
    (hT : 1 < (β : ℝ) ^ 2) {a : ℝ} (ha : 0 < a)
    (α : ℕ → boundedMassProfiles) (hα : ∀ n, α n ∈ scalarProfiles)
    (hv : Tendsto (fun n => scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) (α n))
      atTop (𝓝 (normalizedScalarParisiReference β))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n in atTop,
      ∀ u ∈ Ioo (0 : ℝ) 1, a ≤ u →
        c * u ≤ scalarQuantile (α n) u ∧ scalarQuantile (α n) u ≤ C * u := by
  obtain ⟨c, C, ε, hc, hC, hε, hband⟩ := scalar_near_minimizers_fixed_band hβ hT ha
  refine ⟨c, C, hc, hC, ?_⟩
  have hgt : normalizedScalarParisiReference β < normalizedScalarParisiReference β + ε := by linarith
  filter_upwards [hv.eventually (gt_mem_nhds hgt)] with n hn
  exact hband (α n) (hα n) hn.le

theorem scalar_minimizing_limit_of_values {β : ℝ≥0} (hβ : 0 < β)
    {ι : Type*} {l : Filter ι} [NeBot l] {α : ι → boundedMassProfiles}
    {α₀ : boundedMassProfiles} (hα : ∀ᶠ i in l, α i ∈ scalarProfiles)
    (hconv : Tendsto α l (𝓝 α₀))
    (hv : Tendsto (fun i => scalarParisiValue (sq_pos_of_pos (NNReal.coe_pos.mpr hβ)) (α i))
      l (𝓝 (normalizedScalarParisiReference β))) :
    α₀ ∈ scalarReferenceMinimizers β hβ := by
  refine ⟨scalarProfiles_closed.mem_of_tendsto hconv hα, ?_⟩
  exact tendsto_nhds_unique
    ((scalarParisiValue_continuous _).tendsto α₀ |>.comp hconv) hv

end OAI.SKFluctuations.Hierarchy
