module

public import ComparisonContactCover
public import ComparisonContactBoundaryTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter ProbabilityTheory Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 1800000

theorem dominated_setIntegral_difference_le
    (K S : Set ℝ) (hsub : S⊆K) (μ : Measure ℝ) (hμ : μ ≤ volume)
    (f g : ℝ → ℝ) (hf : IntegrableOn f K) (hg : IntegrableOn g K) :
    (∫r in S,g r∂μ) ≤ (∫r in S,f r∂μ)+(∫r in K,|g r-f r|) := by
  have hfm : IntegrableOn f S μ := (hf.mono_measure hμ).mono_set hsub
  have hgm : IntegrableOn g S μ := (hg.mono_measure hμ).mono_set hsub
  have hn := norm_integral_le_integral_norm (μ:=μ.restrict S) (fun r => g r-f r)
  have hm := integral_mono_measure (Measure.restrict_mono hsub hμ)
    (ae_of_all _ (fun r => abs_nonneg (g r-f r))) (hg.sub hf).abs
  rw [integral_sub hgm hfm] at hn
  simp only [Real.norm_eq_abs] at hn
  have hh := (le_abs_self ((∫r in S,g r∂μ)-(∫r in S,f r∂μ))).trans (hn.trans hm)
  linarith

theorem dominated_varying_contact_neighborhood_trace_transfer
    (H : ℝ → ℝ) (hH : Measurable H) (K : Set ℝ) (hK : MeasurableSet K)
    (f : ℝ → ℝ) (hf : IntegrableOn f K) (hf0 : ∀r∈K,0 ≤ f r)
    (moving : ℕ → ℝ → ℝ) (hmoving : ∀j,IntegrableOn (moving j) K)
    (hL1 : Tendsto (fun j => ∫r in K,|moving j r-f r|) atTop (𝓝 0))
    (μ : ℕ → Measure ℝ) (hμ : ∀j,μ j ≤ volume)
    (selected : ℕ → Set ℝ)
    (hcontain : ∀κ>0,∀ᶠ j in atTop,∀r∈selected j,r∈K → |H r| ≤ κ)
    (B : ℝ)
    (hcontact : ∀ε>0,∀ᶠ j in atTop,
      (∫r in {r | r∈K ∧ H r=0},f r∂μ j) ≤ B+ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop,(∫r in K∩selected j,moving j r∂μ j) ≤ B+ε := by
  have hfixed := fixed_contact_neighborhood_trace_transfer H hH K hK f hf hf0
    μ hμ selected hcontain B hcontact (show 0 < ε/2 by linarith)
  have herror := (tendsto_order.mp hL1).2 (ε/2) (by linarith : 0 < ε/2)
  filter_upwards [hfixed,herror] with j hj he
  have hn := dominated_setIntegral_difference_le K (K∩selected j)
    (fun _ hr => hr.1) (μ j) (hμ j) f (moving j) hf (hmoving j)
  linarith

private theorem boundedWeight_integrableOn_interval
    {a z : ℝ} (w : ℝ → ℝ) (hw : Measurable w) {B : ℝ}
    (hwb : ∀r,‖w r‖ ≤ B) : IntegrableOn w (Ioo a z) := by
  have hfinite : volume (Ioo a z)≠⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc a z)≠⊤) (measure_mono Ioo_subset_Icc_self)
  have hone : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo a z) := integrableOn_const hfinite
  simpa only [IntegrableOn,mul_one] using hone.bdd_mul
    hw.stronglyMeasurable.aestronglyMeasurable.restrict (ae_of_all _ hwb)

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

include hm hM in
theorem comparison_inverse_weight_L1_le
    (α : inverseIntegralConstraints 0 0 k M)
    {a z : ℝ} (ha : 0 < a) (hz : z ≤ 1)
    (w v : ℝ → ℝ) (hw : Measurable w) (hv : Measurable v)
    {B : ℝ} (hwb : ∀r,‖w r‖ ≤ B) (hvb : ∀r,‖v r‖ ≤ B) :
    (∫r in Ioo a z,|deriv α.val.val r*v r-deriv α.val.val r*w r|) ≤
      M 1*(∫r in Ioo a z,|v r-w r|) := by
  have hwI := boundedWeight_integrableOn_interval w hw hwb (a:=a) (z:=z)
  have hvI := boundedWeight_integrableOn_interval v hv hvb (a:=a) (z:=z)
  have hfwI := comparison_radiusWeight_integrableOn hm hM α ha hz
    (Ioo a z) measurableSet_Ioo (Subset.refl _) w hw hwb
  have hfvI := comparison_radiusWeight_integrableOn hm hM α ha hz
    (Ioo a z) measurableSet_Ioo (Subset.refl _) v hv hvb
  have hpoint r (hr : r∈Ioo a z) :
      |deriv α.val.val r*v r-deriv α.val.val r*w r| ≤ M 1*|v r-w r| := by
    have hr01 : r∈Ioo (0:ℝ) 1 := ⟨ha.trans hr.1,hr.2.trans_le hz⟩
    have hd : ‖deriv α.val.val r‖ ≤ M 1 :=
      norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr01.1 hr01.2)
        (inverseIntegralConstraints_lipschitz hm hM α.property)
    rw [←mul_sub,abs_mul]
    exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hd) (abs_nonneg _)
  have hh := setIntegral_mono_on (hfvI.sub hfwI).abs
    ((hvI.sub hwI).abs.const_mul (M 1)) measurableSet_Ioo hpoint
  simpa only [Pi.sub_apply,integral_const_mul] using hh

include hm hM in
theorem comparison_inverse_weight_L1_tendsto
    (α : inverseIntegralConstraints 0 0 k M)
    {a z : ℝ} (ha : 0 < a) (hz : z ≤ 1)
    (w : ℝ → ℝ) (hw : Measurable w) (moving : ℕ → ℝ → ℝ)
    (hmove : ∀j,Measurable (moving j)) {B : ℝ}
    (hwb : ∀r,‖w r‖ ≤ B) (hmb : ∀j r,‖moving j r‖ ≤ B)
    (hL1 : Tendsto (fun j => ∫r in Ioo a z,|moving j r-w r|) atTop (𝓝 0)) :
    Tendsto (fun j => ∫r in Ioo a z,
      |deriv α.val.val r*moving j r-deriv α.val.val r*w r|) atTop (𝓝 0) := by
  have ht : Tendsto (fun j => M 1*(∫r in Ioo a z,|moving j r-w r|)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hL1.const_mul (M 1)
  exact squeeze_zero (fun j => integral_nonneg (fun _ => abs_nonneg _))
    (fun j => comparison_inverse_weight_L1_le hm hM α ha hz w (moving j) hw (hmove j) hwb (hmb j)) ht

theorem comparisonPhysicalVaryingContactCoverTrace_eventually
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d)
    (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1 → H r=0 →
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u => (b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u => (h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u => (b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u => (h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r => b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r => h (α.val.val r)) (Icc a z))
    (w : ℝ → ℝ) (hw : Measurable w) (hw0 : ∀r,0 ≤ w r)
    (moving : ℕ → ℝ → ℝ) (hmove : ∀j,Measurable (moving j))
    {B : ℝ} (hwb : ∀r,‖w r‖ ≤ B) (hmb : ∀j r,‖moving j r‖ ≤ B)
    (hL1 : Tendsto (fun j => ∫r in Ioo a z,|moving j r-w r|) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let A := {r | r∈Ioo a z ∧ H r=0}
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in Ioo a z∩contactMeetingCells H R (partitionPoint 0 (as j)) (as j).length,
        deriv α.val.val r*moving j r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α (as j) (ho j)) ≤
      ((9*Real.log N)/F)*(∫r in A,deriv α.val.val r*w r)+ε := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let K := Ioo a z
  let f := fun r => deriv α.val.val r*w r
  let fm := fun j r => deriv α.val.val r*moving j r
  have hf := comparison_radiusWeight_integrableOn hm hM α ha hz
    K measurableSet_Ioo (Subset.refl _) w hw hwb
  have hfm j := comparison_radiusWeight_integrableOn hm hM α ha hz
    K measurableSet_Ioo (Subset.refl _) (moving j) (hmove j) (hmb j)
  have hf0 r (_ : r∈K) : 0 ≤ f r := mul_nonneg α.val.property.2.deriv_nonneg (hw0 r)
  have hL1f := comparison_inverse_weight_L1_tendsto hm hM α ha hz
    w hw moving hmove hwb hmb hL1
  let He := fun r => H (projIcc (0:ℝ) 1 zero_le_one r)
  have hHC : ContinuousOn H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hH.continuousOn
  have hHe : Continuous He :=
    (continuousOn_iff_continuous_restrict.mp hHC).comp continuous_projIcc
  have heq r (hr : r∈Icc (0:ℝ) 1) : He r=H r := by
    simp only [He,projIcc_of_mem zero_le_one hr]
  have hr01 r (hr : r∈K) : r∈Icc (0:ℝ) 1 :=
    ⟨ha.le.trans hr.1.le,hr.2.le.trans hz⟩
  let μ := fun j => comparisonPhysicalRadiusMeasure hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)
  have hdom j : μ j ≤ volume :=
    (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM
      n dphys e d lam b h α (as j) (ho j)).trans Measure.restrict_le_self
  let selected := fun j => contactMeetingCells H R (partitionPoint 0 (as j)) (as j).length
  have hcontain : ∀κ>0,∀ᶠ j in atTop,∀r∈selected j,r∈K → |He r| ≤ κ := by
    intro κ hκ
    filter_upwards [comparison_contactMeetingCells_potential_eventually hc hk hkc hm hM
      α H hH as mesh ho hmesh hlim hκ] with j hj
    intro r hr hrr
    rw [heq r (hr01 r hrr)]
    exact (hj r hr).le
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let budget := ((9*Real.log N)/F)*(∫r in {r | r∈K ∧ H r=0},f r)
  have hcontactSets : {r | r∈K ∧ He r=0}={r | r∈K ∧ H r=0} := by
    ext r
    constructor <;> intro hr <;> exact ⟨hr.1,by simpa only [heq r (hr01 r hr.1)] using hr.2⟩
  have hcontact : ∀ε'>0,∀ᶠ j in atTop,
      (∫r in {r | r∈K ∧ He r=0},f r∂μ j) ≤ budget+ε' := by
    intro ε' hε'
    have ht := comparisonPhysicalWeightedContactTrace_eventually hc hk hkc hm hM
      hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero
      as mesh ho hend hmesh hmesh0 hlim ha haz hz Kb Kh hparent hfield
      w hw B (fun r _ _ => hwb r) (fun r _ _ => hw0 r) hε'
    simpa only [hcontactSets,K,f,μ,F,budget] using ht
  exact dominated_varying_contact_neighborhood_trace_transfer He hHe.measurable K
    measurableSet_Ioo f hf hf0 fm hfm hL1f μ hdom selected hcontain budget hcontact hε

end
end OAI.SKFluctuations.LaplaceWindowFormalization
