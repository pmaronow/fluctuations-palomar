module

public import ComparisonVaryingContactWeights
public import ComparisonContactColumnLimitMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000

theorem dominated_contact_only_varying_trace_transfer
    (H : ℝ → ℝ) (hH : Measurable H) (K : Set ℝ) (hK : MeasurableSet K)
    (hfinite : volume K ≠ ⊤) (f : ℝ → ℝ) (hf : IntegrableOn f K)
    (moving : ℕ → ℝ → ℝ) (hmoving : ∀j,IntegrableOn (moving j) K)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀j r,r ∈ K → moving j r ∈ Icc (0:ℝ) B)
    (hL1 : Tendsto (fun j=>∫r in {r | r ∈ K ∧ H r=0},|moving j r-f r|) atTop (𝓝 0))
    (μ : ℕ → Measure ℝ) (hμ : ∀j,μ j ≤ volume)
    (selected bad : ℕ → Set ℝ) (hselected : ∀j,MeasurableSet (selected j))
    (hbad : ∀j,MeasurableSet (bad j))
    (hbadlim : Tendsto (fun j=>volume.real (K∩bad j)) atTop (𝓝 0))
    (hcontain : ∀κ>0,∀ᶠ j in atTop,
      ∀r ∈ selected j,r ∈ K → r  ∉  bad j → |H r| ≤ κ)
    (budget : ℝ)
    (hcontact : ∀ε>0,∀ᶠ j in atTop,
      (∫r in {r | r ∈ K ∧ H r=0},f r∂μ j) ≤ budget+ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop,(∫r in K∩selected j,moving j r∂μ j) ≤ budget+ε := by
  let A := {r | r ∈ K ∧ H r=0}
  have hA : MeasurableSet A := hK.inter (hH (measurableSet_singleton 0))
  have hAsub : A ⊆ K := fun r hr=>hr.1
  have hconst : IntegrableOn (fun _ : ℝ=>B) K := integrableOn_const hfinite
  obtain ⟨q,hq⟩ := levelExcess_uniform_dominated_integral H hH K hK (fun _=>B)
    hconst (fun _ _=>hB) (show 0 < ε/4 by linarith)
  let E := levelExcess H K q
  have hE : MeasurableSet E := levelExcess_measurable H hH K hK q
  have hEsub : E ⊆ K := fun r hr=>hr.1
  let κ := ((q:ℝ)+1)⁻¹
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hbadint : Tendsto (fun j=>∫r in K∩bad j,(B:ℝ)) atTop (𝓝 0) := by
    simpa only [setIntegral_const,smul_eq_mul,mul_comm,mul_zero]
      using hbadlim.const_mul B
  have he := (tendsto_order.mp hL1).2 (ε/4) (by linarith : 0 < ε/4)
  have hbe := (tendsto_order.mp hbadint).2 (ε/4) (by linarith : 0 < ε/4)
  filter_upwards [hcontain κ hκ,hcontact (ε/4) (by linarith),he,hbe] with j hj hc hjerror hjbad
  let D := K∩bad j
  have hD : MeasurableSet D := hK.inter (hbad j)
  have hDsub : D ⊆ K := inter_subset_left
  have hgμ : IntegrableOn (moving j) K (μ j) := (hmoving j).mono_measure (hμ j)
  have hconstμ : IntegrableOn (fun _ : ℝ=>B) K (μ j) := hconst.mono_measure (hμ j)
  let env := fun r=>A.indicator (moving j) r+E.indicator (fun _=>B) r+D.indicator (fun _=>B) r
  have henv : IntegrableOn env K (μ j) :=
    ((hgμ.indicator hA).add (hconstμ.indicator hE)).add (hconstμ.indicator hD)
  have henv0 r (hr : r ∈ K) : 0 ≤ env r := by
    exact add_nonneg (add_nonneg
      (indicator_nonneg (fun r h=> (hb j r (hAsub h)).1) r)
      (indicator_nonneg (fun _ _=>hB) r))
      (indicator_nonneg (fun _ _=>hB) r)
  have hp r (hr : r ∈ K∩selected j) : moving j r ≤ env r := by
    by_cases ha : r ∈ A
    · simp only [env,indicator_of_mem ha]
      linarith [indicator_nonneg (fun _ _=>hB) r (s:=E),
        indicator_nonneg (fun _ _=>hB) r (s:=D)]
    · have hAn : H r ≠ 0 := fun hh=>ha ⟨hr.1,hh⟩
      by_cases hd : r ∈ D
      · simp only [env,indicator_of_notMem ha,indicator_of_mem hd,zero_add]
        linarith [(hb j r hr.1).2,indicator_nonneg (fun _ _=>hB) r (s:=E)]
      · have he : r ∈ E := ⟨hr.1,hj r hr.2 hr.1 (fun hh=>hd ⟨hr.1,hh⟩),hAn⟩
        simp only [env,indicator_of_notMem ha,indicator_of_mem he,zero_add]
        linarith [(hb j r hr.1).2,indicator_nonneg (fun _ _=>hB) r (s:=D)]
  have henvelope := (setIntegral_mono_on (hgμ.mono_set inter_subset_left)
    (henv.mono_set inter_subset_left) (hK.inter (hselected j)) hp).trans
    (setIntegral_mono_set henv ((ae_restrict_mem hK).mono henv0)
      (Eventually.of_forall (fun _ hr=>hr.1)))
  have henvEq : (∫r in K,env r∂μ j)=
      (∫r in A,moving j r∂μ j)+(∫r in E,(B:ℝ)∂μ j)+(∫r in D,(B:ℝ)∂μ j) := by
    change (∫r in K,(A.indicator (moving j)+E.indicator (fun _=>B)) r+D.indicator (fun _=>B) r∂μ j)=_
    rw [integral_add ((hgμ.indicator hA).add (hconstμ.indicator hE))
        (hconstμ.indicator hD)]
    simp only [Pi.add_apply]
    rw [integral_add (hgμ.indicator hA) (hconstμ.indicator hE)]
    rw [setIntegral_indicator hA,setIntegral_indicator hE,setIntegral_indicator hD,
      inter_eq_right.mpr hAsub,inter_eq_right.mpr hEsub,inter_eq_right.mpr hDsub]
  rw [henvEq] at henvelope
  have hcontactdiff := dominated_setIntegral_difference_le A A (Subset.refl _) (μ j) (hμ j)
    f (moving j) (hf.mono_set hAsub) ((hmoving j).mono_set hAsub)
  have hbadbound : (∫r in D,(B:ℝ)∂μ j) ≤ (∫r in D,(B:ℝ)) :=
    integral_mono_measure (Measure.restrict_mono (Subset.refl _) (hμ j))
      (ae_of_all _ (fun _=>hB)) (hconst.mono_set hDsub)
  have hexcess := hq (μ j) (hμ j)
  dsimp only [A,D,E] at *
  linarith

theorem bounded_contact_weights_tendsto_L1
    (A : Set ℝ) (hfinite : volume A ≠ ⊤) (moving : ℕ → ℝ → ℝ) (f : ℝ → ℝ)
    (hmove : ∀j,AEStronglyMeasurable (moving j) (volume.restrict A))
    {B : ℝ} (hb : ∀j,∀ᵐ r ∂volume.restrict A,‖moving j r‖ ≤ B)
    (hlim : ∀ᵐ r ∂volume.restrict A,Tendsto (fun j=>moving j r) atTop (𝓝 (f r))) :
    Tendsto (fun j=>∫r in A,|moving j r-f r|) atTop (𝓝 0) := by
  have hfm := aestronglyMeasurable_of_tendsto_ae _ hmove hlim
  have hfb : ∀ᵐ r ∂volume.restrict A,‖f r‖ ≤ B := by
    filter_upwards [hlim,ae_all_iff.mpr hb] with r hr hbr
    exact le_of_tendsto hr.norm (Eventually.of_forall hbr)
  have hbound j : ∀ᵐ r ∂volume.restrict A,‖|moving j r-f r|‖ ≤ 2*B := by
    filter_upwards [hb j,hfb] with r hr hf
    have hh := norm_sub_le (moving j r) (f r)
    simp only [Real.norm_eq_abs,abs_abs] at *
    linarith
  have hl : ∀ᵐ r ∂volume.restrict A,
      Tendsto (fun j=>|moving j r-f r|) atTop (𝓝 (0:ℝ)) := by
    filter_upwards [hlim] with r hr
    simpa only [sub_self,abs_zero] using (hr.sub_const (f r)).abs
  have ht := tendsto_integral_of_dominated_convergence (μ:=volume.restrict A)
    (fun _=>2*B) (fun j=>(hmove j).sub hfm |>.norm)
    (integrableOn_const hfinite) hbound hl
  simpa only [Real.norm_eq_abs,Pi.sub_apply,integral_zero] using ht

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c  ≤  k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0  ≤  M 1)

theorem comparisonPhysicalContactOnlyVaryingTrace_eventually
    {N d lam : ℝ} (hN : 1  ≤  N) (hlog : 1  ≤  Real.log N) (hd : 0 < d)
    (hnd : 1/N  ≤  d) (hlam : 0 < lam) (hld : lam  ≤  d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ  →  ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0  ≤  h 0) (hlb : lam  ≤  b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H : ℝ  →  ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1  →  H r=0  → 
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u => (b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u => (h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u => (b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u => (h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    (as : ℕ  →  List PositiveMass) (mesh : ℕ  →  ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0  ≤  mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z : ℝ} (ha : 0 < a) (haz : a  ≤  z) (hz : z  ≤  1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r => b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r => h (α.val.val r)) (Icc a z))
    (w : ℝ  →  ℝ) (hw : Measurable w) (hw0 : ∀r,0  ≤  w r)
    (moving : ℕ  →  ℝ  →  ℝ) (hmove : ∀j,Measurable (moving j))
    {B : ℝ} (hwb : ∀r,‖w r‖  ≤  B) (hmb : ∀j r,‖moving j r‖  ≤  B)
    (hB : 0  ≤  B) (hm0 : ∀j r,0  ≤  moving j r)
    (hL1 : Tendsto (fun j=>∫r in {r | r∈Ioo a z ∧ H r=0},
      |deriv α.val.val r*moving j r-deriv α.val.val r*w r|) atTop (𝓝 0))
    (selected bad : ℕ → Set ℝ) (hselected : ∀j,MeasurableSet (selected j))
    (hbad : ∀j,MeasurableSet (bad j))
    (hbadlim : Tendsto (fun j=>volume.real (Ioo a z∩bad j)) atTop (𝓝 0))
    (hcontainH : ∀κ>0,∀ᶠ j in atTop,
      ∀r∈selected j,r∈Ioo a z → r ∉ bad j → |H r| ≤ κ)
    {ε : ℝ} (hε : 0 < ε) :
    let A := {r | r∈Ioo a z ∧ H r=0}
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in Ioo a z∩selected j,
        deriv α.val.val r*moving j r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α (as j) (ho j))  ≤ 
      ((9*Real.log N)/F)*(∫r in A,deriv α.val.val r*w r)+ε := by
  dsimp only
  let K := Ioo a z
  let f := fun r => deriv α.val.val r*w r
  let fm := fun j r => deriv α.val.val r*moving j r
  have hf := comparison_radiusWeight_integrableOn hm hM α ha hz
    K measurableSet_Ioo (Subset.refl _) w hw hwb
  have hfm j := comparison_radiusWeight_integrableOn hm hM α ha hz
    K measurableSet_Ioo (Subset.refl _) (moving j) (hmove j) (hmb j)
  let He := fun r => H (projIcc (0:ℝ) 1 zero_le_one r)
  have hHC : ContinuousOn H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hH.continuousOn
  have hHe : Continuous He :=
    (continuousOn_iff_continuous_domRestrict.mp hHC).comp continuous_projIcc
  have heq r (hr : r∈Icc (0:ℝ) 1) : He r=H r := by
    simp only [He,projIcc_of_mem zero_le_one hr]
  have hr01 r (hr : r∈K) : r∈Icc (0:ℝ) 1 :=
    ⟨ha.le.trans hr.1.le,hr.2.le.trans hz⟩
  let μ := fun j => comparisonPhysicalRadiusMeasure hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)
  have hdom j : μ j  ≤  volume :=
    (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM
      n dphys e d lam b h α (as j) (ho j)).trans Measure.restrict_le_self
  have hcontain : ∀κ>0,∀ᶠ j in atTop,∀r∈selected j,r∈K  →  r ∉ bad j  →  |He r|  ≤  κ := by
    intro κ hκ
    filter_upwards [hcontainH κ hκ] with j hj
    intro r hr hrr hbad
    rw [heq r (hr01 r hrr)]
    exact hj r hr hrr hbad
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let budget := ((9*Real.log N)/F)*(∫r in {r | r∈K ∧ H r=0},f r)
  have hcontactSets : {r | r∈K ∧ He r=0}={r | r∈K ∧ H r=0} := by
    ext r
    constructor <;> intro hr <;> exact ⟨hr.1,by simpa only [heq r (hr01 r hr.1)] using hr.2⟩
  have hcontact : ∀ε'>0,∀ᶠ j in atTop,
      (∫r in {r | r∈K ∧ He r=0},f r∂μ j)  ≤  budget+ε' := by
    intro ε' hε'
    have ht := comparisonPhysicalWeightedContactTrace_eventually hc hk hkc hm hM
      hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero
      as mesh ho hend hmesh hmesh0 hlim ha haz hz Kb Kh hparent hfield
      w hw B (fun r _ _ => hwb r) (fun r _ _ => hw0 r) hε'
    simpa only [hcontactSets,K,f,μ,F,budget] using ht
  have hfinite : volume K≠⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc a z)≠⊤) (measure_mono Ioo_subset_Icc_self)
  have hbound j r (hr : r∈K) : fm j r∈Icc (0:ℝ) (M 1*B) := by
    have hrI : r∈Ioo (0:ℝ) 1 := ⟨ha.trans hr.1,hr.2.trans_le hz⟩
    have hd := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hrI.1 hrI.2)
      (inverseIntegralConstraints_lipschitz hm hM α.property)
    have hd0 := α.val.property.2.deriv_nonneg (x:=r)
    have hmv : moving j r ≤ B := (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using hmb j r)
    refine ⟨mul_nonneg hd0 (hm0 j r),?_⟩
    rw [Real.norm_eq_abs,abs_of_nonneg hd0] at hd
    exact mul_le_mul hd hmv (hm0 j r) hM
  have hL1He : Tendsto (fun j=>∫r in {r | r∈K ∧ He r=0},|fm j r-f r|)
      atTop (𝓝 0) := by simpa only [hcontactSets,K,f,fm] using hL1
  exact dominated_contact_only_varying_trace_transfer He hHe.measurable K measurableSet_Ioo
    hfinite f hf fm hfm (mul_nonneg hM hB) hbound hL1He μ hdom selected bad
    hselected hbad hbadlim hcontain budget hcontact hε

end

end OAI.SKFluctuations.LaplaceWindowFormalization
