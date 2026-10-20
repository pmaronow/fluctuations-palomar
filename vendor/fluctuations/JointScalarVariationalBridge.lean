module

public import GeneralClockCongruence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators

def jointScalarVariationalValue (T : ℝ) (e r : ℝ → ℝ) : ℝ :=
  generalScalarMinimum (fun u => T-e u) (fun u => e u*r u)+
    (1/4:ℝ)*(∫u in (0:ℝ)..1,e u*r u^2)

theorem joint_radius_penalty_integrable (e r : ℝ → ℝ)
    (her : MonotoneOn (fun u => e u*r u) (Icc (0:ℝ) 1))
    (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (hen : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ e u)
    (hrn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ r u) :
    IntervalIntegrable (fun u => e u*r u^2) volume 0 1 := by
  have hm : MonotoneOn (fun u => e u*r u^2) (Icc (0:ℝ) 1) := by
    intro u hu v hv huv
    have hp := mul_le_mul (her hu hv huv) (hr hu hv huv) (hrn u hu)
      (mul_nonneg (hen v hv) (hrn v hv))
    nlinarith
  exact (show MonotoneOn (fun u => e u*r u^2) (uIcc (0:ℝ) 1) by simpa using hm).intervalIntegrable

theorem physicalJointQuantileValue_generalScalar (T : ℝ) (e r z : ℝ → ℝ)
    (he : AntitoneOn e (Icc (0:ℝ) 1))
    (heb : ∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc (0:ℝ) T)
    (her : MonotoneOn (fun u => e u*r u) (Icc (0:ℝ) 1))
    (hr : MonotoneOn r (Icc (0:ℝ) 1)) (hrn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ r u)
    (hz : MonotoneOn z (Icc (0:ℝ) 1)) (hzn : ∀ u ∈ Icc (0:ℝ) 1, 0 ≤ z u) :
    physicalJointQuantileValue 1 T e r z=
      generalScalarQuantileValue (fun u => T-e u) (fun u => e u*r u) z+
        (1/4:ℝ)*(∫u in (0:ℝ)..1,e u*r u^2) := by
  have hi := joint_radius_penalty_integrable e r her hr (fun u hu => (heb u hu).1) hrn
  have hj := weighted_quantile_power_integrable (fun u => T-e u) z
    (fun _ hu _ hv huv => sub_le_sub_left (he hu hv huv) T) hz
    (fun u hu => sub_nonneg.mpr (heb u hu).2) hzn 2
  unfold physicalJointQuantileValue generalScalarQuantileValue massStrengthObjective
  rw [intervalIntegral.integral_add hi hj]
  ring

theorem jointScalarVariationalValue_lower {β : ℝ≥0} (hβ : 0 < β) {c : ℝ} (hc : 0 < c)
    (e r : ℝ → ℝ) (he : AntitoneOn e (Icc (0:ℝ) 1))
    (heb : ∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc c ((β:ℝ)^2-c))
    (her : MonotoneOn (fun u => e u*r u) (Icc (0:ℝ) 1))
    (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (hrb : ∀ u ∈ Icc (0:ℝ) 1, r u ∈ Icc (0:ℝ) 1) :
    normalizedScalarParisiReference β ≤ jointScalarVariationalValue ((β:ℝ)^2) e r := by
  let T := (β:ℝ)^2
  have hT : 0 < T := sq_pos_of_pos (NNReal.coe_pos.mpr hβ)
  have heb' : ∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc (0:ℝ) T :=
    fun u hu => ⟨hc.le.trans (heb u hu).1,(heb u hu).2.trans (sub_le_self _ hc.le)⟩
  have hlo : normalizedScalarParisiReference β-(1/4:ℝ)*(∫u in (0:ℝ)..1,e u*r u^2) ≤
      generalScalarMinimum (fun u => T-e u) (fun u => e u*r u) := by
    apply le_csInf (generalScalarQuantileValues_nonempty _ _)
    rintro v ⟨z,hz,rfl⟩
    obtain ⟨hco,href⟩ := joint_quantile_coercivity hβ 1 (by norm_num) hc e r z he heb her hr hz.1 hrb hz.2
    have hnon : 0 ≤ c^2/(4*T)*(∫u in (0:ℝ)..1,(r u-z u)^2) := by
      apply mul_nonneg (by positivity)
      exact intervalIntegral.integral_nonneg (by norm_num : (0:ℝ) ≤ 1) (fun _ _ => sq_nonneg _)
    rw [physicalJointQuantileValue_generalScalar T e r z he heb' her hr
      (fun u hu => (hrb u hu).1) hz.1 (fun u hu => (hz.2 u hu).1)] at hco
    linarith
  unfold jointScalarVariationalValue
  linarith

theorem jointScalarVariational_near_minimizers_fixed_band {β : ℝ≥0} (hβ : 0 < β)
    (hT1 : 1 < (β:ℝ)^2) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ∃ cR CR epsilon : ℝ, 0 < cR ∧ 0 < CR ∧ 0 < epsilon ∧
      ∀ e r : ℝ → ℝ,
      AntitoneOn e (Icc (0:ℝ) 1) →
      (∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc c ((β:ℝ)^2-c)) →
      MonotoneOn (fun u => e u*r u) (Icc (0:ℝ) 1) →
      MonotoneOn r (Icc (0:ℝ) 1) →
      (∀ u ∈ Icc (0:ℝ) 1, r u ∈ Icc (0:ℝ) 1) →
      jointScalarVariationalValue ((β:ℝ)^2) e r ≤ normalizedScalarParisiReference β+epsilon →
      ∀ u ∈ Ioo (0:ℝ) 1, x ≤ u → cR*u ≤ r u ∧ r u ≤ CR*u := by
  obtain ⟨cR,CR,epsilon,hcR,hCR,heps,hband⟩ := joint_near_minimizers_fixed_band hβ hT1 hc hx
  refine ⟨cR,CR,epsilon/2,hcR,hCR,by positivity,?_⟩
  intro e r he heb her hr hrb hv
  let T := (β:ℝ)^2
  have hT : 0 < T := sq_pos_of_pos (NNReal.coe_pos.mpr hβ)
  have heb' : ∀ u ∈ Icc (0:ℝ) 1, e u ∈ Icc (0:ℝ) T :=
    fun u hu => ⟨hc.le.trans (heb u hu).1,(heb u hu).2.trans (sub_le_self _ hc.le)⟩
  have hb : MonotoneOn (fun u => T-e u) (Icc (0:ℝ) 1) :=
    fun _ hu _ hv huv => sub_le_sub_left (he hu hv huv) T
  have hbb : ∀ u ∈ Icc (0:ℝ) 1, T-e u ∈ Icc (0:ℝ) T :=
    fun u hu => ⟨sub_nonneg.mpr (heb' u hu).2,sub_le_self _ (heb' u hu).1⟩
  have hbelow := generalScalarQuantileValues_bddBelow (fun u => T-e u) (fun u => e u*r u)
    hT.le hb her hbb (mul_nonneg (heb' 0 (by norm_num)).1 (hrb 0 (by norm_num)).1)
  obtain ⟨v,hv',hvlt⟩ := (csInf_lt_iff hbelow (generalScalarQuantileValues_nonempty _ _)).mp
    (show generalScalarMinimum (fun u => T-e u) (fun u => e u*r u)<
      generalScalarMinimum (fun u => T-e u) (fun u => e u*r u)+epsilon/2 by linarith)
  obtain ⟨z,hz,rfl⟩ := hv'
  apply hband 1 (by norm_num) e r z he heb her hr hz.1 hrb hz.2
  rw [physicalJointQuantileValue_generalScalar T e r z he heb' her hr
    (fun u hu => (hrb u hu).1) hz.1 (fun u hu => (hz.2 u hu).1)]
  unfold jointScalarVariationalValue at hv
  linarith

end OAI.SKFluctuations.LaplaceWindowFormalization
