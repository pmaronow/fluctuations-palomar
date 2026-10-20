module

public import ComparisonMacroscopicScalarAttainment
public import ActualStrengthVariationalLimit
public import ComparisonPerturbedEndpointBand

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Function
open scoped Topology NNReal

theorem jointScalarVariationalValue_radius_scalar_minimizer
    {β : ℝ≥0} (hβ : 0 < β) {c : ℝ} (hc : 0 < c)
    (e r : ℝ→ℝ) (he : AntitoneOn e (Icc (0:ℝ) 1))
    (heb : ∀u∈Icc (0:ℝ) 1,e u∈Icc c ((β:ℝ)^2-c))
    (her : MonotoneOn (fun u=>e u*r u) (Icc (0:ℝ) 1))
    (hr : MonotoneOn r (Icc (0:ℝ) 1))
    (hrb : ∀u∈Icc (0:ℝ) 1,r u∈Icc (0:ℝ) 1)
    (hv : jointScalarVariationalValue ((β:ℝ)^2) e r≤normalizedScalarParisiReference β) :
    quantileMassProfile r hrb ∈ scalarReferenceMinimizers β hβ := by
  let T := (β:ℝ)^2
  have hT : 0 < T := sq_pos_of_pos (NNReal.coe_pos.mpr hβ)
  have heb' : ∀u∈Icc (0:ℝ) 1,e u∈Icc (0:ℝ) T :=
    fun u hu=>⟨hc.le.trans (heb u hu).1,(heb u hu).2.trans (sub_le_self _ hc.le)⟩
  have hb : MonotoneOn (fun u=>T-e u) (Icc (0:ℝ) 1) :=
    fun _ hu _ hv huv=>sub_le_sub_left (he hu hv huv) T
  have hbb : ∀u∈Icc (0:ℝ) 1,T-e u∈Icc (0:ℝ) T :=
    fun u hu=>⟨sub_nonneg.mpr (heb' u hu).2,sub_le_self _ (heb' u hu).1⟩
  obtain ⟨z,hz,hzmin⟩ := macroScalarMinimum_attained (fun u=>T-e u) (fun u=>e u*r u)
    hT.le hb her hbb (mul_nonneg (heb' 0 (by norm_num)).1 (hrb 0 (by norm_num)).1)
  have hjoint : physicalJointQuantileValue 1 T e r z≤normalizedScalarParisiReference β := by
    rw [physicalJointQuantileValue_generalScalar T e r z he heb' her hr
      (fun u hu=>(hrb u hu).1) hz.1 (fun u hu=>(hz.2 u hu).1),hzmin]
    exact hv
  have hscalar : physicalScalarQuantileValue 1 T r≤normalizedScalarParisiReference β := by
    apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    have ha : 0 < epsilon/T := div_pos hepsilon hT
    have hnear := joint_near_minimum_radius_value hβ 1 (by norm_num) hc ha e r z
      he heb her hr hz.1 hrb hz.2 (E := 0) (by simpa using hjoint)
    change physicalScalarQuantileValue 1 T r ≤ normalizedScalarParisiReference β +
      0 + T * (epsilon/T + ((4*T*0)/c^2)/(4*(epsilon/T))) at hnear
    simpa only [zero_add,mul_zero,zero_div,add_zero,mul_div_cancel₀ _ hT.ne'] using hnear
  have heq : physicalScalarQuantileValue 1 T r=normalizedScalarParisiReference β := by
    apply le_antisymm hscalar
    rw [← scalar_physical_quantile_value 1 (by norm_num) hT r hr hrb]
    exact normalizedScalarParisiReference_le_value hβ _
  exact ⟨quantileMassProfile_mem r hrb,by
    change scalarParisiValue hT (quantileMassProfile r hrb) = normalizedScalarParisiReference β
    rw [scalar_physical_quantile_value 1 (by norm_num) hT r hr hrb]
    exact heq⟩

theorem actualStrengthComparisonPressure_tendsto_jointScalar_of_endpoint_cost
    (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    {dseq lamseq : ℕ→ℝ} {d lam T : ℝ}
    (hd0 : d≠0) (hds : ∀n,dseq n≠0)
    (hd : Tendsto dseq atTop (𝓝 d)) (hlam : Tendsto lamseq atTop (𝓝 lam))
    (hlamb : ∀n,lamseq n∈Icc (0:ℝ) T) (hlamT : lam∈Ioo (0:ℝ) T)
    {rseq : ℕ→boundedMassProfiles} {r : boundedMassProfiles}
    (hr : Tendsto rseq atTop (𝓝 r))
    (bseq hseq : ℕ→ℝ→ℝ)
    (hadmissible : ∀n,comparisonClockAdmissible (bseq n) (hseq n)
      (fun u=>laplaceComparisonStrength (dseq n) (lamseq n) ((rseq n).val u)) (rseq n).val)
    (hcost : Tendsto (fun n=>comparisonEndpointL1Cost T (bseq n) (hseq n)) atTop (𝓝 0)) :
    Tendsto (fun n=>pathCompensatedPressure (N n) (bseq n) (hseq n)
      (fun u=>laplaceComparisonStrength (dseq n) (lamseq n) ((rseq n).val u))
      (rseq n).val 0) atTop
      (𝓝 (jointScalarVariationalValue T
        (fun u=>laplaceComparisonStrength d lam (r.val u)) r.val)) := by
  have hconstant := actualStrengthComparisonPressure_tendsto_jointScalar N hN hd0 hds hd hlam
    hlamb hlamT hr
  have hdiff : Tendsto (fun n=>pathCompensatedPressure (N n) (bseq n) (hseq n)
      (fun u=>laplaceComparisonStrength (dseq n) (lamseq n) ((rseq n).val u)) (rseq n).val 0-
    pathCompensatedPressure (N n) (fun _=>T) (fun _=>0)
      (fun u=>laplaceComparisonStrength (dseq n) (lamseq n) ((rseq n).val u)) (rseq n).val 0)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    apply squeeze_zero' (Eventually.of_forall fun _=>abs_nonneg _) _ hcost
    filter_upwards [hN.eventually (eventually_gt_atTop (0:ℕ))] with n hn
    exact actualComparison_endpoint_cost (N n) hn (hds n) (hlamb n).1 (hlamb n).2
      (bseq n) (hseq n) (rseq n) (hadmissible n)
  simpa only [sub_add_cancel,zero_add] using hdiff.add hconstant

theorem actualStrength_radius_limit_scalar_minimizer_of_endpoint_cost
    {β : ℝ≥0} (hβ : 0 < β) (N : ℕ→ℕ) (hN : Tendsto N atTop atTop)
    {dseq lamseq : ℕ→ℝ} {d lam : ℝ}
    (hd0 : d≠0) (hds : ∀n,dseq n≠0)
    (hd : Tendsto dseq atTop (𝓝 d)) (hlam : Tendsto lamseq atTop (𝓝 lam))
    (hlamb : ∀n,lamseq n∈Icc (0:ℝ) ((β:ℝ)^2))
    (hlamT : lam∈Ioo (0:ℝ) ((β:ℝ)^2))
    {rseq : ℕ→boundedMassProfiles} {r : boundedMassProfiles}
    (hr : Tendsto rseq atTop (𝓝 r)) (bseq hseq : ℕ→ℝ→ℝ)
    (hadmissible : ∀n,comparisonClockAdmissible (bseq n) (hseq n)
      (fun u=>laplaceComparisonStrength (dseq n) (lamseq n) ((rseq n).val u)) (rseq n).val)
    (hcost : Tendsto (fun n=>comparisonEndpointL1Cost ((β:ℝ)^2) (bseq n) (hseq n)) atTop (𝓝 0))
    (error : ℕ→ℝ) (herror : Tendsto error atTop (𝓝 0))
    (hupper : ∀ᶠn in atTop,pathCompensatedPressure (N n) (bseq n) (hseq n)
      (fun u=>laplaceComparisonStrength (dseq n) (lamseq n) ((rseq n).val u))
      (rseq n).val 0≤normalizedScalarParisiReference β+error n) :
    quantileMassProfile r.val (fun u _=>r.property.1 u) ∈ scalarReferenceMinimizers β hβ := by
  have hp := actualStrengthComparisonPressure_tendsto_jointScalar_of_endpoint_cost
    N hN hd0 hds hd hlam hlamb hlamT hr bseq hseq hadmissible hcost
  have hu : Tendsto (fun n=>normalizedScalarParisiReference β+error n) atTop
      (𝓝 (normalizedScalarParisiReference β)) := by
    simpa only [add_zero] using herror.const_add (normalizedScalarParisiReference β)
  have hv := le_of_tendsto_of_tendsto hp hu hupper
  obtain ⟨c,hc,he,heb,her⟩ := actualStrength_profile_geometry hd0 hlamT r
  exact jointScalarVariationalValue_radius_scalar_minimizer hβ hc _ _ he heb her
    (r.property.2.monotoneOn _) (fun u _=>r.property.1 u) hv

end OAI.SKFluctuations.LaplaceWindowFormalization
