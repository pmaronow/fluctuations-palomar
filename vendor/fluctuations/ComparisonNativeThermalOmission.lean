module

public import ComparisonNativeWeightedDefectLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology ENNReal NNReal
set_option maxHeartbeats 2200000

theorem physicalOrderedThermal_removed_mask_budget
    (n : ℕ) (b h : ℝ→ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (v w : ℝ→ℝ) (hv : Measurable v) (hw : Measurable w)
    (hvbound : ∀u∈Ioc (0:ℝ) 1,v u∈Icc (0:ℝ) 1)
    (hwbound : ∀u∈Ioc (0:ℝ) 1,w u∈Icc (0:ℝ) 1)
    (hsub : ∀u∈Ioc (0:ℝ) 1,w u≤v u) :
    let G := fun u=>orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2
    ((∫u in 0..1,v u*G u)-(∫u in 0..1,w u*G u))∈
      Icc (0:ℝ) ((∫u in 0..1,v u)-(∫u in 0..1,w u)) := by
  dsimp only
  let G := fun u=>orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2
  have hG := physicalOrderedThermal_intervalIntegrable n b h hb hh
  have hvG := intervalIntegrable_bounded_measurable_mul hv (show (0:ℝ)≤1 by norm_num) hvbound hG
  have hwG := intervalIntegrable_bounded_measurable_mul hw (show (0:ℝ)≤1 by norm_num) hwbound hG
  have hiV : IntervalIntegrable v volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hv
      (show (0:ℝ)≤1 by norm_num) hvbound (intervalIntegrable_const (c:=(1:ℝ)))
  have hiW : IntervalIntegrable w volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_bounded_measurable_mul hw
      (show (0:ℝ)≤1 by norm_num) hwbound (intervalIntegrable_const (c:=(1:ℝ)))
  have hrow : ∀u∈Ioc (0:ℝ) 1,
      (v u*G u-w u*G u)∈Icc (0:ℝ) (v u-w u) := by
    intro u hu
    have hp := orderedPath_SK_bounds (n+1) (by omega) b h hb hh hu
    have hGu : G u∈Icc (0:ℝ) 1 := by
      dsimp [G]
      constructor <;> nlinarith [hp.2.2.1,hp.2.2.2,sq_nonneg (orderedPathS (n+1) b h u)]
    have hd : 0≤v u-w u := sub_nonneg.mpr (hsub u hu)
    have hn := mul_nonneg hd hGu.1
    have hl := mul_le_of_le_one_right hd hGu.2
    constructor <;> nlinarith
  rw [←intervalIntegral.integral_sub hvG hwG,←intervalIntegral.integral_sub hiV hiW]
  simp only [intervalIntegral.integral_of_le zero_le_one]
  have hiP := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hvG.sub hwG)
  have hiD := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp (hiV.sub hiW)
  constructor
  · apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (hrow u hu).1
  · apply integral_mono_ae hiP hiD
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (hrow u hu).2

theorem physicalOrderedThermal_restore_deleted_bins
    (n : ℕ) (b h : ℝ→ℝ≥0) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1))
    (v w : ℝ→ℝ) (hv : Measurable v) (hw : Measurable w)
    (hvbound : ∀u∈Ioc (0:ℝ) 1,v u∈Icc (0:ℝ) 1)
    (hwbound : ∀u∈Ioc (0:ℝ) 1,w u∈Icc (0:ℝ) 1)
    (hsub : ∀u∈Ioc (0:ℝ) 1,w u≤v u) {B loss : ℝ}
    (hmass : (∫u in 0..1,v u)-(∫u in 0..1,w u)≤loss)
    (hretained : (∫u in 0..1,w u*(orderedPathB (n+1) b h u-
      (orderedPathS (n+1) b h u)^2))≤B) :
    (∫u in 0..1,v u*(orderedPathB (n+1) b h u-(orderedPathS (n+1) b h u)^2))≤B+loss := by
  have h := physicalOrderedThermal_removed_mask_budget n b h hb hh v w hv hw hvbound hwbound hsub
  dsimp only at h
  linarith [h.2]

section Native
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem actual_comparison_thermal_removed_mask_budget
    (n : ℕ) {d lam : ℝ} (hd : d≠0) (hlam : 0≤lam)
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (v w : ℝ→ℝ) (hv : Measurable v) (hw : Measurable w)
    (hvbound : ∀u∈Ioc (0:ℝ) 1,v u∈Icc (0:ℝ) 1)
    (hwbound : ∀u∈Ioc (0:ℝ) 1,w u∈Icc (0:ℝ) 1)
    (hsub : ∀u∈Ioc (0:ℝ) 1,w u≤v u) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let G := fun u=>orderedPathB (n+1) bf hf u-(orderedPathS (n+1) bf hf u)^2
    ((∫u in 0..1,v u*G u)-(∫u in 0..1,w u*G u))∈
      Icc (0:ℝ) ((∫u in 0..1,v u)-(∫u in 0..1,w u)) := by
  dsimp only
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h
    hd hlam hlb hb hh hh0 α
  exact physicalOrderedThermal_removed_mask_budget n _ _
    (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) v w hv hw hvbound hwbound hsub

end Native
end OAI.SKFluctuations.LaplaceWindowFormalization
