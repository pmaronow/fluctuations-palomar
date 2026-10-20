module
public import SKConstants.GrowingQueryMesh

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def paperGrowingQueryMeshSize (a : ℝ) (n : ℕ) : ℝ≥0 := ((n:ℝ)^(-a)).toNNReal

def paperGrowingQueryHorizon (F : ℝ) (n : ℕ) : ℝ≥0 := (F*Real.log (n:ℝ)).toNNReal

lemma paperGrowingQueryMeshSize_pos (a : ℝ) (n : ℕ) (hn : 0<n) :
    0<paperGrowingQueryMeshSize a n := by
  apply Real.toNNReal_pos.mpr
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

lemma paperGrowingQueryMeshSize_coe (a : ℝ) (n : ℕ) :
    (paperGrowingQueryMeshSize a n:ℝ)=(n:ℝ)^(-a) :=
  Real.coe_toNNReal _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)

lemma paperGrowingQueryHorizon_coe (F : ℝ) (hF : 0≤F) (n : ℕ) (hn : 0<n) :
    (paperGrowingQueryHorizon F n:ℝ)=F*Real.log (n:ℝ) := by
  apply Real.coe_toNNReal
  exact mul_nonneg hF (Real.log_nonneg (by exact_mod_cast hn))

lemma paperGrowingQuery_scale_identity (a F : ℝ) (hF : 0≤F) (n : ℕ) (hn : 0<n) :
    (paperGrowingQueryMeshSize a n:ℝ)*Real.exp ((paperGrowingQueryHorizon F n:ℝ)/4)=
      (n:ℝ)^(F/4-a) := by
  rw [paperGrowingQueryMeshSize_coe,paperGrowingQueryHorizon_coe F hF n hn]
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn),Real.rpow_def_of_pos (by exact_mod_cast hn),
    ← Real.exp_add]
  congr 1
  ring

lemma paperGrowingQuery_scale_le_one (a F : ℝ) (hF : 0≤F) (ha : F/4≤a) (n : ℕ) (hn : 0<n) :
    (paperGrowingQueryMeshSize a n:ℝ)*Real.exp ((paperGrowingQueryHorizon F n:ℝ)/4)≤1 := by
  rw [paperGrowingQuery_scale_identity a F hF n hn]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (by linarith)

def paperGrowingQueryStop (a F : ℝ) (n : ℕ) (hn : 0<n) : ℕ :=
  growingQueryStop (paperGrowingQueryMeshSize a n) (paperGrowingQueryMeshSize_pos a n hn)
    (paperGrowingQueryHorizon F n)

lemma paperGrowingQueryStop_small (a F : ℝ) (hF : 0≤F) (ha : F/4≤a) (n : ℕ) (hn : 0<n) :
    ∀ j<paperGrowingQueryStop a F n hn, growingQueryDuration (paperGrowingQueryMeshSize a n) j≤1 :=
  growingQueryStop_small _ _ _ (paperGrowingQuery_scale_le_one a F hF ha n hn)

lemma paperGrowingQueryStop_count_bound (a F : ℝ) (hF : 0≤F) (ha : F/4≤a) (n : ℕ) (hn : 0<n) :
    (paperGrowingQueryStop a F n hn:ℝ)≤8*(n:ℝ)^a := by
  have hc := growingQueryStop_count_bound _ (paperGrowingQueryMeshSize_pos a n hn)
    (paperGrowingQueryHorizon F n) (paperGrowingQuery_scale_le_one a F hF ha n hn)
  change _ ≤ _ at hc
  rw [paperGrowingQueryMeshSize_coe,Real.rpow_neg (Nat.cast_nonneg _),div_inv_eq_mul] at hc
  exact hc

lemma paperGrowingQueryStop_horizon (a F : ℝ) (hF : 0≤F) (ha : F/4≤a) (n : ℕ) (hn : 0<n) :
    F*Real.log (n:ℝ)≤(growingQueryTime (paperGrowingQueryMeshSize a n) (paperGrowingQueryStop a F n hn):ℝ) ∧
    (growingQueryTime (paperGrowingQueryMeshSize a n) (paperGrowingQueryStop a F n hn):ℝ)≤F*Real.log (n:ℝ)+1 := by
  have hl := growingQueryStop_reaches _ (paperGrowingQueryMeshSize_pos a n hn) (paperGrowingQueryHorizon F n)
  have hu := growingQueryStop_overshoot _ (paperGrowingQueryMeshSize_pos a n hn) (paperGrowingQueryHorizon F n)
  rw [paperGrowingQueryHorizon_coe F hF n hn] at hu
  constructor
  · have h := NNReal.coe_le_coe.mpr hl
    simpa only [paperGrowingQueryHorizon_coe F hF n hn,paperGrowingQueryStop] using h
  · exact hu.trans (add_le_add_right (by
      simpa only [paperGrowingQueryHorizon_coe F hF n hn] using paperGrowingQuery_scale_le_one a F hF ha n hn) _)

end SKConstants
