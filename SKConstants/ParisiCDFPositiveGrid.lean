module

public import SKConstants.ParisiCDFPositiveApproximation
public import SKConstants.ParisiCDFMovingJets
public import SKConstants.ParisiGridLimit

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

def positiveGridCDF (α : StieltjesFunction ℝ) (n : ℕ) : StieltjesFunction ℝ :=
  positiveStieltjesCDF α (parisiGridMesh n) (parisiGridMesh n).coe_nonneg

def positiveGridFunction (α : StieltjesFunction ℝ) (n : ℕ) : ℝ → ℝ :=
  gridCDF (positiveGridCDF α n) (parisiGridMesh n)

lemma positiveGridCDF_bounds (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (n : ℕ) (r : ℝ) :
    positiveGridCDF α n r ∈ Icc (0:ℝ) 1 :=
  positiveStieltjesCDF_bounds α ha _ _ r

lemma positiveGridCDF_one (α : StieltjesFunction ℝ) (h1 : α 1=1) (n : ℕ) :
    positiveGridCDF α n 1=1 := positiveStieltjesCDF_one α h1 _ _

lemma positiveGridCDF_pos (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (n : ℕ) (r : ℝ) : 0 < positiveGridCDF α n r :=
  positiveStieltjesCDF_pos α ha _ (by exact_mod_cast parisiGridMesh_pos n) r

def positiveGridIndex (q : ℝ) (n : ℕ) : ℕ := ⌊q/(parisiGridMesh n:ℝ)⌋₊

def positiveGridTime (q : ℝ) (n : ℕ) : ℝ≥0 :=
  (positiveGridIndex q n:ℝ≥0)*parisiGridMesh n

lemma positiveGridTime_le {q : ℝ} (hq0 : 0 ≤ q) (n : ℕ) : (positiveGridTime q n:ℝ) ≤ q := by
  have H := Nat.floor_le (div_nonneg hq0 (parisiGridMesh n).coe_nonneg)
  exact (le_div_iff₀ (by exact_mod_cast parisiGridMesh_pos n)).mp H

lemma positiveGridTime_lower (q : ℝ) (n : ℕ) : q-(parisiGridMesh n:ℝ) < positiveGridTime q n := by
  have H := Nat.lt_floor_add_one (q/(parisiGridMesh n:ℝ))
  have H' := (div_lt_iff₀ (by exact_mod_cast parisiGridMesh_pos n)).mp H
  change q-(parisiGridMesh n:ℝ) < (positiveGridIndex q n:ℝ)*(parisiGridMesh n:ℝ)
  unfold positiveGridIndex
  nlinarith

lemma positiveGridTime_tendsto {q : ℝ} (hq0 : 0 ≤ q) :
    Tendsto (fun n => (positiveGridTime q n:ℝ)) atTop (𝓝 q) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun n => q-(parisiGridMesh n:ℝ)) atTop (𝓝 q) by
      simpa only [sub_zero] using tendsto_const_nhds.sub parisiGridMesh_coe_tendsto)
    tendsto_const_nhds
    (fun n => (positiveGridTime_lower q n).le) (positiveGridTime_le hq0)

lemma positiveGridIndex_lt {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) (n : ℕ) :
    positiveGridIndex q n < n+1 := by
  unfold positiveGridIndex
  rw [Nat.floor_lt (div_nonneg hq.1 (parisiGridMesh n).coe_nonneg),
    div_lt_iff₀ (by exact_mod_cast parisiGridMesh_pos n)]
  have H : ((n+1:ℕ):ℝ)*(parisiGridMesh n:ℝ)=1 := by
    exact_mod_cast parisiGridMesh_horizon n
  rw [H]
  exact hq.2

lemma positiveGridIndex_pos_eventually {q : ℝ} (hq : 0 < q) :
    ∀ᶠ n in atTop, 0 < positiveGridIndex q n := by
  filter_upwards [parisiGridMesh_coe_tendsto.eventually (gt_mem_nhds hq)] with n hn
  rw [positiveGridIndex,Nat.floor_pos,le_div_iff₀ (by exact_mod_cast parisiGridMesh_pos n)]
  simpa only [one_mul] using hn.le

lemma positiveGridFunction_bounds (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (n : ℕ) (r : ℝ) :
    positiveGridFunction α n r ∈ Icc (0:ℝ) 1 := positiveGridCDF_bounds α ha n _

lemma positiveGridFunction_mono (α : StieltjesFunction ℝ) (n : ℕ) :
    Monotone (positiveGridFunction α n) :=
  gridCDF_mono (positiveGridCDF α n).mono (by exact_mod_cast parisiGridMesh_pos n)

lemma positiveGridFunction_interval_error (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (n : ℕ) {s t : ℝ}
    (hst : s ≤ t) (hdur : t-s ≤ 1) :
    (∫ z in s..t, |positiveGridFunction α n z-α z|) ≤ 2*(parisiGridMesh n:ℝ) := by
  let γ := positiveGridCDF α n
  have hi1 : IntervalIntegrable (fun z => |positiveGridFunction α n z-γ z|) volume s t :=
    ((positiveGridFunction_mono α n).intervalIntegrable.sub γ.mono.intervalIntegrable).abs
  have hi2 : IntervalIntegrable (fun z => |γ z-α z|) volume s t :=
    (γ.mono.intervalIntegrable.sub α.mono.intervalIntegrable).abs
  have hi : IntervalIntegrable (fun z => |positiveGridFunction α n z-α z|) volume s t :=
    ((positiveGridFunction_mono α n).intervalIntegrable.sub α.mono.intervalIntegrable).abs
  have H := intervalIntegral.integral_mono hst hi (hi1.add hi2)
    (fun z => abs_sub_le _ (γ z) _)
  rw [intervalIntegral.integral_add hi1 hi2] at H
  have H1 := gridCDF_interval_integral_abs_error γ.mono (positiveGridCDF_bounds α ha n)
    (by exact_mod_cast parisiGridMesh_pos n) hst
  change (∫ z in s..t, |positiveGridFunction α n z-γ z|) ≤ (parisiGridMesh n:ℝ) at H1
  have H2 := intervalIntegral.integral_mono hst hi2 (intervalIntegrable_const (c := (parisiGridMesh n:ℝ)))
    (positiveStieltjesCDF_error α ha (parisiGridMesh n) (parisiGridMesh n).coe_nonneg)
  simp only [intervalIntegral.integral_const,smul_eq_mul] at H2
  have H3 := mul_le_mul_of_nonneg_right hdur (parisiGridMesh n).coe_nonneg
  linarith

theorem positiveGridValue_jets_tendsto (β : ℝ) (hβ : β ≠ 0)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    {q : ℝ} (hq : q ∈ Ico (0:ℝ) 1) (m : ℕ) :
    TendstoUniformly (fun n => iteratedDeriv m (scalarCDFValue β (positiveGridFunction α n)
      (positiveGridTime q n) (Real.toNNReal (1-(positiveGridTime q n:ℝ)))))
      (iteratedDeriv m (scalarCDFValue β α q (Real.toNNReal (1-q)))) atTop := by
  apply scalarCDFValue_moving_time_jets_uniform hβ α ha h1 (positiveGridFunction α)
    (positiveGridFunction_bounds α ha) (positiveGridFunction_mono α)
    (fun n => (positiveGridTime q n:ℝ)) (fun n => 2*(parisiGridMesh n:ℝ))
    hq.2 ⟨hq.1,le_rfl⟩
    (fun n => ⟨(positiveGridTime q n).coe_nonneg,positiveGridTime_le hq.1 n⟩)
    (positiveGridTime_tendsto hq.1)
    (by simpa only [mul_zero] using parisiGridMesh_coe_tendsto.const_mul 2) ?_ m
  intro n
  apply positiveGridFunction_interval_error α ha n
    (le_add_of_nonneg_right (Real.toNNReal (1-(positiveGridTime q n:ℝ))).coe_nonneg)
  simp only [add_sub_cancel_left]
  rw [Real.coe_toNNReal _ (by linarith [positiveGridTime_le hq.1 n,hq.2])]
  linarith [(positiveGridTime q n).coe_nonneg]

lemma positiveGridCoefficient_tendsto (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) {q : ℝ} (hq0 : 0 ≤ q) (hcont : ContinuousAt α q) :
    Tendsto (fun n => (gridCDFCoefficient (positiveGridCDF α n) (parisiGridMesh n)
      (positiveGridIndex q n):ℝ)) atTop (𝓝 (α q)) := by
  have H := hcont.tendsto.comp (positiveGridTime_tendsto hq0)
  have HE := parisiGridMesh_coe_tendsto
  have HD := tendsto_const_nhds.add HE (a := (1:ℝ))
  have HL := (HE.add H).div HD (by norm_num : (1:ℝ)+0 ≠ 0)
  simp only [zero_add,one_div_one] at HL
  convert HL using 1
  · funext n
    unfold gridCDFCoefficient
    rw [Real.coe_toNNReal _ (positiveGridCDF_bounds α ha n _).1]
    rfl
  · simp

end SKConstants.ParisiFullSupport
