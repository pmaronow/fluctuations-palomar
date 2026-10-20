module

public import SKConstants.ParisiCDFCoordinateCutoff

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace SKConstants.ParisiFullSupport
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.ZeroTemperatureSK.WeakIto SKConstantsOAI.SK.Analytic
variable {Ω : Type*} [MeasurableSpace Ω]
variable (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
  (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) (hβ : β≠0)
  {T : ℝ} (hT0 : 0≤T) (hT1 : T<1)

def physicalCDFCoordinateExpected (W : BrownianSystem Ω) (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z∈Icc (0:ℝ) 1) (h1 : α 1=1) (T v : ℝ) : ℝ :=
  ∫ w, finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal v) w*
    compactCDFJet β α T 0 (v/β^2)
      (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal v) w) ∂W.law

lemma physicalCDFCoordinateCutoffField_f (n : ℕ) (v x : ℝ) :
    (physicalCDFCoordinateCutoffField β α ha h1 hβ hT0 hT1 n).f v x=
      scalarSmoothCutoff n x*compactCDFJet β α T 0 (v/β^2) x := by
  unfold physicalCDFCoordinateCutoffField TimeField.mul staticTimeField physicalCDFJetField rescaleTimeField
    compactCDFJetField
  dsimp only
  rw [show (1/β^2)*v=v/β^2 by ring]

lemma physicalCDFCoordinateCutoff_expected_tendsto (V : ℝ) :
    Tendsto (fun n => (physicalCDFCoordinateCutoffField β α ha h1 hβ hT0 hT1 n).expected
      (finiteTemperatureCDFDrift β α ha h1) W V) atTop
      (𝓝 (physicalCDFCoordinateExpected W β α ha h1 T V)) := by
  let := W.isProbability
  obtain ⟨C,hC⟩ := (compactCDFGradient_family β α ha h1 hβ hT0 hT1).bound
  have hm (n : ℕ) := (integrable_family_comp (P:=W.law)
    (physicalCDFCoordinateCutoffField β α ha h1 hβ hT0 hT1 n).smooth V
    ((finiteTemperatureCDFDrift β α ha h1).solution_measurable W (Real.toNNReal V))).aestronglyMeasurable
  unfold TimeField.expected
  unfold physicalCDFCoordinateExpected
  apply tendsto_integral_of_dominated_convergence
    (fun w => |(finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal V) w| * (C:ℝ))
    hm (((finiteTemperatureCDFDrift β α ha h1).solution_integrable W (Real.toNNReal V)).abs.mul_const _) _ _
  · intro n
    filter_upwards [] with w
    rw [physicalCDFCoordinateCutoffField_f]
    simp only [Real.norm_eq_abs,abs_mul]
    exact mul_le_mul (scalarSmoothCutoff_abs_le n _)
      (by simpa only [compactCDFJet,iteratedDeriv_zero] using hC (V/β^2) _)
      (abs_nonneg _) (abs_nonneg _)
  · filter_upwards [] with w
    simpa only [physicalCDFCoordinateCutoffField_f,finiteTemperatureCDFProcess] using (scalarSmoothCutoff_tendsto
      ((finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal V) w)).mul_const
      (compactCDFJet β α T 0 (V/β^2)
        ((finiteTemperatureCDFDrift β α ha h1).solution W.driver (Real.toNNReal V) w))

include ha h1 hβ hT0 hT1 in
lemma physicalCDFCoordinateCutoffRate_uniform_bound :
    ∃ C : ℝ≥0, ∀ n v x, |physicalCDFCoordinateCutoffRate β α T n v x|≤C := by
  obtain ⟨A,hA⟩ := (physicalCDFCoordinateRate_family β α ha h1 hβ hT0 hT1).bound
  obtain ⟨B,hB⟩ := (compactCDFGradient_family β α ha h1 hβ hT0 hT1).bound
  refine ⟨A+B,?_⟩
  intro n v x
  have hmesh : (parisiGridMesh n:ℝ)≤1 := by
    have hn : (1:ℝ)≤((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_pos n
    have HH : ((n+1:ℕ):ℝ)*(parisiGridMesh n:ℝ)=1 := by exact_mod_cast parisiGridMesh_horizon n
    nlinarith [(parisiGridMesh n).coe_nonneg]
  have hD := scalarSmoothCutoff_deriv_bounds n x
  have hDD := (scalarSmoothCutoff_second_deriv_bound n x).trans (mul_le_mul_of_nonneg_left hmesh (by norm_num : (0:ℝ)≤2))
  simp only [mul_one] at hDD
  unfold physicalCDFCoordinateCutoffRate
  calc
    _ ≤ |deriv (scalarSmoothCutoff n) x| * |physicalCDFCoordinateRate β α T v x|+
      (1/2:ℝ)*(|deriv (deriv (scalarSmoothCutoff n)) x| * |compactCDFJet β α T 0 (v/β^2) x|) := by
        simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<1/2)] using abs_add_le
          (deriv (scalarSmoothCutoff n) x*physicalCDFCoordinateRate β α T v x)
          ((1/2:ℝ)*(deriv (deriv (scalarSmoothCutoff n)) x*compactCDFJet β α T 0 (v/β^2) x))
    _ ≤ 1*(A:ℝ)+(1/2:ℝ)*(2*(B:ℝ)) := by
      apply add_le_add
      · exact mul_le_mul (by simpa only [abs_of_nonneg hD.1] using hD.2) (hA v x) (abs_nonneg _) (by norm_num)
      · exact mul_le_mul_of_nonneg_left (mul_le_mul hDD
          (by simpa only [compactCDFJet,iteratedDeriv_zero] using hB (v/β^2) x)
          (abs_nonneg _) (by norm_num)) (by norm_num)
    _ = _ := by simp only [NNReal.coe_add]; ring

lemma physicalCDFCoordinateCutoffRate_tendsto (v x : ℝ) :
    Tendsto (fun n => physicalCDFCoordinateCutoffRate β α T n v x) atTop
      (𝓝 (physicalCDFCoordinateRate β α T v x)) := by
  simpa only [physicalCDFCoordinateCutoffRate,one_mul,zero_mul,mul_zero,add_zero] using
    ((scalarSmoothCutoff_deriv_tendsto x).mul_const (physicalCDFCoordinateRate β α T v x)).add
      (((scalarSmoothCutoff_second_deriv_tendsto x).mul_const (compactCDFJet β α T 0 (v/β^2) x)).const_mul (1/2:ℝ))

include hβ hT0 hT1 in
lemma physicalCDFCoordinateCutoffRate_expected_tendsto (v : ℝ) :
    Tendsto (fun n => ∫ w, physicalCDFCoordinateCutoffRate β α T n v
      (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal v) w) ∂W.law) atTop
      (𝓝 (∫ w, physicalCDFCoordinateRate β α T v
        (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal v) w) ∂W.law)) := by
  let := W.isProbability
  obtain ⟨C,hC⟩ := physicalCDFCoordinateCutoffRate_uniform_bound β α ha h1 hβ hT0 hT1
  apply tendsto_integral_of_dominated_convergence (fun _ : Ω => (C:ℝ))
    (fun n => (integrable_family_comp (P:=W.law)
      (physicalCDFCoordinateCutoffRate_family β α ha h1 hβ hT0 hT1 n) v
      ((finiteTemperatureCDFDrift β α ha h1).solution_measurable W (Real.toNNReal v))).aestronglyMeasurable)
    (integrable_const _) _ _
  · intro n
    exact Eventually.of_forall (fun w => by simpa only [Real.norm_eq_abs] using hC n v _)
  · exact Eventually.of_forall (fun w => physicalCDFCoordinateCutoffRate_tendsto β α v _)

include hβ hT0 hT1 in
lemma physicalCDFCoordinateCutoff_integral_tendsto (V : ℝ) (hV0 : 0≤V) :
    Tendsto (fun n => ∫ v in 0..V, ∫ w, physicalCDFCoordinateCutoffRate β α T n v
      (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal v) w) ∂W.law) atTop
      (𝓝 (∫ v in 0..V, ∫ w, physicalCDFCoordinateRate β α T v
        (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal v) w) ∂W.law)) := by
  let := W.isProbability
  obtain ⟨C,hC⟩ := physicalCDFCoordinateCutoffRate_uniform_bound β α ha h1 hβ hT0 hT1
  simp only [intervalIntegral.integral_of_le hV0]
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => (C:ℝ))
    (fun n => (bounded_family_expected_stronglyMeasurable W (finiteTemperatureCDFDrift β α ha h1)
      (physicalCDFCoordinateCutoffRate_family β α ha h1 hβ hT0 hT1 n)).aestronglyMeasurable.mono_measure
      Measure.restrict_le_self) (integrable_const _) _ _
  · intro n
    filter_upwards [] with v
    have H := norm_integral_le_of_norm_le_const (μ:=W.law) (C:=(C:ℝ))
      (f:=fun w => physicalCDFCoordinateCutoffRate β α T n v
        (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal v) w))
      (Eventually.of_forall (fun w => by simpa only [Real.norm_eq_abs] using hC n v _))
    simpa only [probReal_univ,mul_one,finiteTemperatureCDFProcess] using H
  · exact Eventually.of_forall (fun v => physicalCDFCoordinateCutoffRate_expected_tendsto W β α ha h1 hβ hT0 hT1 v)

include hβ hT0 hT1 in
theorem physicalCDFCoordinateExpected_integral (V : ℝ) (hV0 : 0≤V) (hVT : V/β^2<T) :
    physicalCDFCoordinateExpected W β α ha h1 T V=
      ∫ v in 0..V, ∫ w, physicalCDFCoordinateRate β α T v
        (finiteTemperatureCDFProcess W β α ha h1 (Real.toNNReal v) w) ∂W.law := by
  have H := physicalCDFCoordinateCutoff_expected_tendsto W β α ha h1 hβ hT0 hT1 V
  simp only [physicalCDFCoordinateCutoff_expectation_integral W β α ha h1 hβ hT0 hT1 _ V hV0 hVT] at H
  exact tendsto_nhds_unique H (physicalCDFCoordinateCutoff_integral_tendsto W β α ha h1 hβ hT0 hT1 V hV0)

end SKConstants.ParisiFullSupport
