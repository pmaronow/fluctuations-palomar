module

public import SKConstants.ParisiCDFCoefficientJets
public import SKConstants.Upstream.OAI.Probability.SKBarriers.Parisi.CDFTimeContinuity

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology ContDiff
noncomputable section

namespace SKConstants.ParisiFullSupport

open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.ZeroTemperatureSK.Heat SKConstantsOAI.SK.Analytic

theorem scalarCDFValue_moving_time_uniform (β : ℝ) (α : StieltjesFunction ℝ)
    (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    (αn : ℕ → ℝ → ℝ) (han : ∀ n z, αn n z ∈ Icc (0:ℝ) 1)
    (hmn : ∀ n, Monotone (αn n)) (qn en : ℕ → ℝ) {T q : ℝ}
    (hT1 : T < 1) (hq : q ∈ Icc (0:ℝ) T) (hqn : ∀ n, qn n ∈ Icc (0:ℝ) T)
    (hqL : Tendsto qn atTop (𝓝 q)) (heL : Tendsto en atTop (𝓝 0))
    (hE : ∀ n, (∫ z in qn n..qn n+(Real.toNNReal (1-qn n):ℝ), |αn n z-α z|) ≤ en n) :
    TendstoUniformly (fun n => scalarCDFValue β (αn n) (qn n)
      (Real.toNNReal (1-qn n))) (scalarCDFValue β α q (Real.toNNReal (1-q))) atTop := by
  have hqt : Tendsto qn atTop (𝓝[Icc (0:ℝ) 1] q) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hqL,Eventually.of_forall (fun n => ⟨(hqn n).1,(hqn n).2.trans hT1.le⟩)⟩
  have HT := scalarCDFValue_time_uniform β α ha h1
    (show q ∈ Icc (0:ℝ) 1 from ⟨hq.1,hq.2.trans hT1.le⟩)
  rw [Metric.tendstoUniformly_iff] at HT ⊢
  have HE := heL.const_mul (scalarTimeMassConstant β)
  simp only [mul_zero] at HE
  intro ε hε
  have hε2 : 0 < ε/2 := by positivity
  filter_upwards [HE.eventually (gt_mem_nhds hε2),hqt.eventually (HT (ε/2) hε2)] with n hn ht x
  have hrem : Real.toNNReal (1-qn n) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [(hqn n).1]
  have H := scalarCDFValue_cdf_lipschitz β (han n) (hmn n) ha α.mono (qn n) _ hrem x
  have H' := H.trans (mul_le_mul_of_nonneg_left (hE n) (scalarTimeMassConstant_nonneg β))
  have Ht := ht x
  rw [Real.dist_eq] at Ht ⊢
  have HS := abs_sub_le (scalarCDFValue β α q (Real.toNNReal (1-q)) x)
    (scalarCDFValue β α (qn n) (Real.toNNReal (1-qn n)) x)
    (scalarCDFValue β (αn n) (qn n) (Real.toNNReal (1-qn n)) x)
  rw [abs_sub_comm (scalarCDFValue β α (qn n) (Real.toNNReal (1-qn n)) x)
    (scalarCDFValue β (αn n) (qn n) (Real.toNNReal (1-qn n)) x)] at HS
  linarith

theorem scalarCDFValue_moving_time_jets_uniform {β : ℝ} (hβ : β ≠ 0)
    (α : StieltjesFunction ℝ) (ha : ∀ z, α z ∈ Icc (0:ℝ) 1) (h1 : α 1=1)
    (αn : ℕ → ℝ → ℝ) (han : ∀ n z, αn n z ∈ Icc (0:ℝ) 1)
    (hmn : ∀ n, Monotone (αn n)) (qn en : ℕ → ℝ) {T q : ℝ}
    (hT1 : T < 1) (hq : q ∈ Icc (0:ℝ) T) (hqn : ∀ n, qn n ∈ Icc (0:ℝ) T)
    (hqL : Tendsto qn atTop (𝓝 q)) (heL : Tendsto en atTop (𝓝 0))
    (hE : ∀ n, (∫ z in qn n..qn n+(Real.toNNReal (1-qn n):ℝ), |αn n z-α z|) ≤ en n)
    (m : ℕ) :
    TendstoUniformly (fun n => iteratedDeriv m (scalarCDFValue β (αn n) (qn n)
      (Real.toNNReal (1-qn n))))
      (iteratedDeriv m (scalarCDFValue β α q (Real.toNNReal (1-q)))) atTop := by
  have ht0 (n : ℕ) : 0 < (Real.toNNReal (1-qn n):ℝ) := by
    rw [Real.coe_toNNReal _ (by linarith [(hqn n).2])]
    linarith [(hqn n).2]
  have ht1 (n : ℕ) : Real.toNNReal (1-qn n) ≤ 1 := by
    rw [Real.toNNReal_le_iff_le_coe,NNReal.coe_one]
    linarith [(hqn n).1]
  apply (smooth_limit_of_uniform_derivative_bounds
    (fun n => (scalarCDFValue_contDiff_and_higher_derivative_limit
      (han n) (hmn n) hβ (qn n) _ (ht0 n) (ht1 n)).1)
    ?_ (scalarCDFValue_moving_time_uniform β α ha h1 αn han hmn qn en hT1 hq hqn hqL heL hE)).2 m
  intro k
  obtain ⟨C,hC,hB⟩ := scalarCDFValue_uniform_coefficient_time_derivative_bounds hβ
    (show 0 < 1-T by linarith) k
  refine ⟨C,hC,fun n x => hB (αn n) (han n) (hmn n) (qn n) _ ?_ (ht1 n) x⟩
  rw [Real.coe_toNNReal _ (by linarith [(hqn n).2])]
  linarith [(hqn n).2]

end SKConstants.ParisiFullSupport
