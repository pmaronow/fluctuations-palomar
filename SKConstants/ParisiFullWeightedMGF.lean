module

public import SKConstants.ParisiPostWeightedMGF

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option maxHeartbeats 1000000

namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport

def actualParisiPostWeighted {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (q : ℕ → ℝ≥0) (d : ℕ → ℝ) (n : ℕ) (w : Ω) : ℝ :=
  ∑ i ∈ Finset.range n, d i *
    (Real.tanh (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β+q (i+1)) w) -
      Real.tanh (actualParisiFullScalarProcess W β (parisiEquilibriumPhysicalEndpoint β+q i) w))

theorem postPathWeighted_actual_version {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (q : ℕ → ℝ≥0) (hq : Monotone q)
    (d : ℕ → ℝ) (n : ℕ) :
    (fun w => postPathWeighted q d n (actualParisiPostEndpointPath W β (q n) w)) =ᵐ[W.law]
      actualParisiPostWeighted W β q d n := by
  filter_upwards [actualParisiPostEndpointPath_version W β (q n)] with w hw
  apply Finset.sum_congr rfl
  intro i hi
  have hin := Finset.mem_range.mp hi
  have h0 : (q i : ℝ) ∈ Icc (0:ℝ) (q n : ℝ) := ⟨(q i).coe_nonneg,hq (by omega)⟩
  have h1 : (q (i+1) : ℝ) ∈ Icc (0:ℝ) (q n : ℝ) :=
    ⟨(q (i+1)).coe_nonneg,hq (by omega)⟩
  simp only [projIcc_of_mem (q n).coe_nonneg h0,projIcc_of_mem (q n).coe_nonneg h1,hw]
  rfl

theorem actualParisi_past_post_mgf {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (F : ScalarContinuousPath (parisiEquilibriumPhysicalEndpoint β) → ℝ)
    (hF : Measurable F) (C : ℝ) (hFC : ∀ p, |F p| ≤ C) (K : ℝ≥0)
    (hpre : HasSubgaussianMGF (fun w => F (actualParisiEndpointPastPath W β w)) K W.law)
    (q : ℕ → ℝ≥0) (hq : Monotone q) (d : ℕ → ℝ) (n : ℕ) (θ : ℝ) :
    (∫ w, Real.exp (θ*(F (actualParisiEndpointPastPath W β w)+
      actualParisiPostWeighted W β q d n w)) ∂W.law) ≤
        Real.exp (((K+preCDFWeightedProxy q d n : ℝ≥0) : ℝ)*θ^2/2) := by
  let := W.isProbability
  let V := parisiEquilibriumPhysicalEndpoint β
  let b := actualParisiFullScalarDrift β
  let H : ScalarContinuousPath V × ScalarContinuousPath (q n) → ℝ := fun p =>
    Real.exp (θ*(F p.1+postPathWeighted q d n p.2))
  have hH : Measurable H := Real.continuous_exp.measurable.comp
    (measurable_const.mul ((hF.comp measurable_fst).add
      ((measurable_postPathWeighted q d n).comp measurable_snd)))
  have hbound (p : ScalarContinuousPath V × ScalarContinuousPath (q n)) :
      |H p| ≤ Real.exp (|θ| * (C+2*∑ i ∈ Finset.range n, |d i|)) := by
    rw [abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc θ*_ ≤ |θ*_| := le_abs_self _
      _ = |θ| * |_| := abs_mul _ _
      _ ≤ |θ| * (|F p.1|+|postPathWeighted q d n p.2|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg θ)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (add_le_add (hFC p.1) (postPathWeighted_abs_le q d n p.2)) (abs_nonneg θ)
  have he := boundedDrift_restart_integral W b V (q n) H hH _ hbound
  have hp := postPathWeighted_actual_version W β q hq d n
  have hactual : (∫ w, Real.exp (θ*(F (actualParisiEndpointPastPath W β w)+
      actualParisiPostWeighted W β q d n w)) ∂W.law) =
      ∫ w, H (boundedDriftPastPath W b V w,boundedDriftRestartPath W b V (q n) w) ∂W.law := by
    apply integral_congr_ae
    exact hp.mono (fun w hw => congrArg (fun x =>
      Real.exp (θ*(F (actualParisiEndpointPastPath W β w)+x))) hw.symm)
  rw [hactual,he]
  let μ := W.law.map (actualParisiEndpointPastPath W β)
  have hpm : Measurable (actualParisiEndpointPastPath W β) :=
    measurable_boundedDriftPastPath W b V
  have hEm : Measurable (fun p : ScalarContinuousPath V => Real.exp (θ*F p)) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul hF)
  have hFi : Integrable (fun p => Real.exp (θ*F p)) μ := by
    change Integrable (fun p => Real.exp (θ*F p)) (W.law.map (actualParisiEndpointPastPath W β))
    rw [integrable_map_measure hEm.aestronglyMeasurable hpm.aemeasurable]
    exact hpre.integrable_exp_mul θ
  calc
    _ ≤ ∫ past, Real.exp (θ*F past)*Real.exp ((preCDFWeightedProxy q d n : ℝ)*θ^2/2) ∂μ := by
      apply integral_mono_of_nonneg
      · exact ae_of_all _ fun past => integral_nonneg (fun w => (Real.exp_pos _).le)
      · exact hFi.mul_const _
      · apply ae_of_all
        intro past
        change (∫ w, H (past,boundedDriftRestartCallback b V (q n)
          (past,brownianFinitePath W (q n) w)) ∂W.law) ≤ _
        have hcallback : (∫ w, H (past,boundedDriftRestartCallback b V (q n)
            (past,brownianFinitePath W (q n) w)) ∂W.law) =
            Real.exp (θ*F past) * ∫ w, Real.exp (θ*postPathWeighted q d n
              (scalarForwardPicardPath scalarTanhDrift (q n)
                (past ⟨V,V.coe_nonneg,le_rfl⟩,brownianFinitePath W (q n) w))) ∂W.law := by
          rw [←integral_const_mul]
          apply integral_congr_ae
          apply ae_of_all
          intro w
          dsimp only [H]
          rw [actualParisiEndpointRestartCallback_eq_tanh β hβ (q n),mul_add,Real.exp_add]
        rw [hcallback]
        exact mul_le_mul_of_nonneg_left
          (scalarTanhPicard_weighted_mgf W (past ⟨V,V.coe_nonneg,le_rfl⟩) q hq d n θ) (by positivity)
    _ ≤ Real.exp (((K+preCDFWeightedProxy q d n : ℝ≥0) : ℝ)*θ^2/2) := by
      rw [integral_mul_const]
      have hmap : (∫ p, Real.exp (θ*F p) ∂μ) =
          ∫ w, Real.exp (θ*F (actualParisiEndpointPastPath W β w)) ∂W.law :=
        integral_map hpm.aemeasurable hEm.aestronglyMeasurable
      rw [hmap]
      calc
        _ ≤ Real.exp ((K : ℝ)*θ^2/2)*Real.exp ((preCDFWeightedProxy q d n : ℝ)*θ^2/2) :=
          mul_le_mul_of_nonneg_right (hpre.mgf_le θ) (by positivity)
        _ = _ := by rw [←Real.exp_add,NNReal.coe_add]; congr 1; ring

end SKConstants
