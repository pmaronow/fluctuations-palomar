module

public import SKConstants.ParisiCDFWeightedMGF
public import SKConstants.ParisiPostEndpointLaw
public import SKConstants.ScalarProcessRowMGF

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology
set_option maxHeartbeats 1000000

namespace SKConstants
open SKConstantsOAI.ZeroTemperatureSK ParisiFullSupport

def postPathWeighted (q : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ)
    (p : ScalarContinuousPath (q n)) : ℝ :=
  ∑ i ∈ Finset.range n, c i *
    (Real.tanh (p (projIcc 0 (q n : ℝ) (q n).coe_nonneg (q (i+1)))) -
      Real.tanh (p (projIcc 0 (q n : ℝ) (q n).coe_nonneg (q i))))

theorem measurable_postPathWeighted (q : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ) :
    Measurable (postPathWeighted q c n) :=
  Finset.measurable_fun_sum _ fun _i _hi => measurable_const.mul
    ((measurable_scalarTanh.comp (ContinuousMap.measurable_eval _)).sub
      (measurable_scalarTanh.comp (ContinuousMap.measurable_eval _)))

theorem postPathWeighted_abs_le (q : ℕ → ℝ≥0) (c : ℕ → ℝ) (n : ℕ)
    (p : ScalarContinuousPath (q n)) :
    |postPathWeighted q c n p| ≤ 2*∑ i ∈ Finset.range n, |c i| := by
  calc
    _ ≤ ∑ i ∈ Finset.range n, |c i * (Real.tanh
        (p (projIcc 0 (q n : ℝ) (q n).coe_nonneg (q (i+1)))) - Real.tanh
        (p (projIcc 0 (q n : ℝ) (q n).coe_nonneg (q i))))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, 2*|c i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      have hA := abs_le.mp (norm_tanh_le_one
        (p (projIcc 0 (q n : ℝ) (q n).coe_nonneg (q (i+1)))))
      have hB := abs_le.mp (norm_tanh_le_one
        (p (projIcc 0 (q n : ℝ) (q n).coe_nonneg (q i))))
      have hD : |Real.tanh (p (projIcc 0 (q n : ℝ) (q n).coe_nonneg (q (i+1)))) -
          Real.tanh (p (projIcc 0 (q n : ℝ) (q n).coe_nonneg (q i)))| ≤ 2 :=
        abs_le.mpr ⟨by linarith,by linarith⟩
      nlinarith [abs_nonneg (c i),mul_le_mul_of_nonneg_left hD (abs_nonneg (c i))]
    _ = _ := by rw [Finset.mul_sum]

theorem scalarTanhPicard_weighted_mgf {Ω : Type*} [MeasurableSpace Ω]
    (W : BrownianSystem Ω) (z : ℝ) (q : ℕ → ℝ≥0) (hq : Monotone q)
    (c : ℕ → ℝ) (n : ℕ) (θ : ℝ) :
    (∫ w, Real.exp (θ*postPathWeighted q c n
      (scalarForwardPicardPath scalarTanhDrift (q n) (z,brownianFinitePath W (q n) w))) ∂W.law) ≤
        Real.exp ((preCDFWeightedProxy q c n : ℝ)*θ^2/2) := by
  let := W.isProbability
  let F := brownianFinitePath W (q n)
  let J : ScalarContinuousPath (q n) → ScalarContinuousPath (q n) :=
    fun p => scalarForwardPicardPath scalarTanhDrift (q n) (z,p)
  let H : ScalarContinuousPath (q n) → ℝ := fun p => Real.exp (θ*postPathWeighted q c n p)
  have hF : Measurable F := measurable_brownianFinitePath W (q n)
  have hJ : Measurable J := (measurable_scalarForwardPicardPath scalarTanhDrift (q n)).comp
    (measurable_const.prodMk measurable_id)
  have hH : Measurable H := Real.continuous_exp.measurable.comp
    (measurable_const.mul (measurable_postPathWeighted q c n))
  have hl := scalarForwardPicardPath_actual_hidden_field_law_joint_version
    W.law W.B W.brownian (q n) z F hF (brownianFinitePath_version W (q n))
  have he : (∫ w, H (J (F w)) ∂W.law) =
      ∫ u, H (scalarSeedHiddenFieldPath (q n) F (z,u)) ∂scalarHiddenBrownianLaw z W.law := by
    have hl' : W.law.map (J ∘ F) =
        (scalarHiddenBrownianLaw z W.law).map (fun u => scalarSeedHiddenFieldPath (q n) F (z,u)) := by
      rw [←Measure.map_map hJ hF]
      exact hl
    calc
      _ = ∫ p, H p ∂W.law.map (J ∘ F) := by
        simpa only [Function.comp_def] using
          (integral_map (hJ.comp hF).aemeasurable hH.aestronglyMeasurable).symm
      _ = _ := by
        rw [hl']
        have hm : Measurable (fun u : Bool × Ω => scalarSeedHiddenFieldPath (q n) F (z,u)) :=
          (measurable_scalarSeedHiddenFieldPath (q n) F hF).comp
            (measurable_const.prodMk measurable_id)
        exact integral_map hm.aemeasurable hH.aestronglyMeasurable
  have hv : (fun u => postPathWeighted q c n (scalarSeedHiddenFieldPath (q n) F (z,u))) =ᵐ[
      scalarHiddenBrownianLaw z W.law] (fun u => ∑ i ∈ Finset.range n,
        c i * scalarContinuousPosteriorIncrement z W.B (q i) (q (i+1)) u) := by
    have hf := (measurePreserving_snd (μ := scalarHiddenPriorBool z) (ν := W.law)).quasiMeasurePreserving.ae
      (brownianFinitePath_version W (q n))
    filter_upwards [hf] with u hu
    apply Finset.sum_congr rfl
    intro i hi
    have hin := Finset.mem_range.mp hi
    have h0 : (q i : ℝ) ∈ Icc (0:ℝ) (q n : ℝ) := ⟨(q i).coe_nonneg,hq (by omega)⟩
    have h1 : (q (i+1) : ℝ) ∈ Icc (0:ℝ) (q n : ℝ) :=
      ⟨(q (i+1)).coe_nonneg,hq (by omega)⟩
    simp only [projIcc_of_mem (q n).coe_nonneg h0,projIcc_of_mem (q n).coe_nonneg h1,
      scalarContinuousPosteriorIncrement,scalarHiddenContinuousField]
    change c i * (Real.tanh (z+scalarHiddenSign u.1*(q (i+1) : ℝ)+F u.2 ⟨q (i+1),h1⟩) -
      Real.tanh (z+scalarHiddenSign u.1*(q i : ℝ)+F u.2 ⟨q i,h0⟩)) = _
    rw [hu ⟨q (i+1),h1⟩,hu ⟨q i,h0⟩]
    rfl
  have hs := scalarContinuousPosterior_linearForm_hasSubgaussianMGF W.law z W.B W.brownian q hq c n
  have hp : (∑ i ∈ Finset.range n, ‖c i‖₊^2*(q (i+1)-q i)) = preCDFWeightedProxy q c n := by
    apply Finset.sum_congr rfl
    intro i hi
    congr 1
    apply NNReal.coe_injective
    simp only [NNReal.coe_pow,coe_nnnorm,Real.norm_eq_abs,NNReal.coe_mk,sq_abs]
  change (∫ w, H (J (F w)) ∂W.law) ≤ _
  rw [he]
  calc
    _ = mgf (fun u => ∑ i ∈ Finset.range n,
        c i*scalarContinuousPosteriorIncrement z W.B (q i) (q (i+1)) u) (scalarHiddenBrownianLaw z W.law) θ := by
      apply integral_congr_ae
      exact hv.mono (fun u hu => congrArg (fun x => Real.exp (θ*x)) hu)
    _ ≤ _ := by simpa only [hp] using hs.mgf_le θ

end SKConstants
