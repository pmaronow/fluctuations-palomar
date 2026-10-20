module

public import SKConstants.ParisiFullMixedRowCovariance
public import SKConstants.ParisiFullPredictableMGF
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Topology BigOperators InnerProductSpace
namespace SKConstants.Completion.LGram
open SKConstantsOAI.ZeroTemperatureSK SKConstantsOAI.SK.Analytic ParisiFullSupport
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω]

def posteriorGridForm (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (k : ℕ) (w : Ω) : ℝ :=
  ∑ i ∈ Finset.range k, c i * actualParisiMagnetizationIncrement W β (t i) (t (i+1)) w

private def gridPastForm (β : ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ)
    (k : ℕ) (p : ScalarContinuousPath (t k)) : ℝ :=
  ∑ i ∈ Finset.range k, c i *
    (actualParisiFullMagnetization β (t (i+1))
      (p (projIcc 0 (t k : ℝ) (t k).coe_nonneg (t (i+1)))) -
     actualParisiFullMagnetization β (t i)
      (p (projIcc 0 (t k : ℝ) (t k).coe_nonneg (t i))))

private lemma gridPastForm_measurable (β : ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (k : ℕ) :
    Measurable (gridPastForm β t c k) := by
  have hm (s : ℝ≥0) : Measurable (actualParisiFullMagnetization β (s : ℝ)) :=
    ((continuous_actualParisiFullMagnetization β).comp
      (continuous_const.prodMk continuous_id)).measurable
  exact Finset.measurable_fun_sum _ fun i _ => measurable_const.mul
    ((hm _ |>.comp (ContinuousMap.measurable_eval _)).sub
      (hm _ |>.comp (ContinuousMap.measurable_eval _)))

private lemma gridPastForm_bound (β : ℝ) (t : ℕ → ℝ≥0) (c : ℕ → ℝ)
    (k : ℕ) (p : ScalarContinuousPath (t k)) :
    |gridPastForm β t c k p| ≤ 2 * ∑ i ∈ Finset.range k, |c i| :=
  abs_weighted_differences _ _ c k
    (fun _ => (actualParisiFullMagnetization_curvature_bounds β _ _).1)
    (fun _ => (actualParisiFullMagnetization_curvature_bounds β _ _).1)

private lemma gridPastForm_version (W : BrownianSystem Ω) (β : ℝ)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (k : ℕ) :
    (fun w => gridPastForm β t c k
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w)) =ᵐ[W.law]
        posteriorGridForm W β t c k := by
  filter_upwards [boundedDriftPastPath_version W (actualParisiFullScalarDrift β) (t k)]
    with w hw
  apply Finset.sum_congr rfl
  intro i hi
  have hik : i < k := Finset.mem_range.mp hi
  have h0 : (t i : ℝ) ∈ Icc (0:ℝ) (t k : ℝ) :=
    ⟨(t i).coe_nonneg, ht (by omega)⟩
  have h1 : (t (i+1) : ℝ) ∈ Icc (0:ℝ) (t k : ℝ) :=
    ⟨(t (i+1)).coe_nonneg, ht (by omega)⟩
  simp only [projIcc_of_mem (t k).coe_nonneg h0,
    projIcc_of_mem (t k).coe_nonneg h1, hw,
    actualParisiMagnetizationIncrement, actualParisiMagnetizationObservable]
  rfl

theorem posteriorGridForm_mgf (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (k : ℕ) (θ : ℝ) :
    (∫ w, Real.exp (θ * posteriorGridForm W β t c k w) ∂W.law) ≤
      Real.exp ((preCDFWeightedProxy t c k : ℝ) * θ^2 / 2) := by
  let := W.isProbability
  induction k with
  | zero => simp [posteriorGridForm, preCDFWeightedProxy]
  | succ k ih =>
    let F : ScalarContinuousPath (t k) → ℝ := fun p =>
      Real.exp (θ * gridPastForm β t c k p)
    have hF : Measurable F :=
      Real.continuous_exp.measurable.comp ((gridPastForm_measurable β t c k).const_mul θ)
    have hFB (p : ScalarContinuousPath (t k)) :
        F p ≤ Real.exp (|θ| * (2 * ∑ i ∈ Finset.range k, |c i|)) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ |θ * gridPastForm β t c k p| := le_abs_self _
        _ = |θ| * |gridPastForm β t c k p| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (gridPastForm_bound β t c k p) (abs_nonneg θ)
    have H := actualParisiFullProcess_predictable_mgf_test W β hβ
      (t k) (t (k+1)-t k) F (fun _ => c k) hF measurable_const
      (fun _ => (Real.exp_pos _).le)
      (Real.exp (|θ| * (2 * ∑ i ∈ Finset.range k, |c i|))) |c k|
      (Real.exp_pos _).le (abs_nonneg _) hFB (fun _ => le_rfl) θ
    simp only [← NNReal.coe_add,
      add_tsub_cancel_of_le (ht (Nat.le_succ k))] at H
    have H' :
        (∫ w, Real.exp (θ * posteriorGridForm W β t c (k+1) w) ∂W.law) ≤
        (∫ w, Real.exp (θ * posteriorGridForm W β t c k w) ∂W.law) *
          Real.exp (θ^2 * (c k)^2 * ((t (k+1)-t k : ℝ≥0):ℝ) / 2) := by
      calc
        _ = ∫ w, F (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w) *
            Real.exp (θ * c k * (actualParisiFullMagnetization β (t (k+1))
              (actualParisiFullScalarProcess W β (t (k+1)) w) -
              actualParisiFullMagnetization β (t k)
                (actualParisiFullScalarProcess W β (t k) w))) ∂W.law := by
          apply integral_congr_ae
          filter_upwards [gridPastForm_version W β t ht c k] with w hw
          dsimp only [F]
          rw [hw, posteriorGridForm, Finset.sum_range_succ]
          rw [← Real.exp_add]
          congr 1
          dsimp only [posteriorGridForm, actualParisiMagnetizationIncrement,
            actualParisiMagnetizationObservable]
          ring
        _ ≤ _ := H
        _ = _ := by
          rw [integral_mul_const]
          congr 1
          apply integral_congr_ae
          filter_upwards [gridPastForm_version W β t ht c k] with w hw
          simp only [F, hw]
    calc
      _ ≤ _ := H'
      _ ≤ Real.exp ((preCDFWeightedProxy t c k : ℝ) * θ^2 / 2) *
          Real.exp (θ^2 * (c k)^2 * ((t (k+1)-t k : ℝ≥0):ℝ) / 2) :=
        mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        simp only [preCDFWeightedProxy, Finset.sum_range_succ, NNReal.coe_add,
          NNReal.coe_mul, NNReal.coe_mk]
        ring

theorem posteriorGridForm_hasSubgaussianMGF (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (k : ℕ) :
    HasSubgaussianMGF (posteriorGridForm W β t c k) (preCDFWeightedProxy t c k) W.law := by
  let := W.isProbability
  have hm : Measurable (posteriorGridForm W β t c k) :=
    Finset.measurable_fun_sum _ fun i _ =>
      (measurable_actualParisiMagnetizationIncrement W β _ _).const_mul _
  have hB (w : Ω) : |posteriorGridForm W β t c k w| ≤
      2 * ∑ i ∈ Finset.range k, |c i| :=
    abs_weighted_differences _ _ c k
      (fun _ => actualParisiMagnetizationObservable_abs_le W β _ w)
      (fun _ => actualParisiMagnetizationObservable_abs_le W β _ w)
  exact ⟨fun θ => integrable_exp_mul_of_mem_Icc hm.aemeasurable
    (ae_of_all _ fun w => abs_le.mp (hB w)),
    fun θ => posteriorGridForm_mgf W β hβ t ht c k θ⟩

theorem normalizedPosteriorRow_hasSubgaussianMGF
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (d : ℕ) (a : EuclideanSpace ℝ (Fin d)) :
    HasSubgaussianMGF (fun w => ⟪actualParisiNormalizedPosteriorRow W β t d w,a⟫_ℝ)
      (actualParisiPosteriorRowMGFProxy W β (t d)*‖a‖₊^2) W.law := by
  let u := t
  let K := actualParisiPosteriorRowMGFProxy W β (t d)
  let s : Fin d → ℝ≥0 := fun i => actualParisiPosteriorIntervalScale W β (u i) (u (i+1))
  let c : ℕ → ℝ := fun k => if hk : k<d then a ⟨k,hk⟩/(s ⟨k,hk⟩:ℝ) else 0
  have hu : StrictMono u := ht
  have hend : u d=t d :=
    rfl
  have hs (i : Fin d) : 0 < s i := actualParisiPosteriorIntervalScale_pos W β hβ _ _
    (hu (Nat.lt_succ_self _))
  have hb (i : Fin d) : u (i+1)-u i ≤ K*(s i)^2 := by
    apply actualParisiPosteriorIntervalScale_duration_budget W β hβ _ _ _ (hu (Nat.lt_succ_self _))
    rw [←hend]
    exact hu.monotone (by omega)
  have he (w : Ω) : ⟪actualParisiNormalizedPosteriorRow W β u d w,a⟫_ℝ=
      ∑ i ∈ Finset.range d,c i*actualParisiMagnetizationIncrement W β (u i) (u (i+1)) w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct,Pi.star_apply,star_trivial,actualParisiNormalizedPosteriorRow,WithLp.ofLp_toLp]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [c,Finset.mem_range.mp hk,dite_true]
    ring
  have hp : (∑ i ∈ Finset.range d,‖c i‖₊^2*(u (i+1)-u i)) ≤ K*‖a‖₊^2 := by
    apply NNReal.coe_le_coe.mp
    simp only [NNReal.coe_sum,NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm,EuclideanSpace.real_norm_sq_eq]
    rw [Finset.mul_sum,Finset.sum_fin_eq_sum_range]
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    let i : Fin d := ⟨k,hk'⟩
    have hsi : (s i:ℝ)≠0 := (NNReal.coe_pos.mpr (hs i)).ne'
    have HI := NNReal.coe_le_coe.mpr (hb i)
    simp only [NNReal.coe_mul,NNReal.coe_pow] at HI
    simp only [c,hk',dite_true,Real.norm_eq_abs,sq_abs]
    change (a i/(s i:ℝ))^2*((u (i+1)-u i:ℝ≥0):ℝ) ≤ (K:ℝ)*(a i)^2
    calc
      _ ≤ (a i/(s i:ℝ))^2*((K:ℝ)*(s i:ℝ)^2) :=
        mul_le_mul_of_nonneg_left HI (sq_nonneg _)
      _ = _ := by field_simp
  have H := posteriorGridForm_hasSubgaussianMGF W β hβ t ht.monotone c d
  have hproxy : preCDFWeightedProxy t c d ≤ K*‖a‖₊^2 := by
    apply NNReal.coe_le_coe.mp
    simpa only [preCDFWeightedProxy, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_mk,
      NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs, u] using
      (NNReal.coe_le_coe.mpr hp)
  have H' := Concentration.hasSubgaussianMGF_of_proxy_le H hproxy
  exact H'.congr (ae_of_all _ (fun w => (he w).symm))

theorem normalizedPosteriorRow_unit_hasSubgaussianMGF
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (d : ℕ)
    (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1) :
    HasSubgaussianMGF (fun w => ⟪actualParisiNormalizedPosteriorRow W β t d w,a⟫_ℝ)
      (actualParisiPosteriorRowMGFProxy W β (t d)) W.law := by
  apply Concentration.hasSubgaussianMGF_of_proxy_le
    (normalizedPosteriorRow_hasSubgaussianMGF W β hβ t ht d a)
  apply mul_le_of_le_one_right (by positivity)
  exact pow_le_one₀ (by positivity) (show ‖a‖₊ ≤ 1 from ha)

end SKConstants.Completion.LGram
