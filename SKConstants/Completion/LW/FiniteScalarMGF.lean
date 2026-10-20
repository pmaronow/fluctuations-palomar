module

public import SKConstants.Completion.LW.ScalarEstimates
public import SKConstants.ParisiFullPredictableExponential

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal InnerProductSpace

namespace SKConstants.Completion.LW
open SKConstantsOAI.ZeroTemperatureSK
variable {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]

def weightedIncrement (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0)
    (c : ℕ → ℝ) (k : ℕ) (w : Ω) : ℝ :=
  ∑ j ∈ Finset.range k, c j * actualParisiMagnetizationIncrement W β (t j) (t (j+1)) w

def weightedDurationProxy (t : ℕ → ℝ≥0) (c : ℕ → ℝ) (k : ℕ) : ℝ≥0 :=
  ∑ j ∈ Finset.range k, ‖c j‖₊^2 * (t (j+1)-t j)

theorem weightedDurationProxy_coe (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (k : ℕ) :
    (weightedDurationProxy t c k : ℝ) = ∑ j ∈ Finset.range k, c j^2 * previousDuration t j := by
  simp only [weightedDurationProxy, NNReal.coe_sum, NNReal.coe_mul, NNReal.coe_pow,
    coe_nnnorm, Real.norm_eq_abs, sq_abs, NNReal.coe_sub (ht (Nat.le_succ _)), previousDuration]

theorem constantPredictableExponential_version
    (W : BrownianSystem Ω) (β : ℝ) (t : ℕ → ℝ≥0) (ht : Monotone t)
    (c : ℕ → ℝ) (θ : ℝ) (k : ℕ) :
    (fun w => actualParisiPredictableExponential β t ht (fun j _ => c j) θ k
      (boundedDriftPastPath W (actualParisiFullScalarDrift β) (t k) w)) =ᵐ[W.law]
      (fun w => Real.exp (θ * weightedIncrement W β t c k w -
        θ^2 * (weightedDurationProxy t c k : ℝ)/2)) := by
  induction k with
  | zero => simp [actualParisiPredictableExponential, weightedIncrement, weightedDurationProxy]
  | succ k ih =>
    filter_upwards [ih, boundedDriftPastPath_restrict W (actualParisiFullScalarDrift β)
      (t k) (t (k+1)) (ht (Nat.le_succ _)),
      actualParisiPastMagnetization_version W β (t k),
      actualParisiPastMagnetization_version W β (t (k+1))] with w hi hr h0 h1
    dsimp only [actualParisiPredictableExponential]
    rw [hr, hi, h0, h1, ← Real.exp_add]
    congr 1
    simp only [weightedIncrement, weightedDurationProxy, Finset.sum_range_succ,
      NNReal.coe_add, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm,
      Real.norm_eq_abs, sq_abs, NNReal.coe_sub (ht (Nat.le_succ _)),
      actualParisiMagnetizationIncrement, actualParisiMagnetizationObservable]
    ring

theorem weightedIncrement_hasSubgaussianMGF
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (k : ℕ) :
    HasSubgaussianMGF (weightedIncrement W β t c k) (weightedDurationProxy t c k) W.law := by
  letI := W.isProbability
  have hm : Measurable (weightedIncrement W β t c k) := by
    apply Finset.measurable_fun_sum
    intro j _
    exact measurable_const.mul (measurable_actualParisiMagnetizationIncrement W β _ _)
  have hb (w : Ω) : |weightedIncrement W β t c k w| ≤ 2 * ∑ j ∈ Finset.range k, |c j| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul]
    nlinarith only [actualParisiMagnetizationIncrement_abs_le W β (t j) (t (j+1)) w,
      mul_le_mul_of_nonneg_left
        (actualParisiMagnetizationIncrement_abs_le W β (t j) (t (j+1)) w) (abs_nonneg (c j))]
  constructor
  · intro θ
    exact integrable_exp_mul_of_mem_Icc hm.aemeasurable (ae_of_all _ (fun w => abs_le.mp (hb w)))
  · intro θ
    have H := actualParisiPredictableExponential_integral_le_one W β hβ t ht
      (fun j _ => c j) (fun _ => measurable_const) (fun j => |c j|)
      (fun j => abs_nonneg _) (fun _ _ => le_rfl) θ k
    rw [integral_congr_ae (constantPredictableExponential_version W β t ht c θ k)] at H
    calc
      mgf (weightedIncrement W β t c k) W.law θ =
          ∫ w, Real.exp ((weightedDurationProxy t c k : ℝ)*θ^2/2) *
            Real.exp (θ*weightedIncrement W β t c k w -
              θ^2*(weightedDurationProxy t c k : ℝ)/2) ∂W.law := by
        apply integral_congr_ae
        exact ae_of_all _ (fun w => by dsimp only; rw [← Real.exp_add]; congr 1; ring)
      _ = Real.exp ((weightedDurationProxy t c k : ℝ)*θ^2/2) *
          ∫ w, Real.exp (θ*weightedIncrement W β t c k w -
            θ^2*(weightedDurationProxy t c k : ℝ)/2) ∂W.law := integral_const_mul _ _
      _ ≤ Real.exp ((weightedDurationProxy t c k : ℝ)*θ^2/2) * 1 :=
        mul_le_mul_of_nonneg_left H (Real.exp_pos _).le
      _ = _ := mul_one _

theorem weightedIncrement_supported_hasSubgaussianMGF
    (W : BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : Monotone t) (c : ℕ → ℝ) (k : ℕ)
    (I : Finset ℕ) (hI : I ⊆ Finset.range k) {B : ℝ}
    (hc : ∀ j ∈ I, |c j| ≤ B) (hzero : ∀ j ∈ Finset.range k, j ∉ I → c j = 0) :
    HasSubgaussianMGF (weightedIncrement W β t c k)
      (Real.toNNReal (B^2 * ∑ j ∈ I, previousDuration t j)) W.law := by
  have hd (j : ℕ) : 0 ≤ previousDuration t j :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr (ht (Nat.le_succ _)))
  apply Concentration.hasSubgaussianMGF_of_proxy_le
    (weightedIncrement_hasSubgaussianMGF W β hβ t ht c k)
  apply NNReal.coe_le_coe.mp
  rw [weightedDurationProxy_coe t ht, Real.coe_toNNReal _
    (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => hd j))), Finset.mul_sum]
  calc
    _ = ∑ j ∈ I, c j^2 * previousDuration t j := by
      symm
      exact Finset.sum_subset hI (fun j hj hjI => by rw [hzero j hj hjI]; simp)
    _ ≤ _ := Finset.sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_right
        (by simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hc j hj) 2) (hd j))

theorem posteriorRow_unit_hasSubgaussianMGF
    (W : BrownianSystem Ω) (Z : BrownianSystem A) (β : ℝ) (hβ : 1 < β)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) (k : ℕ) (V : ℝ≥0) (hV : t k ≤ V)
    (α : EuclideanSpace ℝ (Fin k)) (hα : ‖α‖ ≤ 1) :
    HasSubgaussianMGF (fun u => ⟪posteriorRow W β t k u,α⟫_ℝ)
      (actualParisiPosteriorRowMGFProxy W β V) (linkedScalarLaw W Z β V) := by
  let s (j : Fin k) : ℝ := posteriorWeight W β t k j
  let c (j : ℕ) : ℝ := if hj : j < k then α ⟨j,hj⟩ / s ⟨j,hj⟩ else 0
  have he (w : Ω) : ⟪actualParisiNormalizedPosteriorRow W β t k w,α⟫_ℝ =
      weightedIncrement W β t c k w := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Pi.star_apply, star_trivial, actualParisiNormalizedPosteriorRow,
      WithLp.ofLp_toLp, weightedIncrement, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [c, Finset.mem_range.mp hj, dite_true, s, posteriorWeight]
    ring
  have hp : weightedDurationProxy t c k ≤ actualParisiPosteriorRowMGFProxy W β V := by
    apply NNReal.coe_le_coe.mp
    rw [weightedDurationProxy_coe t ht.monotone]
    have hn : ∑ j ∈ Finset.range k, c j^2*previousDuration t j ≤
        (actualParisiPosteriorRowMGFProxy W β V : ℝ) * ‖α‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_fin_eq_sum_range]
      apply Finset.sum_le_sum
      intro j hj
      have hj' := Finset.mem_range.mp hj
      let i : Fin k := ⟨j,hj'⟩
      have hs : s i ≠ 0 := (NNReal.coe_pos.mpr
        (actualParisiPosteriorIntervalScale_pos W β hβ (t j) (t (j+1)) (ht (Nat.lt_succ_self _)))).ne'
      have H := actualParisiPosteriorIntervalScale_duration_budget W β hβ
        (t j) (t (j+1)) V (ht (Nat.lt_succ_self _)) ((ht.monotone (by omega)).trans hV)
      have HR := NNReal.coe_le_coe.mpr H
      rw [NNReal.coe_sub (ht.monotone (Nat.le_succ _)), NNReal.coe_mul, NNReal.coe_pow] at HR
      simp only [c, hj', dite_true]
      change (α i / s i)^2*previousDuration t j ≤ (actualParisiPosteriorRowMGFProxy W β V : ℝ)*(α i)^2
      calc
        _ ≤ (α i / s i)^2*((actualParisiPosteriorRowMGFProxy W β V : ℝ)*s i^2) :=
          mul_le_mul_of_nonneg_left HR (sq_nonneg _)
        _ = _ := by field_simp
    exact hn.trans (mul_le_of_le_one_right (NNReal.coe_nonneg _) (by nlinarith [norm_nonneg α]))
  have H := Concentration.hasSubgaussianMGF_of_proxy_le
    (weightedIncrement_hasSubgaussianMGF W β hβ t ht.monotone c k) hp
  have H' : HasSubgaussianMGF (fun w => ⟪actualParisiNormalizedPosteriorRow W β t k w,α⟫_ℝ)
      (actualParisiPosteriorRowMGFProxy W β V) W.law := H.congr (ae_of_all _ (fun w => (he w).symm))
  apply HasSubgaussianMGF.of_map
    (X := fun w => ⟪actualParisiNormalizedPosteriorRow W β t k w,α⟫_ℝ)
    (actualParisiFullQuerySpinLaw_path_hasLaw W Z β V).aemeasurable
  rw [(actualParisiFullQuerySpinLaw_path_hasLaw W Z β V).map_eq]
  exact H'

end SKConstants.Completion.LW
