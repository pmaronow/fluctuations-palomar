module
public import SKConstants.ScalarProcessRowMGFVariance

public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology InnerProductSpace
set_option backward.isDefEq.respectTransparency false
namespace SKConstants

lemma scalarContinuousPosterior_linearForm_secondMoment {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (t : ℕ → ℝ≥0)
    (ht : Monotone t) (ht0 : 0 < t 0) (a : ℕ → ℝ) (d : ℕ) :
    (∫ u, (∑ i ∈ Finset.range d,
      a i * scalarContinuousPosteriorIncrement z B (t i) (t (i+1)) u)^2
      ∂scalarHiddenBrownianLaw z P) =
      ∑ i ∈ Finset.range d, a i ^ 2 * (scalarP z (t i) - scalarP z (t (i+1))) := by
  let m : ℕ → ℕ → ℕ := fun n i => ⌊((n : ℝ) + 1) * (t i : ℝ)⌋₊
  have hm (n : ℕ) : Monotone (m n) := by
    intro i j hij
    apply Nat.floor_le_floor
    exact mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr (ht hij)) (by positivity)
  let X : ℕ → Bool × Ω → ℝ := fun n u => ∑ i ∈ Finset.range d, a i *
    (scalarWeightedBrownianMeshSum scalarDefect z B n (m n (i+1)) u -
      scalarWeightedBrownianMeshSum scalarDefect z B n (m n i) u)
  let Y : Bool × Ω → ℝ := fun u => ∑ i ∈ Finset.range d,
    a i * scalarContinuousPosteriorIncrement z B (t i) (t (i+1)) u
  have hX (n : ℕ) : MemLp (X n) 2 (scalarHiddenBrownianLaw z P) :=
    (scalarRowPosteriorMesh_hasSubgaussianMGF P z B hB n (m n) (hm n) a d).memLp 2
  have hY : MemLp Y 2 (scalarHiddenBrownianLaw z P) :=
    (scalarContinuousPosterior_linearForm_hasSubgaussianMGF P z B hB t ht a d).memLp 2
  have hlim := integral_sq_tendsto_of_meanSquare hX hY
    (scalarContinuousPosterior_linearForm_tendsto_L2 P z B hB t a d)
  have hP (i : ℕ) :
      (∫ s in Icc 0 (t i : ℝ), scalarHiddenExpectedDefectSqReal P z B s) =
        scalarDefect z - scalarP z (t i) := by
    have h := scalarP_actual_variance_balance P z B hB (t i)
      (ht0.trans_le (ht (Nat.zero_le i))).ne'
    linarith
  have henergy : Tendsto (fun n => ∫ u, X n u ^ 2 ∂scalarHiddenBrownianLaw z P)
      atTop (𝓝 (∑ i ∈ Finset.range d, a i ^ 2 * (scalarP z (t i) - scalarP z (t (i+1))))) := by
    have he (n : ℕ) := scalarRowPosteriorMesh_secondMoment_eq P z B hB n (m n) (hm n) a d
    change ∀ n : ℕ, (∫ u, X n u ^ 2 ∂scalarHiddenBrownianLaw z P) = _ at he
    simp_rw [he]
    apply tendsto_finsetSum
    intro i hi
    have h := ((scalarWeightedBrownianMeshSum_defect_secondMoment_tendsto P z B hB (t (i+1))).sub
      (scalarWeightedBrownianMeshSum_defect_secondMoment_tendsto P z B hB (t i))).const_mul (a i ^ 2)
    simpa only [hP, sub_sub_sub_cancel_left] using h
  exact tendsto_nhds_unique hlim henergy

lemma scalarActualNormalizedPosteriorRow_secondMoment {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) {d : ℕ} (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0 : ℝ)) (htV : t d ≤ V) (a : EuclideanSpace ℝ (Fin d)) :
    (∫ u, ⟪scalarNormalizedPosteriorRow z B t
        (fun i : Fin d => scalarPosteriorIntervalScale z (t i) (t (i+1))) u, a⟫_ℝ ^ 2
      ∂scalarHiddenBrownianLaw z P) = ‖a‖ ^ 2 := by
  let s : Fin d → ℝ≥0 := fun i => scalarPosteriorIntervalScale z (t i) (t (i+1))
  let b : ℕ → ℝ := fun k => if hk : k < d then a ⟨k,hk⟩ / (s ⟨k,hk⟩ : ℝ) else 0
  have hs (i : Fin d) : 0 < s i := scalarPosteriorIntervalScale_pos P z B hB R hR hz
    (t i) (t (i+1)) V
    (ht1.trans (NNReal.coe_le_coe.mpr (ht.monotone (Nat.zero_le _))))
    (ht (Nat.lt_succ_self _)) ((ht.monotone (by omega)).trans htV)
  have hs2 (i : Fin d) : (s i : ℝ)^2 = scalarP z (t i) - scalarP z (t (i+1)) := by
    have hi := hs i
    dsimp [s, scalarPosteriorIntervalScale] at hi ⊢
    have hd : 0 < scalarP z (t i) - scalarP z (t (i+1)) := by
      simpa only [NNReal.sqrt_pos, Real.toNNReal_pos] using hi
    rw [← NNReal.coe_pow, NNReal.sq_sqrt, Real.coe_toNNReal _ hd.le]
  have he (u : Bool × Ω) :
      ⟪scalarNormalizedPosteriorRow z B t s u, a⟫_ℝ =
      ∑ i ∈ Finset.range d, b i * scalarContinuousPosteriorIncrement z B (t i) (t (i+1)) u := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Pi.star_apply, star_trivial, scalarNormalizedPosteriorRow,
      WithLp.ofLp_toLp]
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [b, Finset.mem_range.mp hk, dite_true]
    ring
  calc
    _ = ∫ u, (∑ i ∈ Finset.range d,
        b i * scalarContinuousPosteriorIncrement z B (t i) (t (i+1)) u)^2
        ∂scalarHiddenBrownianLaw z P := by
      apply integral_congr_ae
      exact ae_of_all _ (fun u => congrArg (fun x : ℝ => x^2) (he u))
    _ = ∑ i ∈ Finset.range d, b i ^ 2 * (scalarP z (t i) - scalarP z (t (i+1))) :=
      scalarContinuousPosterior_linearForm_secondMoment P z B hB t ht.monotone
        (NNReal.coe_pos.mp (by linarith)) b d
    _ = ∑ i : Fin d, (a i)^2 := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k hk
      have hk' := Finset.mem_range.mp hk
      let i : Fin d := ⟨k,hk'⟩
      have hi : (s i : ℝ) ≠ 0 := (NNReal.coe_pos.mpr (hs i)).ne'
      simp only [b, hk', dite_true]
      change (a i / (s i : ℝ))^2 * (scalarP z (t i) - scalarP z (t (i+1))) = (a i)^2
      rw [← hs2 i]
      field_simp
    _ = _ := (EuclideanSpace.real_norm_sq_eq a).symm

lemma scalarActualNormalizedPosteriorRow_unit_secondMoment_le_one {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (z : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P) (R : ℝ) (hR : 0 ≤ R) (hz : |z| ≤ R)
    (t : ℕ → ℝ≥0) (ht : StrictMono t) {d : ℕ} (V : ℝ≥0)
    (ht1 : 1 ≤ (t 0 : ℝ)) (htV : t d ≤ V) (a : EuclideanSpace ℝ (Fin d)) (ha : ‖a‖ ≤ 1) :
    (∫ u, ⟪scalarNormalizedPosteriorRow z B t
        (fun i : Fin d => scalarPosteriorIntervalScale z (t i) (t (i+1))) u, a⟫_ℝ ^ 2
      ∂scalarHiddenBrownianLaw z P) ≤ 1 := by
  rw [scalarActualNormalizedPosteriorRow_secondMoment P z B hB R hR hz t ht V ht1 htV a]
  nlinarith [norm_nonneg a]

end SKConstants
