module
public import SKConstants.ScalarProcessLagWeights
public import SKConstants.ScalarProcessLagGrouping

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

lemma measurable_scalarDeterministicLagInnovationSum_joint (dt : ℕ → ℝ≥0) (ρ : ℕ → ℝ) (n : ℕ) :
    Measurable (fun p : ℝ × ScalarObservationHistory n => scalarDeterministicLagInnovationSum p.1 dt ρ n p.2) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    let f : ℝ × ScalarObservationHistory (n+1) → ℝ × ScalarObservationHistory n :=
      fun p => (p.1,p.2.1)
    have hf : Measurable f := measurable_fst.prodMk (measurable_fst.comp measurable_snd)
    have hlast := (measurable_scalarLastField_joint n).comp hf
    have htanh : Measurable (fun p : ℝ × ScalarObservationHistory (n+1) =>
        Real.tanh (scalarLastField p.1 n p.2.1)) :=
      scalar_tanh_lipschitz.continuous.measurable.comp hlast
    have hcoef := htanh.sub (scalar_tanh_lipschitz.continuous.measurable.comp measurable_fst)
    have hinc := ((measurable_snd.comp measurable_snd).sub hlast).sub (htanh.const_mul (dt n : ℝ))
    exact (ih.comp hf).add ((hcoef.const_mul (ρ n)).mul hinc)

def scalarFineWeightedLagBlockSum (z : ℝ) (dt : ℕ → ℝ≥0) (N : ℕ) (ρ : ℕ → ℕ → ℝ) (w : ℕ → ℝ) :
    (k : ℕ) → ScalarLagBlockHistory N k → ℝ :=
  Nat.rec (fun _ => 0) (fun k prev p => prev p.1 + w k *
    scalarDeterministicLagInnovationSum (scalarLagBlockLastField z N k p.1) dt (ρ k) N p.2)

lemma measurable_scalarFineWeightedLagBlockSum (z : ℝ) (dt : ℕ → ℝ≥0) (N : ℕ) (ρ : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (k : ℕ) :
    Measurable (scalarFineWeightedLagBlockSum z dt N ρ w k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact (ih.comp measurable_fst).add
      (((measurable_scalarDeterministicLagInnovationSum_joint dt (ρ k) N).comp
        (((measurable_scalarLagBlockLastField z N k).comp measurable_fst).prodMk measurable_snd)).const_mul (w k))

lemma scalarFineWeightedLagBlockSum_exp_succ (z : ℝ) (dt : ℕ → ℝ≥0) (N : ℕ) (ρ : ℕ → ℕ → ℝ)
    (w : ℕ → ℝ) (k : ℕ) (p : ScalarLagBlockHistory N k) (q : ScalarObservationHistory N) (θ : ℝ) :
    Real.exp (θ * scalarFineWeightedLagBlockSum z dt N ρ w (k+1) (p,q)) =
      Real.exp (θ * scalarFineWeightedLagBlockSum z dt N ρ w k p) *
        Real.exp ((θ*w k) * scalarDeterministicLagInnovationSum (scalarLagBlockLastField z N k p) dt (ρ k) N q) := by
  change Real.exp (θ*(_ + _)) = _
  rw [mul_add, Real.exp_add, mul_assoc]
  rfl

lemma scalarFineWeightedLagBlockSum_mgf_bound (z : ℝ) (dt : ℕ → ℝ≥0) (N : ℕ) (ρ : ℕ → ℕ → ℝ) (hρ : ∀ j k, |ρ j k| ≤ 1)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hdt : ∀ j < N, (dt j : ℝ) ≤ 1)
    (hduration : (∑ j ∈ Finset.range N, (dt j : ℝ)) ≤ h)
    (w : ℕ → ℝ) (A : ℝ) (hA : 0 < A) (θ : ℝ) (hθ : |θ| ≤ 1/(32*h*A))
    (k : ℕ) (hw : ∀ j < k, |w j| ≤ A) :
    Integrable (fun p => Real.exp (θ * scalarFineWeightedLagBlockSum z dt N ρ w k p))
      (scalarLagBlockHistoryLaw z dt N k) ∧
    mgf (scalarFineWeightedLagBlockSum z dt N ρ w k) (scalarLagBlockHistoryLaw z dt N k) θ ≤
      Real.exp ((2048*Real.exp 1*h^2) * θ^2 * ∑ j ∈ Finset.range k, (w j)^2) := by
  induction k with
  | zero =>
    constructor
    · simpa only [scalarFineWeightedLagBlockSum, Nat.rec_zero, mul_zero, Real.exp_zero] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : ScalarLagBlockHistory N 0 => (1 : ℝ))
          (scalarLagBlockHistoryLaw z dt N 0))
    · simp [mgf, scalarFineWeightedLagBlockSum, scalarLagBlockHistoryLaw]
  | succ k ih =>
    have hp := ih (fun j hj => hw j (by omega))
    have hparameter : |θ*w k| ≤ 1/(32*h) := by
      rw [abs_mul]
      calc
        _ ≤ (1/(32*h*A))*A := mul_le_mul hθ (hw k (by omega)) (abs_nonneg _) (by positivity)
        _ = _ := by field_simp
    have hfiber (p : ScalarLagBlockHistory N k) :
        Integrable (fun q => Real.exp (θ * scalarFineWeightedLagBlockSum z dt N ρ w (k+1) (p,q)))
          (scalarLagBlockStepKernel z dt N k p) := by
      rw [scalarLagBlockStepKernel_apply]
      simp only [scalarFineWeightedLagBlockSum_exp_succ]
      exact ((scalarDeterministicLagInnovationSum_local_mgf (scalarLagBlockLastField z N k p) dt (ρ k) (hρ k)
        h hh hh1 N hdt hduration).integrable_exp_mul (θ*w k) hparameter).const_mul _
    have hfiber_bound (p : ScalarLagBlockHistory N k) :
        (∫ q, Real.exp (θ * scalarFineWeightedLagBlockSum z dt N ρ w (k+1) (p,q))
          ∂scalarLagBlockStepKernel z dt N k p) ≤
        Real.exp (θ * scalarFineWeightedLagBlockSum z dt N ρ w k p) *
          Real.exp ((2048*Real.exp 1*h^2)*(θ*w k)^2) := by
      rw [scalarLagBlockStepKernel_apply]
      simp only [scalarFineWeightedLagBlockSum_exp_succ]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left ((scalarDeterministicLagInnovationSum_local_mgf
        (scalarLagBlockLastField z N k p) dt (ρ k) (hρ k) h hh hh1 N hdt hduration).mgf_le
        (θ*w k) hparameter) (Real.exp_pos _).le
    have hmeas : Measurable (fun p : ScalarLagBlockHistory N (k+1) =>
        Real.exp (θ * scalarFineWeightedLagBlockSum z dt N ρ w (k+1) p)) :=
      ((measurable_scalarFineWeightedLagBlockSum z dt N ρ w (k+1)).const_mul θ).exp
    have hInt : Integrable (fun p => Real.exp (θ * scalarFineWeightedLagBlockSum z dt N ρ w (k+1) p))
        (scalarLagBlockHistoryLaw z dt N (k+1)) := by
      change Integrable _ (scalarLagBlockHistoryLaw z dt N k ⊗ₘ scalarLagBlockStepKernel z dt N k)
      apply (Measure.integrable_compProd_iff hmeas.aestronglyMeasurable).2
      constructor
      · exact ae_of_all _ hfiber
      · have hm : StronglyMeasurable (fun p : ScalarLagBlockHistory N k =>
            ∫ q, ‖Real.exp (θ * scalarFineWeightedLagBlockSum z dt N ρ w (k+1) (p,q))‖
              ∂scalarLagBlockStepKernel z dt N k p) :=
          hmeas.norm.stronglyMeasurable.integral_kernel_prod_right'
        apply (hp.1.mul_const (Real.exp ((2048*Real.exp 1*h^2)*(θ*w k)^2))).mono' hm.aestronglyMeasurable
        apply ae_of_all
        intro p
        simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [abs_of_nonneg (integral_nonneg (fun q => (Real.exp_pos _).le))]
        exact hfiber_bound p
    constructor
    · exact hInt
    · change (∫ p, Real.exp (θ * scalarFineWeightedLagBlockSum z dt N ρ w (k+1) p)
        ∂scalarLagBlockHistoryLaw z dt N k ⊗ₘ scalarLagBlockStepKernel z dt N k) ≤ _
      rw [Measure.integral_compProd hInt]
      calc
        _ ≤ ∫ p, Real.exp (θ * scalarFineWeightedLagBlockSum z dt N ρ w k p) *
            Real.exp ((2048*Real.exp 1*h^2)*(θ*w k)^2) ∂scalarLagBlockHistoryLaw z dt N k := by
          apply integral_mono_ae
            hInt.integral_compProd
            (hp.1.mul_const _) (ae_of_all _ hfiber_bound)
        _ ≤ Real.exp ((2048*Real.exp 1*h^2)*θ^2*∑ j ∈ Finset.range k, (w j)^2) *
            Real.exp ((2048*Real.exp 1*h^2)*(θ*w k)^2) := by
          rw [integral_mul_const]
          exact mul_le_mul_of_nonneg_right hp.2 (Real.exp_pos _).le
        _ = _ := by
          rw [← Real.exp_add, Finset.sum_range_succ]
          congr 1
          ring

lemma scalarFineWeightedLagBlockSum_local_mgf (z : ℝ) (dt : ℕ → ℝ≥0) (N : ℕ) (ρ : ℕ → ℕ → ℝ) (hρ : ∀ j k, |ρ j k| ≤ 1)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hdt : ∀ j < N, (dt j : ℝ) ≤ 1)
    (hduration : (∑ j ∈ Finset.range N, (dt j : ℝ)) ≤ h)
    (w : ℕ → ℝ) (A : ℝ) (hA : 0 < A) (k : ℕ) (hw : ∀ j < k, |w j| ≤ A) :
    Concentration.LocalQuadraticMGF (scalarFineWeightedLagBlockSum z dt N ρ w k)
      (scalarLagBlockHistoryLaw z dt N k)
      ((2048*Real.exp 1*h^2)*∑ j ∈ Finset.range k, (w j)^2) (1/(32*h*A)) := by
  constructor
  · intro θ hθ
    exact (scalarFineWeightedLagBlockSum_mgf_bound z dt N ρ hρ h hh hh1 hdt hduration w A hA θ hθ k hw).1
  · intro θ hθ
    convert (scalarFineWeightedLagBlockSum_mgf_bound z dt N ρ hρ h hh hh1 hdt hduration w A hA θ hθ k hw).2 using 1
    congr 1
    ring

lemma scalarFineWeightedLagBlockSum_local_mgf_of_budget (z : ℝ) (dt : ℕ → ℝ≥0) (N : ℕ) (ρ : ℕ → ℕ → ℝ) (hρ : ∀ j k, |ρ j k| ≤ 1)
    (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hdt : ∀ j < N, (dt j : ℝ) ≤ 1)
    (hduration : (∑ j ∈ Finset.range N, (dt j : ℝ)) ≤ h)
    (w : ℕ → ℝ) (A : ℝ) (hA : 0 < A) (k : ℕ) (hw : ∀ j < k, |w j| ≤ A)
    (T : ℝ) (hbudget : h * ∑ j ∈ Finset.range k, (w j)^2 ≤ T) :
    Concentration.LocalQuadraticMGF (scalarFineWeightedLagBlockSum z dt N ρ w k)
      (scalarLagBlockHistoryLaw z dt N k) (2048*Real.exp 1*T*h) (1/(32*h*A)) := by
  have hbase := scalarFineWeightedLagBlockSum_local_mgf z dt N ρ hρ h hh hh1 hdt hduration w A hA k hw
  have hvariance : (2048*Real.exp 1*h^2)*∑ j ∈ Finset.range k, (w j)^2 ≤
      2048*Real.exp 1*T*h := by
    have hb := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ 2048*Real.exp 1*h)
    nlinarith only [hb]
  constructor
  · exact hbase.integrable_exp_mul
  · intro θ hθ
    apply (hbase.mgf_le θ hθ).trans
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hvariance (sq_nonneg θ))

end SKConstants
