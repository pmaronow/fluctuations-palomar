module
public import SKConstants.ScalarProcessLagFineBlocks

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

def scalarVariableLagBlockStepKernel (z : ℝ) (dt : ℕ → ℕ → ℝ≥0) (N k : ℕ) :
    Kernel (ScalarLagBlockHistory N k) (ScalarObservationHistory N) :=
  scalarLagBlockStepKernel z (dt k) N k

instance scalarVariableLagBlockStepKernel_isMarkov (z : ℝ) (dt : ℕ → ℕ → ℝ≥0) (N k : ℕ) :
    IsMarkovKernel (scalarVariableLagBlockStepKernel z dt N k) := by
  unfold scalarVariableLagBlockStepKernel
  infer_instance

lemma scalarVariableLagBlockStepKernel_apply (z : ℝ) (dt : ℕ → ℕ → ℝ≥0) (N k : ℕ)
    (p : ScalarLagBlockHistory N k) :
    scalarVariableLagBlockStepKernel z dt N k p =
      scalarObservationHistoryLaw (scalarLagBlockLastField z N k p) (dt k) N :=
  scalarLagBlockStepKernel_apply z (dt k) N k p

def scalarVariableLagBlockHistoryLaw (z : ℝ) (dt : ℕ → ℕ → ℝ≥0) (N : ℕ) :
    (k : ℕ) → Measure (ScalarLagBlockHistory N k)
  | 0 => Measure.dirac PUnit.unit
  | k+1 => scalarVariableLagBlockHistoryLaw z dt N k ⊗ₘ scalarVariableLagBlockStepKernel z dt N k

instance scalarVariableLagBlockHistoryLaw_isProbability (z : ℝ) (dt : ℕ → ℕ → ℝ≥0) (N k : ℕ) :
    IsProbabilityMeasure (scalarVariableLagBlockHistoryLaw z dt N k) := by
  induction k with
  | zero => change IsProbabilityMeasure (Measure.dirac PUnit.unit); infer_instance
  | succ k ih => change IsProbabilityMeasure (_ ⊗ₘ scalarVariableLagBlockStepKernel z dt N k); infer_instance

def scalarVariableFineWeightedLagBlockSum (z : ℝ) (dt : ℕ → ℕ → ℝ≥0) (N : ℕ)
    (ρ : ℕ → ℕ → ℝ) (w : ℕ → ℝ) : (k : ℕ) → ScalarLagBlockHistory N k → ℝ
  | 0, _ => 0
  | k+1, p => scalarVariableFineWeightedLagBlockSum z dt N ρ w k p.1+w k*
      scalarDeterministicLagInnovationSum (scalarLagBlockLastField z N k p.1) (dt k) (ρ k) N p.2

lemma measurable_scalarVariableFineWeightedLagBlockSum (z : ℝ) (dt : ℕ → ℕ → ℝ≥0) (N : ℕ)
    (ρ : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (k : ℕ) :
    Measurable (scalarVariableFineWeightedLagBlockSum z dt N ρ w k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih =>
    exact (ih.comp measurable_fst).add
      (((measurable_scalarDeterministicLagInnovationSum_joint (dt k) (ρ k) N).comp
        (((measurable_scalarLagBlockLastField z N k).comp measurable_fst).prodMk measurable_snd)).const_mul (w k))

lemma scalarVariableFineWeightedLagBlockSum_exp_succ (z : ℝ) (dt : ℕ → ℕ → ℝ≥0) (N : ℕ)
    (ρ : ℕ → ℕ → ℝ) (w : ℕ → ℝ) (k : ℕ) (p : ScalarLagBlockHistory N k)
    (q : ScalarObservationHistory N) (θ : ℝ) :
    Real.exp (θ*scalarVariableFineWeightedLagBlockSum z dt N ρ w (k+1) (p,q)) =
      Real.exp (θ*scalarVariableFineWeightedLagBlockSum z dt N ρ w k p)*
        Real.exp ((θ*w k)*scalarDeterministicLagInnovationSum (scalarLagBlockLastField z N k p) (dt k) (ρ k) N q) := by
  change Real.exp (θ*(_+_))=_
  rw [mul_add,Real.exp_add,mul_assoc]

lemma scalarVariableFineWeightedLagBlockSum_mgf_bound (z : ℝ) (dt : ℕ → ℕ → ℝ≥0)
    (N : ℕ) (ρ : ℕ → ℕ → ℝ) (hρ : ∀ j i, |ρ j i| ≤ 1)
    (h : ℕ → ℝ) (hh : ∀ j, 0<h j) (hh1 : ∀ j, h j≤1)
    (hdt : ∀ j i, i<N → (dt j i:ℝ)≤1)
    (hduration : ∀ j, (∑ i ∈ Finset.range N, (dt j i:ℝ))≤h j)
    (w : ℕ → ℝ) (θ : ℝ) (k : ℕ) (hθ : ∀ j<k, |θ*w j|≤1/(32*h j)) :
    Integrable (fun p => Real.exp (θ*scalarVariableFineWeightedLagBlockSum z dt N ρ w k p))
      (scalarVariableLagBlockHistoryLaw z dt N k) ∧
    mgf (scalarVariableFineWeightedLagBlockSum z dt N ρ w k)
      (scalarVariableLagBlockHistoryLaw z dt N k) θ≤
      Real.exp ((2048*Real.exp 1)*θ^2*∑ j ∈ Finset.range k, (h j)^2*(w j)^2) := by
  induction k with
  | zero =>
    constructor
    · simpa only [scalarVariableFineWeightedLagBlockSum, Nat.rec_zero, mul_zero, Real.exp_zero] using
        (integrable_const (1 : ℝ) : Integrable (fun _ : ScalarLagBlockHistory N 0 => (1 : ℝ))
          (scalarVariableLagBlockHistoryLaw z dt N 0))
    · simp [mgf, scalarVariableFineWeightedLagBlockSum, scalarVariableLagBlockHistoryLaw]
  | succ k ih =>
    have hp := ih (fun j hj => hθ j (by omega))
    have hparameter : |θ*w k| ≤ 1/(32*h k) := hθ k (by omega)
    have hfiber (p : ScalarLagBlockHistory N k) :
        Integrable (fun q => Real.exp (θ * scalarVariableFineWeightedLagBlockSum z dt N ρ w (k+1) (p,q)))
          (scalarVariableLagBlockStepKernel z dt N k p) := by
      rw [scalarVariableLagBlockStepKernel_apply]
      simp only [scalarVariableFineWeightedLagBlockSum_exp_succ]
      exact ((scalarDeterministicLagInnovationSum_local_mgf (scalarLagBlockLastField z N k p) (dt k) (ρ k) (hρ k)
        (h k) (hh k) (hh1 k) N (hdt k) (hduration k)).integrable_exp_mul (θ*w k) hparameter).const_mul _
    have hfiber_bound (p : ScalarLagBlockHistory N k) :
        (∫ q, Real.exp (θ * scalarVariableFineWeightedLagBlockSum z dt N ρ w (k+1) (p,q))
          ∂scalarVariableLagBlockStepKernel z dt N k p) ≤
        Real.exp (θ * scalarVariableFineWeightedLagBlockSum z dt N ρ w k p) *
          Real.exp ((2048*Real.exp 1*(h k)^2)*(θ*w k)^2) := by
      rw [scalarVariableLagBlockStepKernel_apply]
      simp only [scalarVariableFineWeightedLagBlockSum_exp_succ]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left ((scalarDeterministicLagInnovationSum_local_mgf
        (scalarLagBlockLastField z N k p) (dt k) (ρ k) (hρ k) (h k) (hh k) (hh1 k) N (hdt k) (hduration k)).mgf_le
        (θ*w k) hparameter) (Real.exp_pos _).le
    have hmeas : Measurable (fun p : ScalarLagBlockHistory N (k+1) =>
        Real.exp (θ * scalarVariableFineWeightedLagBlockSum z dt N ρ w (k+1) p)) :=
      ((measurable_scalarVariableFineWeightedLagBlockSum z dt N ρ w (k+1)).const_mul θ).exp
    have hInt : Integrable (fun p => Real.exp (θ * scalarVariableFineWeightedLagBlockSum z dt N ρ w (k+1) p))
        (scalarVariableLagBlockHistoryLaw z dt N (k+1)) := by
      change Integrable _ (scalarVariableLagBlockHistoryLaw z dt N k ⊗ₘ scalarVariableLagBlockStepKernel z dt N k)
      apply (Measure.integrable_compProd_iff hmeas.aestronglyMeasurable).2
      constructor
      · exact ae_of_all _ hfiber
      · have hm : StronglyMeasurable (fun p : ScalarLagBlockHistory N k =>
            ∫ q, ‖Real.exp (θ * scalarVariableFineWeightedLagBlockSum z dt N ρ w (k+1) (p,q))‖
              ∂scalarVariableLagBlockStepKernel z dt N k p) :=
          hmeas.norm.stronglyMeasurable.integral_kernel_prod_right'
        apply (hp.1.mul_const (Real.exp ((2048*Real.exp 1*(h k)^2)*(θ*w k)^2))).mono' hm.aestronglyMeasurable
        apply ae_of_all
        intro p
        simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [abs_of_nonneg (integral_nonneg (fun q => (Real.exp_pos _).le))]
        exact hfiber_bound p
    constructor
    · exact hInt
    · change (∫ p, Real.exp (θ * scalarVariableFineWeightedLagBlockSum z dt N ρ w (k+1) p)
        ∂scalarVariableLagBlockHistoryLaw z dt N k ⊗ₘ scalarVariableLagBlockStepKernel z dt N k) ≤ _
      rw [Measure.integral_compProd hInt]
      calc
        _ ≤ ∫ p, Real.exp (θ * scalarVariableFineWeightedLagBlockSum z dt N ρ w k p) *
            Real.exp ((2048*Real.exp 1*(h k)^2)*(θ*w k)^2) ∂scalarVariableLagBlockHistoryLaw z dt N k := by
          apply integral_mono_ae
            hInt.integral_compProd
            (hp.1.mul_const _) (ae_of_all _ hfiber_bound)
        _ ≤ Real.exp ((2048*Real.exp 1)*θ^2*∑ j ∈ Finset.range k, (h j)^2*(w j)^2) *
            Real.exp ((2048*Real.exp 1*(h k)^2)*(θ*w k)^2) := by
          rw [integral_mul_const]
          exact mul_le_mul_of_nonneg_right hp.2 (Real.exp_pos _).le
        _ = _ := by
          rw [← Real.exp_add, Finset.sum_range_succ]
          congr 1
          ring


lemma scalarVariableFineWeightedLagBlockSum_local_mgf_of_budget (z : ℝ) (dt : ℕ → ℕ → ℝ≥0)
    (N : ℕ) (ρ : ℕ → ℕ → ℝ) (hρ : ∀ j i, |ρ j i| ≤ 1)
    (h : ℕ → ℝ) (hh : ∀ j, 0<h j) (hh1 : ∀ j, h j≤1)
    (hdt : ∀ j i, i<N → (dt j i:ℝ)≤1)
    (hduration : ∀ j, (∑ i ∈ Finset.range N, (dt j i:ℝ))≤h j)
    (w : ℕ → ℝ) (k : ℕ) (δ : ℝ) (hδ : 0<δ) (A : ℝ) (_hA : 0<A)
    (hmax : ∀ j<k, h j*|w j|≤δ)
    (hbudget : (∑ j ∈ Finset.range k, (h j)^2*(w j)^2)≤A*δ) :
    Concentration.LocalQuadraticMGF (scalarVariableFineWeightedLagBlockSum z dt N ρ w k)
      (scalarVariableLagBlockHistoryLaw z dt N k) (2048*Real.exp 1*A*δ) (1/(32*δ)) := by
  have hparameter (θ : ℝ) (hθ : |θ|≤1/(32*δ)) (j : ℕ) (hj : j<k) :
      |θ*w j|≤1/(32*h j) := by
    rw [abs_mul]
    apply (le_div_iff₀ (mul_pos (by norm_num) (hh j) : 0<32*h j)).2
    calc
      |θ| * |w j| * (32*h j) = (|θ| * (32*δ))*(h j * |w j| / δ) := by field_simp
      _ ≤ 1*1 := mul_le_mul
        ((le_div_iff₀ (by positivity : 0<32*δ)).1 hθ)
        ((div_le_one hδ).2 (hmax j hj)) (div_nonneg (mul_nonneg (hh j).le (abs_nonneg _)) hδ.le) (by norm_num)
      _ = 1 := by ring
  constructor
  · intro θ hθ
    exact (scalarVariableFineWeightedLagBlockSum_mgf_bound z dt N ρ hρ h hh hh1 hdt hduration w θ k
      (hparameter θ hθ)).1
  · intro θ hθ
    apply (scalarVariableFineWeightedLagBlockSum_mgf_bound z dt N ρ hρ h hh hh1 hdt hduration w θ k
      (hparameter θ hθ)).2.trans
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hbudget
      (by positivity : 0≤(2048*Real.exp 1)*θ^2)
    nlinarith only [hm]

end SKConstants
