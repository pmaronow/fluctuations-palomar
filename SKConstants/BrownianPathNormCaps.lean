module
public import SKConstants.GaussianProposalScalarInitialState
public import Mathlib.Probability.Distributions.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic
/-!
# Supremum-norm exponential bounds for genuine Brownian paths

The Gaussian path rotation proof is adapted from OpenAI/math, commit
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb,
OAI/Probability/SKGap/Brownian/BrownianPathFernique.lean.
The finite-product Chernoff argument is adapted from its IndependentPathTail.lean.
Only actual finite-dimensional Brownian laws and measurable continuous versions
are used; no supremum-norm bound is supplied as a hypothesis.
-/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set TopologicalSpace
open scoped BigOperators ENNReal NNReal Topology
namespace SKConstants.BrownianNormCaps
set_option maxHeartbeats 1000000
variable {H : ℝ≥0}
instance intervalNonempty : Nonempty (Set.Icc (0 : ℝ) (H : ℝ)) := ⟨⟨0,le_rfl,H.coe_nonneg⟩⟩

def pathPairEvaluations (p : ScalarContinuousPath H × ScalarContinuousPath H) : ℕ→ℝ×ℝ :=
  fun k=>(p.1 (denseSeq (Set.Icc (0 : ℝ) (H : ℝ)) k),p.2 (denseSeq (Set.Icc (0 : ℝ) (H : ℝ)) k))

lemma continuous_pathPairEvaluations : Continuous (pathPairEvaluations (H := H)) := by
  apply continuous_pi
  intro k
  exact ((ContinuousMap.evalCLM ℝ (denseSeq (Set.Icc (0 : ℝ) (H : ℝ)) k)).continuous.comp continuous_fst).prodMk
    ((ContinuousMap.evalCLM ℝ (denseSeq (Set.Icc (0 : ℝ) (H : ℝ)) k)).continuous.comp continuous_snd)

lemma injective_pathPairEvaluations : Function.Injective (pathPairEvaluations (H := H)) := by
  intro p q h
  apply Prod.ext
  · apply ContinuousMap.coe_injective
    apply (denseRange_denseSeq (Set.Icc (0 : ℝ) (H : ℝ))).equalizer p.1.continuous q.1.continuous
    funext k
    exact congrArg Prod.fst (congrFun h k)
  · apply ContinuousMap.coe_injective
    apply (denseRange_denseSeq (Set.Icc (0 : ℝ) (H : ℝ))).equalizer p.2.continuous q.2.continuous
    funext k
    exact congrArg Prod.snd (congrFun h k)

lemma measurableEmbedding_pathPairEvaluations : MeasurableEmbedding (pathPairEvaluations (H := H)) :=
  continuous_pathPairEvaluations.measurableEmbedding injective_pathPairEvaluations

lemma centered_gaussian_path_rotation (μ : Measure (ScalarContinuousPath H)) [IsProbabilityMeasure μ]
    (hG : IsGaussianProcess (fun t : Set.Icc (0 : ℝ) (H : ℝ)=>fun f : ScalarContinuousPath H=>f t) μ)
    (h0 : ∀ t : Set.Icc (0 : ℝ) (H : ℝ), ∫ f : ScalarContinuousPath H,f t ∂μ=0) (θ : ℝ) :
    (μ.prod μ).map (ContinuousLinearMap.rotation θ)=μ.prod μ := by
  apply measurableEmbedding_pathPairEvaluations.map_injective
  rw [Measure.map_map continuous_pathPairEvaluations.measurable (by fun_prop)]
  apply (map_eq_iff_forall_finset_map_restrict_eq
    (continuous_pathPairEvaluations.measurable.comp (by fun_prop)).aemeasurable
    continuous_pathPairEvaluations.measurable.aemeasurable).2
  intro s
  let e : ScalarContinuousPath H→s→ℝ := fun f i=>f (denseSeq (Set.Icc (0 : ℝ) (H : ℝ)) i)
  have he : Measurable e := by
    apply Measurable.of_eval
    intro i
    exact (ContinuousMap.evalCLM ℝ (denseSeq (Set.Icc (0 : ℝ) (H : ℝ)) i)).continuous.measurable
  have heG : HasGaussianLaw e μ := (hG.comp_right (denseSeq (Set.Icc (0 : ℝ) (H : ℝ)))).hasGaussianLaw s
  let ν := μ.map e
  let : IsGaussian ν := heG.isGaussian_map
  have hν0 : (∫ x : s→ℝ,id x ∂ν)=0 := by
    rw [show ν=μ.map e from rfl,integral_map he.aemeasurable measurable_id.aestronglyMeasurable]
    ext i
    have hh := (ContinuousLinearMap.proj i : (s→ℝ)→L[ℝ]ℝ).integral_comp_comm heG.integrable
    exact hh.symm.trans (h0 _)
  have hr := IsGaussian.map_rotation_eq_self (μ:=ν) hν0 θ
  let pair : ((s→ℝ)×(s→ℝ))→s→ℝ×ℝ := fun p i=>(p.1 i,p.2 i)
  have hp : Measurable pair := by fun_prop
  have hr' := congrArg (Measure.map pair) hr
  rw [Measure.map_map hp (by fun_prop)] at hr'
  have hn : ν.prod ν=(μ.prod μ).map (Prod.map e e) := Measure.map_prod_map μ μ he he
  rw [hn,Measure.map_map (hp.comp (by fun_prop)) (he.prodMap he),
    Measure.map_map hp (he.prodMap he)] at hr'
  convert hr' using 1
  · congr 1
  · rfl

theorem centered_gaussian_path_fernique (μ : Measure (ScalarContinuousPath H)) [IsProbabilityMeasure μ]
    (hG : IsGaussianProcess (fun t : Set.Icc (0 : ℝ) (H : ℝ)=>fun f : ScalarContinuousPath H=>f t) μ)
    (h0 : ∀ t : Set.Icc (0 : ℝ) (H : ℝ), ∫ f : ScalarContinuousPath H,f t ∂μ=0) :
    ∃ a : ℝ, 0<a ∧ Integrable (fun f : ScalarContinuousPath H=>exp (a*‖f‖^2)) μ :=
  exists_integrable_exp_sq_of_map_rotation_eq_self
    (centered_gaussian_path_rotation μ hG h0 (-(π/4)))


/-- The literal primitive continuous Brownian path law is a centered Gaussian
process law, derived by pushing the actual finite-dimensional Brownian laws. -/
theorem primitivePathLaw_gaussian {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) :
    IsGaussianProcess (fun t : Icc (0:ℝ) (H:ℝ) => fun f : ScalarContinuousPath H => f t)
      (scalarPrimitiveBrownianPathLaw W H) := by
  have hG := W.brownian.isGaussianProcess.comp_right
    (fun t : Icc (0:ℝ) (H:ℝ) => (⟨t,t.property.1⟩ : ℝ≥0))
  have hv := hG.congr (fun t => (scalarPrimitiveBrownianPathVersion_ae W H).mono
    (fun w hw => (hw t).symm))
  constructor
  intro I
  have he : Measurable (fun f : ScalarContinuousPath H => I.restrict (fun t => f t)) :=
    Measurable.of_eval (fun t => ContinuousMap.measurable_eval (t : Icc (0:ℝ) (H:ℝ)))
  refine ⟨he.aemeasurable,?_⟩
  change IsGaussian ((W.law.map (scalarPrimitiveBrownianPathVersion W H)).map _)
  rw [Measure.map_map he (measurable_scalarPrimitiveBrownianPathVersion W H)]
  exact (hv.hasGaussianLaw I).isGaussian_map

theorem primitivePathLaw_centered {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0)
    (t : Icc (0:ℝ) (H:ℝ)) :
    (∫ f : ScalarContinuousPath H,f t ∂scalarPrimitiveBrownianPathLaw W H)=0 := by
  rw [scalarPrimitiveBrownianPathLaw,integral_map
    (measurable_scalarPrimitiveBrownianPathVersion W H).aemeasurable
    (ContinuousMap.measurable_eval t).aestronglyMeasurable]
  calc
    _ = ∫ w,W.B ⟨t,t.property.1⟩ w ∂W.law := integral_congr_ae
      ((scalarPrimitiveBrownianPathVersion_ae W H).mono (fun w hw => hw t))
    _ = 0 := W.brownian.integral_eval _

theorem primitivePathLaw_fernique {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) :
    ∃ a : ℝ,0<a ∧ Integrable (fun f : ScalarContinuousPath H => exp (a*‖f‖^2))
      (scalarPrimitiveBrownianPathLaw W H) :=
  centered_gaussian_path_fernique _ (primitivePathLaw_gaussian W H)
    (primitivePathLaw_centered W H)

/-- Total squared supremum norm of independent rows. -/
def pathEnergy (n : ℕ) (f : Fin n → ScalarContinuousPath H) : ℝ := ∑ i,‖f i‖^2

lemma energy_exponential_prod (n : ℕ) (a : ℝ) (f : Fin n → ScalarContinuousPath H) :
    exp (a*pathEnergy n f)=∏ i,exp (a*‖f i‖^2) := by
  rw [pathEnergy,Finset.mul_sum,exp_sum]

lemma pathEnergy_exponential_integrable (μ : Measure (ScalarContinuousPath H))
    [IsProbabilityMeasure μ] (a : ℝ)
    (hi : Integrable (fun f : ScalarContinuousPath H => exp (a*‖f‖^2)) μ) (n : ℕ) :
    Integrable (fun f=>exp (a*pathEnergy n f)) (Measure.pi (fun _ : Fin n=>μ)) := by
  simp_rw [energy_exponential_prod]
  exact Integrable.fintype_prod (fun _=>hi)

lemma pathEnergy_exponential_integral (μ : Measure (ScalarContinuousPath H))
    [IsProbabilityMeasure μ] (a : ℝ) (n : ℕ) :
    (∫ f,exp (a*pathEnergy n f) ∂Measure.pi (fun _ : Fin n=>μ))=
      (∫ f : ScalarContinuousPath H,exp (a*‖f‖^2) ∂μ)^n := by
  simp_rw [energy_exponential_prod]
  simpa using integral_fintype_prod_eq_pow (ι:=Fin n) (μ:=μ)
    (fun f : ScalarContinuousPath H=>exp (a*‖f‖^2))

/-- A genuine exponential tail for the entire row energy. The constant is
uniform in row dimension and the extra parameter permits finite union bounds. -/
theorem pathEnergy_tail_of_fernique (μ : Measure (ScalarContinuousPath H))
    [IsProbabilityMeasure μ] {a : ℝ} (ha : 0<a)
    (hi : Integrable (fun f : ScalarContinuousPath H => exp (a*‖f‖^2)) μ) :
    ∃ C : ℝ,0<C ∧ ∀ (n : ℕ) (t : ℝ),0≤t →
      (Measure.pi (fun _ : Fin n=>μ)).real {f | C*((n:ℝ)+t)≤pathEnergy n f}
        ≤exp (-(n:ℝ)-t) := by
  let M := ∫ f : ScalarContinuousPath H,exp (a*‖f‖^2) ∂μ
  have hM : 1≤M := by
    calc
      1 = ∫ _ : ScalarContinuousPath H,(1:ℝ) ∂μ := by simp
      _ ≤ M := integral_mono (integrable_const _) hi (fun f=>
        one_le_exp_iff.mpr (mul_nonneg ha.le (sq_nonneg _)))
  have hMp : 0<M := lt_of_lt_of_le zero_lt_one hM
  let C := (log M+1)/a
  have hC : 0<C := div_pos (by linarith [log_nonneg hM]) ha
  refine ⟨C,hC,fun n t ht=>?_⟩
  calc
    _ ≤ exp (-a*(C*((n:ℝ)+t)))*mgf (pathEnergy n)
        (Measure.pi (fun _ : Fin n=>μ)) a :=
      measure_ge_le_exp_mul_mgf _ ha.le (pathEnergy_exponential_integrable μ a hi n)
    _ = exp (-(n:ℝ)-(log M+1)*t) := by
      rw [mgf,pathEnergy_exponential_integral]
      change exp (-a*(C*((n:ℝ)+t)))*M^n=_
      rw [← exp_log hMp,← exp_nat_mul,← exp_add]
      congr 1
      dsimp [C]
      simp only [log_exp]
      field_simp
      ring
    _ ≤ exp (-(n:ℝ)-t) := exp_le_exp.mpr (by
      have := mul_nonneg (log_nonneg hM) ht
      nlinarith)

theorem primitivePathLaw_energy_tail {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (H : ℝ≥0) :
    ∃ C : ℝ,0<C ∧ ∀ (n : ℕ) (t : ℝ),0≤t →
      (Measure.pi (fun _ : Fin n=>scalarPrimitiveBrownianPathLaw W H)).real
        {f | C*((n:ℝ)+t)≤pathEnergy n f} ≤exp (-(n:ℝ)-t) := by
  obtain ⟨a,ha,hi⟩ := primitivePathLaw_fernique W H
  exact pathEnergy_tail_of_fernique (scalarPrimitiveBrownianPathLaw W H) ha hi

end SKConstants.BrownianNormCaps
