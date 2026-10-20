module
public import SKConstants.ScalarProcessCausalReconstruction
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Independence.Integration

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace SKConstants
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

def scalarBrownianBridgeProcess (T : ℝ≥0) (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ := B t ω - (t : ℝ)/(T : ℝ)*B T ω

theorem scalarBrownianBridgeProcess_indep_endpoint
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) :
    IndepFun (B T) (fun ω (t : Set.Iic T) => scalarBrownianBridgeProcess T B t ω) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hJ : IsGaussianProcess (Sum.elim (fun _ : Unit => B T)
      (fun t : Set.Iic T => scalarBrownianBridgeProcess T B t)) P := by
    apply hB.isGaussianProcess.of_isGaussianProcess
    rintro (_ | ⟨t,ht⟩)
    · exact ⟨{T},
        { toFun x := x ⟨T, by simp⟩
          map_add' x y := by simp
          map_smul' c x := by simp }, by simp⟩
    · exact ⟨{T,t},
        { toFun x := x ⟨t,by simp⟩-(t : ℝ)/(T : ℝ)*x ⟨T,by simp⟩
          map_add' x y := by simp; ring
          map_smul' c x := by simp; ring }, by simp [scalarBrownianBridgeProcess]⟩
  have hm (t : Set.Iic T) : AEMeasurable (scalarBrownianBridgeProcess T B t) P :=
    (hB.aemeasurable _).sub ((hB.aemeasurable _).const_mul _)
  have hcov (_ : Unit) (t : Set.Iic T) :
      cov[B T, scalarBrownianBridgeProcess T B t;P] = 0 := by
    change cov[B T, fun ω => B t ω-(t.val : ℝ)/(T : ℝ)*B T ω;P] = 0
    rw [covariance_fun_sub_right, covariance_const_mul_right,
      hB.covariance_eval, hB.covariance_eval]
    rw [show (min T t.val : ℝ≥0) = t.val from min_eq_right t.property, min_self]
    · field_simp [(NNReal.coe_pos.mpr hT).ne']
      ring
    · exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    · exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
    · exact ((hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two).const_mul _
  have hi := hJ.indepFun_of_covariance_eq_zero (fun _ => hB.aemeasurable T) hm hcov
  simpa only [Function.comp_def, id_eq] using hi.comp (measurable_pi_apply ()) measurable_id

def scalarBrownianBridgePath (T : ℝ≥0) (f : ScalarContinuousPath T) : ScalarContinuousPath T :=
  ⟨fun t => f t-(t : ℝ)/(T : ℝ)*f ⟨T,T.coe_nonneg,le_rfl⟩,
    f.continuous.sub ((continuous_subtype_val.div_const _).mul continuous_const)⟩

def scalarBrownianBridgeComplete (T : ℝ≥0) (p : ℝ × ScalarContinuousPath T) : ScalarContinuousPath T :=
  ⟨fun t => p.2 t+(t : ℝ)/(T : ℝ)*p.1,
    p.2.continuous.add ((continuous_subtype_val.div_const _).mul continuous_const)⟩

theorem measurable_scalarBrownianBridgePath (T : ℝ≥0) : Measurable (scalarBrownianBridgePath T) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (ContinuousMap.measurable_eval t).sub ((ContinuousMap.measurable_eval _).const_mul _)

theorem measurable_scalarBrownianBridgeComplete (T : ℝ≥0) : Measurable (scalarBrownianBridgeComplete T) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact ((ContinuousMap.measurable_eval t).comp measurable_snd).add (measurable_fst.const_mul _)

theorem scalarBrownianBridgeComplete_path (T : ℝ≥0) (f : ScalarContinuousPath T) :
    scalarBrownianBridgeComplete T (f ⟨T,T.coe_nonneg,le_rfl⟩,scalarBrownianBridgePath T f) = f := by
  ext t
  dsimp [scalarBrownianBridgeComplete,scalarBrownianBridgePath]
  ring

theorem scalarBrownianBridgePath_indep_endpoint
    (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (F : Ω → ScalarContinuousPath T)
    (hF : ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) (T : ℝ), F ω t = B ⟨t,t.property.1⟩ ω) :
    IndepFun (B T) (fun ω => scalarBrownianBridgePath T (F ω)) P := by
  apply indepFun_scalarPathVersion_of_past P T (scalarBrownianBridgeProcess T B)
    (fun ω => scalarBrownianBridgePath T (F ω)) (B T) _
    (scalarBrownianBridgeProcess_indep_endpoint P B hB T hT)
  filter_upwards [hF] with ω hω
  intro t
  dsimp only [scalarBrownianBridgePath, ContinuousMap.coe_mk, scalarBrownianBridgeProcess]
  rw [hω t, hω ⟨T,T.coe_nonneg,le_rfl⟩]
  rfl

theorem scalarBrownianBridgeComplete_law
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (hB : IsPreBrownianReal B P)
    (T : ℝ≥0) (hT : 0 < T) (F : Ω → ScalarContinuousPath T) (hFm : Measurable F)
    (hF : ∀ᵐ ω ∂P, ∀ t : Set.Icc (0 : ℝ) (T : ℝ), F ω t = B ⟨t,t.property.1⟩ ω) :
    ((gaussianReal 0 T).prod (P.map (fun ω => scalarBrownianBridgePath T (F ω)))).map
      (scalarBrownianBridgeComplete T) = P.map F := by
  have hbridge : Measurable (fun ω => scalarBrownianBridgePath T (F ω)) :=
    (measurable_scalarBrownianBridgePath T).comp hFm
  have hi := scalarBrownianBridgePath_indep_endpoint P B hB T hT F hF
  have hp := hi.map_prod_eq_prod_map_map (hB.aemeasurable T) hbridge.aemeasurable
  rw [(hB.hasLaw_eval T).map_eq] at hp
  rw [← hp, AEMeasurable.map_map_of_aemeasurable (measurable_scalarBrownianBridgeComplete T).aemeasurable
    ((hB.aemeasurable T).prodMk hbridge.aemeasurable)]
  apply Measure.map_congr
  filter_upwards [hF] with ω hω
  change scalarBrownianBridgeComplete T (B T ω,scalarBrownianBridgePath T (F ω)) = F ω
  have he : F ω ⟨T,T.coe_nonneg,le_rfl⟩ = B T ω := hω ⟨T,T.coe_nonneg,le_rfl⟩
  rw [← he]
  exact scalarBrownianBridgeComplete_path T (F ω)

end SKConstants
