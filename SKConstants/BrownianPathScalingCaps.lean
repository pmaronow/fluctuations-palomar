module
public import SKConstants.BrownianPathNormCaps
import Mathlib.Tactic

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal Topology
namespace SKConstants.BrownianNormCaps
set_option maxHeartbeats 1000000

def normalizePath (T : ℝ≥0) (f : ScalarContinuousPath T) : ScalarContinuousPath 1 :=
  ⟨fun t => (sqrt T)⁻¹*f ⟨(T:ℝ)*t,
    mul_nonneg T.coe_nonneg t.property.1,
    by simpa using mul_le_mul_of_nonneg_left t.property.2 T.coe_nonneg⟩,
    continuous_const.mul (f.continuous.comp (by fun_prop))⟩

lemma measurable_normalizePath (T : ℝ≥0) : Measurable (normalizePath T) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact (ContinuousMap.measurable_eval _).const_mul _

lemma norm_le_normalizePath (T : ℝ≥0) (hT : 0<T) (f : ScalarContinuousPath T) :
    ‖f‖ ≤ sqrt T * ‖normalizePath T f‖ := by
  have hTp : 0<(T:ℝ) := hT
  have hs : sqrt (T:ℝ) ≠ 0 := (sqrt_pos.mpr hTp).ne'
  apply (ContinuousMap.norm_le _ (mul_nonneg (sqrt_nonneg _) (norm_nonneg _))).mpr
  intro t
  let u : Icc (0:ℝ) (1:ℝ) := ⟨(t:ℝ)/(T:ℝ),div_nonneg t.property.1 hTp.le,
    (div_le_one hTp).mpr t.property.2⟩
  have he : f t = sqrt T * normalizePath T f u := by
    change f t = sqrt T * ((sqrt T)⁻¹*f _)
    rw [← mul_assoc,mul_inv_cancel₀ hs,one_mul]
    congr 1
    apply Subtype.ext
    dsimp [u]
    field_simp
  rw [he,norm_mul,Real.norm_eq_abs,abs_of_nonneg (sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left ((normalizePath T f).norm_coe_le_norm u) (sqrt_nonneg _)

lemma norm_sq_le_normalizePath (T : ℝ≥0) (hT : 0<T) (f : ScalarContinuousPath T) :
    ‖f‖^2 ≤ (T:ℝ)*‖normalizePath T f‖^2 := by
  have hp := pow_le_pow_left₀ (norm_nonneg _) (norm_le_normalizePath T hT f) 2
  simpa only [mul_pow,Real.sq_sqrt T.coe_nonneg] using hp

theorem normalizePath_law {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (T : ℝ≥0) (hT : 0<T) :
    (scalarPrimitiveBrownianPathLaw W T).map (normalizePath T) =
      scalarPrimitiveBrownianPathLaw W 1 := by
  let := W.isProbability
  rw [scalarPrimitiveBrownianPathLaw,Measure.map_map (measurable_normalizePath T)
    (measurable_scalarPrimitiveBrownianPathVersion W T)]
  apply scalarBrownian_continuousPath_law_unique W.law W.law
    (fun t w => (sqrt T)⁻¹*W.B (T*t) w) W.B
    (W.brownian.smul hT.ne').toIsPreBrownianReal W.brownian.toIsPreBrownianReal
    1 _ _ ((measurable_normalizePath T).comp
      (measurable_scalarPrimitiveBrownianPathVersion W T))
    (measurable_scalarPrimitiveBrownianPathVersion W 1) _
    (scalarPrimitiveBrownianPathVersion_ae W 1)
  filter_upwards [scalarPrimitiveBrownianPathVersion_ae W T] with w hw t
  change (sqrt T)⁻¹*scalarPrimitiveBrownianPathVersion W T w _ = _
  rw [hw]
  rfl

lemma energy_le_normalizePath (T : ℝ≥0) (hT : 0<T) (n : ℕ)
    (f : Fin n → ScalarContinuousPath T) :
    pathEnergy n f ≤ (T:ℝ)*pathEnergy n (fun i => normalizePath T (f i)) := by
  rw [pathEnergy,pathEnergy,Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => norm_sq_le_normalizePath T hT (f i))

theorem primitivePathLaw_uniform_energy_tail {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) :
    ∃ C : ℝ,0<C ∧ ∀ (T : ℝ≥0),0<T → ∀ (n : ℕ) (t : ℝ),0≤t →
      (Measure.pi (fun _ : Fin n=>scalarPrimitiveBrownianPathLaw W T)).real
        {f | (T:ℝ)*C*((n:ℝ)+t)≤pathEnergy n f} ≤exp (-(n:ℝ)-t) := by
  obtain ⟨C,hC,hCap⟩ := primitivePathLaw_energy_tail W 1
  refine ⟨C,hC,fun T hT n t ht=>?_⟩
  let μ := Measure.pi (fun _ : Fin n=>scalarPrimitiveBrownianPathLaw W T)
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let N : (Fin n→ScalarContinuousPath T) → Fin n→ScalarContinuousPath 1 :=
    fun f i=>normalizePath T (f i)
  have hN : Measurable N := Measurable.of_eval (fun i =>
    (measurable_normalizePath T).comp (measurable_pi_apply i))
  have hlaw : μ.map N = Measure.pi (fun _ : Fin n=>scalarPrimitiveBrownianPathLaw W 1) := by
    rw [Measure.pi_map_pi (fun _ => (measurable_normalizePath T).aemeasurable)]
    simp only [normalizePath_law W T hT]
  have hs : MeasurableSet {f : Fin n→ScalarContinuousPath 1 |
      C*((n:ℝ)+t)≤pathEnergy n f} := by
    apply measurableSet_le measurable_const
    unfold pathEnergy
    fun_prop
  calc
    _ ≤ μ.real (N ⁻¹' {f | C*((n:ℝ)+t)≤pathEnergy n f}) := by
      apply measureReal_mono (h₂ := measure_ne_top μ _)
      intro f hf
      have he := energy_le_normalizePath T hT n f
      change C*((n:ℝ)+t) ≤ pathEnergy n (N f)
      have hTp : 0<(T:ℝ) := hT
      change (T:ℝ)*C*((n:ℝ)+t) ≤ pathEnergy n f at hf
      change pathEnergy n f ≤ (T:ℝ)*pathEnergy n (N f) at he
      nlinarith
    _ = (μ.map N).real {f | C*((n:ℝ)+t)≤pathEnergy n f} :=
      (map_measureReal_apply hN hs).symm
    _ ≤ exp (-(n:ℝ)-t) := by rw [hlaw]; exact hCap n t ht

lemma norm_scalarBrownianBridgePath (T : ℝ≥0) (f : ScalarContinuousPath T) :
    ‖scalarBrownianBridgePath T f‖ ≤ 2*‖f‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  have hcoef : |(t:ℝ)/(T:ℝ)|≤1 := by
    rw [abs_of_nonneg (div_nonneg t.property.1 T.coe_nonneg)]
    by_cases hT : T=0
    · simp [hT]
    · exact (div_le_one (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hT))).mpr t.property.2
  change ‖f t-(t:ℝ)/(T:ℝ)*f _‖≤_
  calc
    _ ≤ ‖f t‖+‖(t:ℝ)/(T:ℝ)*f _‖ := norm_sub_le _ _
    _ ≤ ‖f‖+1*‖f‖ := add_le_add (f.norm_coe_le_norm _) (by
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul hcoef (f.norm_coe_le_norm _) (norm_nonneg _) (by norm_num))
    _ = 2*‖f‖ := by ring

lemma energy_scalarBrownianBridgePath (T : ℝ≥0) (n : ℕ)
    (f : Fin n → ScalarContinuousPath T) :
    pathEnergy n (fun i => scalarBrownianBridgePath T (f i)) ≤ 4*pathEnergy n f := by
  rw [pathEnergy,pathEnergy,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_scalarBrownianBridgePath T (f i)) 2
  nlinarith

theorem primitiveBridgePathLaw_uniform_energy_tail {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) :
    ∃ C : ℝ,0<C ∧ ∀ (T : ℝ≥0),0<T → ∀ (n : ℕ) (t : ℝ),0≤t →
      (Measure.pi (fun _ : Fin n=>scalarPrimitiveBridgePathLaw W T)).real
        {f | 4*(T:ℝ)*C*((n:ℝ)+t)≤pathEnergy n f} ≤exp (-(n:ℝ)-t) := by
  obtain ⟨C,hC,hCap⟩ := primitivePathLaw_uniform_energy_tail W
  refine ⟨C,hC,fun T hT n t ht=>?_⟩
  let μ := Measure.pi (fun _ : Fin n=>scalarPrimitiveBrownianPathLaw W T)
  haveI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  let N : (Fin n→ScalarContinuousPath T) → Fin n→ScalarContinuousPath T :=
    fun f i=>scalarBrownianBridgePath T (f i)
  have hN : Measurable N := Measurable.of_eval (fun i =>
    (measurable_scalarBrownianBridgePath T).comp (measurable_pi_apply i))
  have hlaw : μ.map N = Measure.pi (fun _ : Fin n=>scalarPrimitiveBridgePathLaw W T) :=
    Measure.pi_map_pi (fun _ => (measurable_scalarBrownianBridgePath T).aemeasurable)
  have hs : MeasurableSet {f : Fin n→ScalarContinuousPath T |
      4*(T:ℝ)*C*((n:ℝ)+t)≤pathEnergy n f} := by
    apply measurableSet_le measurable_const
    unfold pathEnergy
    fun_prop
  rw [← hlaw,map_measureReal_apply hN hs]
  calc
    _ ≤ μ.real {f | (T:ℝ)*C*((n:ℝ)+t)≤pathEnergy n f} := by
      apply measureReal_mono (h₂ := measure_ne_top μ _)
      intro f hf
      have he := energy_scalarBrownianBridgePath T n f
      change (T:ℝ)*C*((n:ℝ)+t) ≤ pathEnergy n f
      change 4*(T:ℝ)*C*((n:ℝ)+t)≤pathEnergy n (N f) at hf
      dsimp [N] at hf
      nlinarith
    _ ≤ exp (-(n:ℝ)-t) := hCap T hT n t ht

end SKConstants.BrownianNormCaps
