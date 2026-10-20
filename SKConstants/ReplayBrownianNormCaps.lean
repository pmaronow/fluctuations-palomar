module
public import SKConstants.BrownianPathScalingCaps
public import SKConstants.GaussianProposalScalarPrefixReplay
import Mathlib.Tactic
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ENNReal NNReal Topology
namespace SKConstants.BrownianNormCaps
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem primitiveBridgeStream_energy_tail {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) :
    ∃ C : ℝ,0<C ∧ ∀ (T : ℕ→ℝ≥0) (n : ℕ) (I : Finset ℕ),
      (∀ j∈I,0<T j) → ∀ t : ℝ,0≤t →
      (Measure.infinitePi (fun j : ℕ=>Measure.pi
        (fun _ : Fin n=>scalarPrimitiveBridgePathLaw W (T j)))).real
        {f | ∃ j∈I,4*(T j:ℝ)*C*((n:ℝ)+t)≤pathEnergy n (f j)} ≤
      (I.card:ℝ)*exp (-(n:ℝ)-t) := by
  obtain ⟨C,hC,hCap⟩ := primitiveBridgePathLaw_uniform_energy_tail W
  refine ⟨C,hC,fun T n I hT t ht=>?_⟩
  let μ := Measure.infinitePi (fun j : ℕ=>Measure.pi
    (fun _ : Fin n=>scalarPrimitiveBridgePathLaw W (T j)))
  let A : ℕ→Set ((j : ℕ)→Fin n→ScalarContinuousPath (T j)) :=
    fun j=>{f | 4*(T j:ℝ)*C*((n:ℝ)+t)≤pathEnergy n (f j)}
  have hEach (j : ℕ) (hj : j∈I) : μ.real (A j)≤exp (-(n:ℝ)-t) := by
    have hs : MeasurableSet {f : Fin n→ScalarContinuousPath (T j) |
        4*(T j:ℝ)*C*((n:ℝ)+t)≤pathEnergy n f} := by
      apply measurableSet_le measurable_const
      unfold pathEnergy
      fun_prop
    have hp := (measurePreserving_eval_infinitePi
      (fun j : ℕ=>Measure.pi (fun _ : Fin n=>scalarPrimitiveBridgePathLaw W (T j))) j).map_eq
    change μ.real ((fun f=>f j) ⁻¹' {f : Fin n→ScalarContinuousPath (T j) |
      4*(T j:ℝ)*C*((n:ℝ)+t)≤pathEnergy n f})≤exp (-(n:ℝ)-t)
    rw [← map_measureReal_apply (measurable_pi_apply j) hs,hp]
    exact hCap (T j) (hT j hj) n t ht
  calc
    _ = μ.real (⋃ j∈I,A j) := by
      congr 1
      ext f
      simp [A]
    _ ≤ ∑ j∈I,μ.real (A j) := measureReal_biUnion_finset_le I A
    _ ≤ ∑ _j∈I,exp (-(n:ℝ)-t) := Finset.sum_le_sum (fun j hj=>hEach j hj)
    _ = _ := by simp

end SKConstants.BrownianNormCaps
