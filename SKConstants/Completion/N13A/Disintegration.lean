module

public import SKConstants.Completion.N13A.ChangeOfMeasure
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SKConstants.Completion.N13A
open GaussianProposal Blueprint

theorem uniformSpinLaw_singleton (n : ℕ) (x : Spin n) :
    uniformSpinLaw n {x} = ENNReal.ofReal (1 / (2:ℝ)^n) := by
  rw [uniformSpinLaw, finiteWeightMeasure_apply _ _ (measurableSet_singleton x)]
  simp

theorem uniformSpin_intrinsic_cancel (n : ℕ) (β K : ℝ) (x : Spin n) (g : Prim n) :
    ENNReal.ofReal (intrinsicDensity n β K (x,g)) * uniformSpinLaw n {x} =
      ENNReal.ofReal (Real.exp (K + β * goeSpinHamiltonian
        (1 / Real.sqrt (2*(n : ℝ))) x g)) := by
  rw [uniformSpinLaw_singleton]
  rw [← ENNReal.ofReal_mul
    (show 0 ≤ intrinsicDensity n β K (x,g) from (Real.exp_pos _).le)]
  congr 1
  unfold intrinsicDensity
  rw [show (n : ℝ)*Real.log 2 + K +
      β * goeSpinHamiltonian (1 / Real.sqrt (2*(n : ℝ))) x g =
      (n : ℝ)*Real.log 2 + (K +
        β * goeSpinHamiltonian (1 / Real.sqrt (2*(n : ℝ))) x g) by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
  field_simp

theorem intrinsic_endpoint_rectangle (n : ℕ) (β K : ℝ) (x : Spin n)
    (A : Set (Prim n)) (hA : MeasurableSet A) :
    ((unlinkedPrimitiveSpinFirstLaw n).withDensity
      (fun z => ENNReal.ofReal (intrinsicDensity n β K z))) ({x} ×ˢ A) =
      ∫⁻ g in A, ENNReal.ofReal (Real.exp (K + β * goeSpinHamiltonian
        (1 / Real.sqrt (2*(n : ℝ))) x g)) ∂primLaw n := by
  rw [withDensity_apply _ ((measurableSet_singleton x).prod hA)]
  change (∫⁻ z in {x} ×ˢ A, ENNReal.ofReal (intrinsicDensity n β K z)
    ∂(uniformSpinLaw n).prod (primLaw n)) = _
  rw [setLIntegral_prod _ ((measurable_intrinsicDensity n β K).ennreal_ofReal.aemeasurable.restrict),
    lintegral_singleton, ← lintegral_mul_const' _ _ (measure_ne_top _ _)]
  exact lintegral_congr (fun g => uniformSpin_intrinsic_cancel n β K x g)

theorem restricted_output_rectangle {U : Type*} [MeasurableSpace U]
    (n : ℕ) (η : Measure U) [SFinite η]
    (F : Prim n × U → Spin n) (hF : Measurable F)
    (E : Set (Prim n × U)) (hE : MeasurableSet E) (x : Spin n)
    (A : Set (Prim n)) (hA : MeasurableSet A) :
    ((((primLaw n).prod η).restrict E).map (fun y => (F y,y.1))) ({x} ×ˢ A) =
      ∫⁻ g in A, η {u | (g,u) ∈ E ∧ F (g,u) = x} ∂primLaw n := by
  have hS : MeasurableSet ((fun y : Prim n × U => (F y,y.1)) ⁻¹' ({x} ×ˢ A)) :=
    (hF.prodMk measurable_fst) ((measurableSet_singleton x).prod hA)
  rw [Measure.map_apply (hF.prodMk measurable_fst) ((measurableSet_singleton x).prod hA),
    Measure.restrict_apply hS, Measure.prod_apply (hS.inter hE), ← lintegral_indicator hA]
  apply lintegral_congr
  intro g
  by_cases hg : g ∈ A
  · simp only [hg, indicator_of_mem, mem_preimage, mem_prod, mem_singleton_iff,
      Prod.fst, Prod.snd]
    congr 1
    ext u
    simp [hg, and_comm, and_left_comm]
  · change η {u | (F (g,u) = x ∧ g ∈ A) ∧ (g,u) ∈ E} =
      A.indicator (fun g => η {u | (g,u) ∈ E ∧ F (g,u) = x}) g
    simp [hg]

theorem intrinsic_kernel_of_endpoint_domination {U : Type*} [MeasurableSpace U]
    (n : ℕ) (β K : ℝ) (η : Measure U) [IsProbabilityMeasure η]
    (F : Prim n × U → Spin n) (hF : Measurable F)
    (E : Set (Prim n × U)) (hE : MeasurableSet E)
    (hdom : ((((primLaw n).prod η).restrict E).map (fun y => (F y,y.1))) ≤
      (unlinkedPrimitiveSpinFirstLaw n).withDensity
        (fun z => ENNReal.ofReal (intrinsicDensity n β K z))) :
    ∀ᵐ g ∂primLaw n, ∀ x : Spin n,
      η.real {u | (g,u) ∈ E ∧ F (g,u) = x} ≤
        Real.exp (K + β * goeSpinHamiltonian (1 / Real.sqrt (2*(n : ℝ))) x g) := by
  have hx (x : Spin n) :
      (fun g => η {u | (g,u) ∈ E ∧ F (g,u) = x}) ≤ᵐ[primLaw n]
        (fun g => ENNReal.ofReal (Real.exp (K +
          β * goeSpinHamiltonian (1 / Real.sqrt (2*(n : ℝ))) x g))) := by
    have hS : MeasurableSet {y : Prim n × U | y ∈ E ∧ F y = x} :=
      hE.inter (hF (measurableSet_singleton x))
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (measurable_measure_prodMk_left hS)
    intro A hA _
    change (∫⁻ g in A, η {u | (g,u) ∈ E ∧ F (g,u) = x} ∂primLaw n) ≤ _
    rw [← restricted_output_rectangle n η F hF E hE x A hA,
      ← intrinsic_endpoint_rectangle n β K x A hA]
    exact hdom _
  have hall := (ae_all_iff.2 hx)
  filter_upwards [hall] with g hg
  intro x
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hg x)).trans_eq
    (ENNReal.toReal_ofReal (Real.exp_pos _).le)

end SKConstants.Completion.N13A
