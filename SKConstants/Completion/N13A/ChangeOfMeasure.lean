module

public import SKConstants.Completion.N13A.Statements

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace SKConstants.Completion.N13A
open GaussianProposal Blueprint

theorem exponential_reference_recover {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (I : A → ℝ) (hI : AEMeasurable I μ) :
    (μ.withDensity (fun y => ENNReal.ofReal (Real.exp (-I y)))).withDensity
      (fun y => ENNReal.ofReal (Real.exp (I y))) = μ := by
  have hn : AEMeasurable (fun y => ENNReal.ofReal (Real.exp (-I y))) μ :=
    hI.neg.exp.ennreal_ofReal
  have hp : AEMeasurable (fun y => ENNReal.ofReal (Real.exp (I y))) μ :=
    hI.exp.ennreal_ofReal
  rw [← withDensity_mul₀ hn hp]
  have h : (fun y => ENNReal.ofReal (Real.exp (-I y)) *
      ENNReal.ofReal (Real.exp (I y))) = (fun _ => 1) := by
    funext y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    simp
  change μ.withDensity (fun y => ENNReal.ofReal (Real.exp (-I y)) *
    ENNReal.ofReal (Real.exp (I y))) = μ
  rw [h]
  exact withDensity_one

def intrinsicDensity (n : ℕ) (β K : ℝ) (z : Spin n × Prim n) : ℝ :=
  Real.exp ((n : ℝ)*Real.log 2 + K +
    β * goeSpinHamiltonian (1 / Real.sqrt (2*(n : ℝ))) z.1 z.2)

theorem measurable_intrinsicDensity (n : ℕ) (β K : ℝ) :
    Measurable (intrinsicDensity n β K) := by
  apply measurable_from_prod_countable_right
  intro x
  apply Continuous.measurable
  unfold intrinsicDensity goeSpinHamiltonian quadraticHamiltonian
  have hM := continuous_goeMatrix (V := Fin n) (1 / Real.sqrt (2*(n : ℝ)))
  fun_prop

theorem restricted_gibbs_after_partition_removal {A : Type*} [MeasurableSpace A]
    (n : ℕ) (β K : ℝ) (R : Measure A)
    (Y : A → Spin n × Prim n) (hY : Measurable Y)
    (hR : R.map Y = unlinkedPrimitiveSpinFirstLaw n)
    (I : A → ℝ) (E : Set A) (hE : MeasurableSet E)
    (hbound : ∀ y ∈ E, I y - (n : ℝ)*Real.log 2 -
      β * goeSpinHamiltonian (1 / Real.sqrt (2*(n : ℝ))) (Y y).1 (Y y).2 ≤ K) :
    ((R.withDensity (fun y => ENNReal.ofReal (Real.exp
      (I y - Real.log (gibbsPartition β (physical n (Y y).2)))))).restrict E).map Y ≤
      ENNReal.ofReal (Real.exp K) •
        ((primitiveJointGibbsLaw n β (1 / Real.sqrt (2*(n : ℝ)))).map Prod.swap) := by
  apply enlargedReference_gibbs_restricted_endpoint_domination n β R Y hY hR _
    (fun _ => Real.exp_pos _) E hE K
  intro y hy
  simp only [proposalGibbsLogRatio, Real.log_exp]
  have h := hbound y hy
  change I y - (n : ℝ)*Real.log 2 -
    β * goeSpinHamiltonian (1 / Real.sqrt (2*(n : ℝ))) (Y y).1 (Y y).2 ≤ K at h
  dsimp only [physical]
  linarith

theorem intrinsic_restricted_endpoint_domination {A : Type*} [MeasurableSpace A]
    (n : ℕ) (β K : ℝ) (μ : Measure A) (I : A → ℝ) (hI : AEMeasurable I μ)
    (Y : A → Spin n × Prim n) (hY : Measurable Y)
    (hR : (μ.withDensity (fun y => ENNReal.ofReal (Real.exp (-I y)))).map Y =
      unlinkedPrimitiveSpinFirstLaw n)
    (E : Set A) (hE : MeasurableSet E)
    (hbound : ∀ y ∈ E, I y - (n : ℝ)*Real.log 2 -
      β * goeSpinHamiltonian (1 / Real.sqrt (2*(n : ℝ))) (Y y).1 (Y y).2 ≤ K) :
    (μ.restrict E).map Y ≤ (unlinkedPrimitiveSpinFirstLaw n).withDensity
      (fun z => ENNReal.ofReal (intrinsicDensity n β K z)) := by
  let R := μ.withDensity (fun y => ENNReal.ofReal (Real.exp (-I y)))
  have h := positive_density_restrict_le_exp_logratio R (fun y => Real.exp (I y))
    (fun y => intrinsicDensity n β K (Y y))
    ((measurable_intrinsicDensity n β K).comp hY)
    (fun _ => Real.exp_pos _) (fun _ => Real.exp_pos _) E hE 0 (by
      intro y hy
      simp only [intrinsicDensity, Real.log_exp]
      linarith [hbound y hy])
  simp only [Real.exp_zero, ENNReal.ofReal_one, one_smul] at h
  rw [exponential_reference_recover μ I hI] at h
  have hm := Measure.map_mono h hY
  have he := map_withDensity_comp R Y hY
    (fun z => ENNReal.ofReal (intrinsicDensity n β K z))
      (measurable_intrinsicDensity n β K).ennreal_ofReal
  change ((R.withDensity (fun y => ENNReal.ofReal (intrinsicDensity n β K (Y y)))).map Y) = _ at he
  rw [he, hR] at hm
  exact hm

end SKConstants.Completion.N13A
