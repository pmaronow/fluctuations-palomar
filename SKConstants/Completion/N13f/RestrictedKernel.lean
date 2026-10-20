module

public import SKConstants.Completion.Blueprint.AssemblyCoarse
public import SKConstants.ProposalGibbsChangeOfMeasure
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators NNReal

namespace SKConstants.Completion.N13f
open GaussianProposal Blueprint

theorem restricted_endpoint_le_withDensity_of_log_bound
    {U V : Type*} [MeasurableSpace U] [MeasurableSpace V]
    (R : Measure U) (Y : U → V) (hY : Measurable Y)
    (f : U → ℝ) (hf : ∀ u, 0 < f u)
    (B : V → ℝ) (hB : Measurable B) (hBpos : ∀ v, 0 < B v)
    (S : Set U) (hS : MeasurableSet S)
    (hbound : ∀ u ∈ S, Real.log (f u) ≤ Real.log (B (Y u))) :
    ((R.withDensity (fun u => ENNReal.ofReal (f u))).restrict S).map Y ≤
      (R.map Y).withDensity (fun v => ENNReal.ofReal (B v)) := by
  have h := positive_density_restrict_le_exp_logratio R f (B ∘ Y) (hB.comp hY)
    hf (fun u => hBpos (Y u)) S hS 0 (fun u hu => sub_nonpos.mpr (hbound u hu))
  simp only [Real.exp_zero, ENNReal.ofReal_one, one_smul] at h
  have hm := Measure.map_mono h hY
  change _ ≤ (R.withDensity ((fun v => ENNReal.ofReal (B v)) ∘ Y)).map Y at hm
  rw [map_withDensity_comp R Y hY _ hB.ennreal_ofReal] at hm
  exact hm

def intrinsicReferenceWeight (n : ℕ) (β P L : ℝ) (v : Spin n × Prim n) : ℝ :=
  (2 : ℝ)^n * Real.exp (-(n : ℝ)*P + L +
    β * goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) v.1 v.2)

theorem measurable_intrinsicReferenceWeight (n : ℕ) (β P L : ℝ) :
    Measurable (intrinsicReferenceWeight n β P L) := by
  apply measurable_from_prod_countable_right
  intro x
  have hm := measurable_dominationBound β n L x
  have he : (fun g => intrinsicReferenceWeight n β P L (x,g)) =
      fun g => (2 : ℝ)^n * Real.exp ((n : ℝ)*(parisiPressure β-P)) *
        dominationBound β n L g x := by
    funext g
    unfold intrinsicReferenceWeight dominationBound
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [he]
  exact hm.const_mul _

theorem intrinsicReference_fiber (n : ℕ) (β P L : ℝ)
    (x : Spin n) (A : Set (Prim n)) (hA : MeasurableSet A) :
    ((unlinkedPrimitiveSpinFirstLaw n).withDensity
      (fun v => ENNReal.ofReal (intrinsicReferenceWeight n β P L v))) ({x} ×ˢ A) =
      ∫⁻ g in A, ENNReal.ofReal (Real.exp (-(n : ℝ)*P + L +
        β * goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x g)) ∂primLaw n := by
  classical
  rw [withDensity_apply _ ((measurableSet_singleton x).prod hA)]
  change (∫⁻ v in {x} ×ˢ A, ENNReal.ofReal (intrinsicReferenceWeight n β P L v)
    ∂(uniformSpinLaw n).prod (primLaw n)) = _
  rw [← Measure.prod_restrict]
  rw [lintegral_prod _ (measurable_intrinsicReferenceWeight n β P L).ennreal_ofReal.aemeasurable]
  rw [lintegral_singleton]
  have hx : uniformSpinLaw n {x} = ENNReal.ofReal (1/(2 : ℝ)^n) := by
    simp [uniformSpinLaw, finiteWeightMeasure_apply _ _ (measurableSet_singleton x)]
  rw [hx]
  unfold intrinsicReferenceWeight
  simp_rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ)^n)]
  have hm : Measurable (fun g : Prim n => Real.exp (-(n : ℝ)*P+L+
      β*goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) x g)) := by
    convert measurable_dominationBound β n (L+(n : ℝ)*(parisiPressure β-P)) x using 1
    funext g
    unfold dominationBound
    congr 1
    ring
  rw [lintegral_const_mul _ hm.ennreal_ofReal, mul_right_comm,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ)^n)]
  simp

theorem enlargedReference_intrinsic_restricted_endpoint_domination
    {U : Type*} [MeasurableSpace U]
    (n : ℕ) (β P L : ℝ) (R : Measure U)
    (Y : U → Spin n × Prim n) (hY : Measurable Y)
    (hR : R.map Y = unlinkedPrimitiveSpinFirstLaw n)
    (f : U → ℝ) (hf : ∀ u, 0 < f u)
    (S : Set U) (hS : MeasurableSet S)
    (hbound : ∀ u ∈ S, Real.log (f u) - (n : ℝ)*Real.log 2 -
      β * goeSpinHamiltonian (1/Real.sqrt (2*(n : ℝ))) (Y u).1 (Y u).2 ≤ -(n : ℝ)*P + L) :
    ((R.withDensity (fun u => ENNReal.ofReal (f u))).restrict S).map Y ≤
      (unlinkedPrimitiveSpinFirstLaw n).withDensity
        (fun v => ENNReal.ofReal (intrinsicReferenceWeight n β P L v)) := by
  rw [← hR]
  apply restricted_endpoint_le_withDensity_of_log_bound R Y hY f hf _
    (measurable_intrinsicReferenceWeight n β P L) (fun v => by
      unfold intrinsicReferenceWeight
      positivity) S hS
  intro u hu
  rw [intrinsicReferenceWeight, Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_pow, Real.log_exp]
  linarith [hbound u hu]

theorem restricted_sampler_kernel_le
    {G U X : Type*} [MeasurableSpace G] [MeasurableSpace U]
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X]
    (μ : Measure G) [SigmaFinite μ] (ν : Measure U) [IsFiniteMeasure ν]
    (F : G × U → X) (hF : Measurable F) (E : Set (G × U)) (hE : MeasurableSet E)
    (B : G → X → ℝ)
    (hB0 : ∀ g x, 0 ≤ B g x)
    (hdom : ∀ x A, MeasurableSet A →
      (((μ.prod ν).restrict E).map (fun u => (F u,u.1))) ({x} ×ˢ A) ≤
        ∫⁻ g in A, ENNReal.ofReal (B g x) ∂μ) :
    ∀ᵐ g ∂μ, ∀ x, ν.real {u | (g,u) ∈ E ∧ F (g,u) = x} ≤ B g x := by
  have hall (x : X) : ∀ᵐ g ∂μ, ν.real {u | (g,u) ∈ E ∧ F (g,u) = x} ≤ B g x := by
    have hs : MeasurableSet {u : G × U | u ∈ E ∧ F u = x} :=
      hE.inter (hF (measurableSet_singleton x))
    have hm : Measurable (fun g => ν {u | (g,u) ∈ E ∧ F (g,u) = x}) :=
      measurable_measure_prodMk_left hs
    have hle : (fun g => ν {u | (g,u) ∈ E ∧ F (g,u) = x}) ≤ᵐ[μ]
        (fun g => ENNReal.ofReal (B g x)) := by
      apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hm.aemeasurable
      intro A hA _
      have hd := hdom x A hA
      rw [Measure.map_apply (hF.prodMk measurable_fst)
        ((measurableSet_singleton x).prod hA), Measure.restrict_apply
        ((hF.prodMk measurable_fst) ((measurableSet_singleton x).prod hA))] at hd
      have he : ((fun u : G × U => (F u,u.1)) ⁻¹' ({x} ×ˢ A)) ∩ E =
          (A ×ˢ univ) ∩ {u : G × U | u ∈ E ∧ F u = x} := by
        ext u
        simp only [mem_inter_iff, mem_preimage, mem_prod, mem_singleton_iff,
          mem_univ, and_true, mem_ofPred_eq]
        tauto
      rw [he, inter_comm, ← Measure.restrict_apply hs, ← Measure.restrict_prod_eq_prod_univ,
        Measure.prod_apply hs] at hd
      exact hd
    filter_upwards [hle] with g hg
    simpa only [Measure.real, ENNReal.toReal_ofReal (hB0 g x)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hg
  exact ae_all_iff.mpr hall

theorem blueprint_restrictedKernel_le_of_endpoint_domination
    {Ω : Type*} [MeasurableSpace Ω]
    (W : SKConstantsOAI.ZeroTemperatureSK.BrownianSystem Ω) (β : ℝ) (hβ : 1 < β)
    (p : Parameters) (n : ℕ) (E : Set (RunInput p n)) (hE : MeasurableSet E) (L : ℝ)
    (hdom : ((runLaw W p n).restrict E).map
        (fun u => (coarseSpin W β hβ p n u.1 u.2.1 u.2.2,u.1)) ≤
      (unlinkedPrimitiveSpinFirstLaw n).withDensity
        (fun v => ENNReal.ofReal (intrinsicReferenceWeight n β (parisiPressure β) L v))) :
    ∀ᵐ g ∂primLaw n, ∀ x : Spin n,
      restrictedKernel W β hβ p n E g x ≤ dominationBound β n L g x := by
  apply restricted_sampler_kernel_le (primLaw n) ((fineAuxLaw W p n).prod (thresholdLaw n))
    (fun u => coarseSpin W β hβ p n u.1 u.2.1 u.2.2)
    (measurable_runSpin W β hβ p n (readoutTime p.a p.b n)) E hE
    (fun g x => dominationBound β n L g x)
    (fun _ _ => (Real.exp_pos _).le)
  intro x A hA
  exact (hdom _).trans_eq (intrinsicReference_fiber n β (parisiPressure β) L x A hA)

end SKConstants.Completion.N13f
