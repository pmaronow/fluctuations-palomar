module

public import CavityStarCentering

@[expose] public section

noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations
open Hierarchy

def physicalStarPairMoment (n l : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {P : Type} [MeasurableSpace P]
    (μ : Measure P) (x : P → FeatureIndex n → ℝ) (hx : Measurable x)
    (fork : ℕ) (S : ℝ) : ℝ :=
  ∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
    (fun z => |orderedOverlap n (ForwardPath.spin steps.length z.1.2)
      (ForwardPath.spin steps.length z.2.2)-S|^(2*l)) p ∂physicalPathLaw μ n steps x hx

theorem physicalStarPairMoment_le_finite_ledger (n l : ℕ) (hl : 0 < l)
    (steps : List (GaussianStep (FeatureIndex n))) {c : ℝ} (hc : OrderedSteps c steps)
    {P : Type} [MeasurableSpace P] (μ : Measure P) [IsFiniteMeasure μ]
    (x : P → FeatureIndex n → ℝ) (hx : Measurable x) (fork t : ℕ) (S : ℝ) :
    physicalStarPairMoment n l steps μ x hx fork S ≤ (3:ℝ)^(2*l-1)*
      (physicalOverlapProjectionErrorMoment n l steps μ x hx fork t +
        (∫ p, conditionalForkTest (uniformWeight n) (finiteFeature n) steps x fork
          (fun z => |physicalCentralPairError n steps x fork t z|^(2*l)) p
            ∂physicalPathLaw μ n steps x hx) +
        (∫ p, |‖actualSpinPath n steps x fork p‖^2-S|^(2*l)
          ∂physicalPathLaw μ n steps x hx)) := by
  let Ω := PhysicalPathState P n steps
  let F : Fin 3 → Ω × Ω → ℝ := ![
    physicalOverlapProjectionError n steps x t,
    physicalCentralPairError n steps x fork t,
    fun z => ‖actualSpinPath n steps x fork z.1‖^2-S]
  have htM := actualSpinPath_measurable n steps hc x hx t
  have hfM := actualSpinPath_measurable n steps hc x hx fork
  have hover : Measurable (fun z : Ω × Ω => orderedOverlap n
      (ForwardPath.spin steps.length z.1.2) (ForwardPath.spin steps.length z.2.2)) := by
    exact (measurable_of_finite (f := fun p : Spin n × Spin n => orderedOverlap n p.1 p.2)).comp
      (((ForwardPath.spin_measurable steps.length).comp (measurable_snd.comp measurable_fst)).prodMk
        ((ForwardPath.spin_measurable steps.length).comp (measurable_snd.comp measurable_snd)))
  have hF i : Measurable (F i) := by
    fin_cases i
    · exact hover.sub ((htM.comp measurable_fst).inner (htM.comp measurable_snd))
    · exact ((htM.comp measurable_fst).inner (htM.comp measurable_snd)).sub
        ((hfM.comp measurable_fst).norm.pow_const 2)
    · exact ((hfM.comp measurable_fst).norm.pow_const 2).sub_const S
  have hcore (u : ℕ) (z : Ω × Ω) : |inner ℝ (actualSpinPath n steps x u z.1)
      (actualSpinPath n steps x u z.2)| ≤ 1 := by
    have hi := norm_inner_le_norm (𝕜:=ℝ) (actualSpinPath n steps x u z.1)
      (actualSpinPath n steps x u z.2)
    rw [Real.norm_eq_abs] at hi
    apply hi.trans
    exact (mul_le_mul (actualSpinPath_norm_le n steps hc x u z.1)
      (actualSpinPath_norm_le n steps hc x u z.2) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have hFbound (i : Fin 3) (z : Ω × Ω) : |F i z| ≤ 2+|S| := by
    fin_cases i
    · apply (abs_sub _ _).trans
      have h1 := orderedOverlap_abs_le_one n (ForwardPath.spin steps.length z.1.2)
        (ForwardPath.spin steps.length z.2.2)
      have h2 := hcore t z
      linarith [abs_nonneg S]
    · change |inner ℝ (actualSpinPath n steps x t z.1) (actualSpinPath n steps x t z.2)-
        ‖actualSpinPath n steps x fork z.1‖^2| ≤ _
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg (sq_nonneg ‖actualSpinPath n steps x fork z.1‖)]
      have h1 := hcore t z
      have h2 := actualSpinPath_norm_le n steps hc x fork z.1
      nlinarith [norm_nonneg (actualSpinPath n steps x fork z.1),abs_nonneg S]
    · change |‖actualSpinPath n steps x fork z.1‖^2-S| ≤ _
      apply (abs_sub _ _).trans
      rw [abs_of_nonneg (sq_nonneg ‖actualSpinPath n steps x fork z.1‖)]
      have h2 := actualSpinPath_norm_le n steps hc x fork z.1
      nlinarith [norm_nonneg (actualSpinPath n steps x fork z.1)]
  have hsum (z : Ω × Ω) : (∑ i : Fin 3, F i z) = orderedOverlap n
      (ForwardPath.spin steps.length z.1.2) (ForwardPath.spin steps.length z.2.2)-S := by
    simp [Fin.sum_univ_three,F,physicalOverlapProjectionError,physicalCentralPairError]
  have H := fork_sum_power_le (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork
    Finset.univ F hF hFbound (2*l) (by omega)
  simp only [hsum] at H
  simp [F,Fin.sum_univ_three] at H
  rw [integral_conditionalForkTest_fst (uniformWeight_pos n) (finiteFeature n) steps hc μ x hx fork
    (fun p => |‖actualSpinPath n steps x fork p‖^2-S|^(2*l))] at H
  exact H

end OAI.SKFluctuations
