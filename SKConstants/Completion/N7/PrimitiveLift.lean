module

public import SKConstants.GaussianPrimitiveGibbsLift

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory

namespace SKConstants.Completion.N7
open GaussianProposal

theorem lift_randomized_output
    {X A N Z S : Type*} [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace N]
    [MeasurableSpace Z] [MeasurableSpace S]
    (μ : Measure X) (ν : Measure A) (η : Measure N) (γ : Measure Z)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure η]
    (L : X × N → Z) (hL : Measurable L) (g : Z → X) (hg : Measurable g)
    (hlaw : (μ.prod η).map L = γ) (hinv : ∀ᵐ x ∂μ, ∀ b, g (L (x, b)) = x)
    (F : X × A → S) (hF : Measurable F) :
    ((((μ.prod ν).map (fun p => (p.1, F p))).prod η).map
      (fun p => (L (p.1.1, p.2), p.1.2))) =
      (γ.prod ν).map (fun p => (p.1, F (g p.1, p.2))) := by
  let shuffle : (X × A) × N → (X × N) × A := fun p => ((p.1.1, p.2), p.1.2)
  have hs : MeasurePreserving shuffle ((μ.prod ν).prod η) ((μ.prod η).prod ν) :=
    ((measurePreserving_prodAssoc μ η ν).symm).comp
      (((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := η))).comp
        (measurePreserving_prodAssoc μ ν η))
  have hIn : Measurable (fun p : X × A => (p.1, F p)) := measurable_fst.prodMk hF
  have hOut : Measurable (fun p : (X × S) × N => (L (p.1.1, p.2), p.1.2)) :=
    (hL.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd
  have hK : Measurable (fun p : (X × N) × A => (L p.1, F (p.1.1, p.2))) :=
    (hL.comp measurable_fst).prodMk (hF.comp (measurable_fst.fst.prodMk measurable_snd))
  have hH : Measurable (fun p : Z × A => (p.1, F (g p.1, p.2))) :=
    measurable_fst.prodMk (hF.comp ((hg.comp measurable_fst).prodMk measurable_snd))
  have hinv' : ∀ᵐ p ∂(μ.prod η).prod ν, g (L p.1) = p.1.1 := by
    have hi := ((measurePreserving_fst (μ := μ) (ν := η)).comp
      (measurePreserving_fst (μ := μ.prod η) (ν := ν))).quasiMeasurePreserving.ae hinv
    exact hi.mono (fun p hp => hp p.1.2)
  have hprod : (((μ.prod ν).map (fun p => (p.1, F p))).prod η) =
      ((μ.prod ν).prod η).map (Prod.map (fun p => (p.1, F p)) id) := by
    simpa only [Measure.map_id] using Measure.map_prod_map (μ.prod ν) η hIn measurable_id
  rw [hprod, Measure.map_map hOut (hIn.prodMap measurable_id)]
  change ((μ.prod ν).prod η).map ((fun p => (L p.1, F (p.1.1, p.2))) ∘ shuffle) = _
  rw [← Measure.map_map hK hs.measurable, hs.map_eq]
  calc
    _ = ((μ.prod η).prod ν).map ((fun p => (p.1, F (g p.1, p.2))) ∘ Prod.map L id) := by
      apply Measure.map_congr
      filter_upwards [hinv'] with p hp
      change (L p.1, F (p.1.1, p.2)) = (L p.1, F (g (L p.1), p.2))
      rw [hp]
    _ = _ := by
      rw [← Measure.map_map hH (hL.prodMap measurable_id),
        ← Measure.map_prod_map (μ.prod η) ν hL measurable_id, Measure.map_id, hlaw]

theorem primitiveLiftJointLaw_randomized_output
    {A : Type*} [MeasurableSpace A] (n : ℕ) (σ : ℝ) (hσ : σ ≠ 0)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (F : Matrix (Fin n) (Fin n) ℝ × A → Spin n) (hF : Measurable F) :
    primitiveLiftJointLaw n σ
      (((primitiveGaussian (Fin n × Fin n)).map (goeMatrix σ)).prod ν |>.map
        (fun p => (p.1, F p))) =
      ((primitiveGaussian (Fin n × Fin n)).prod ν).map
        (fun p => (p.1, F (goeMatrix σ p.1, p.2))) := by
  let μ := (primitiveGaussian (Fin n × Fin n)).map (goeMatrix σ)
  have hsym : ∀ᵐ G ∂μ, G.IsSymm := by
    have hs : MeasurableSet {G : Matrix (Fin n) (Fin n) ℝ | G.IsSymm} := by
      change MeasurableSet {G : Matrix (Fin n) (Fin n) ℝ | G.transpose = G}
      exact (isClosed_eq (by fun_prop) continuous_id).measurableSet
    exact (ae_map_iff (continuous_goeMatrix σ).measurable.aemeasurable hs).mpr
      (Filter.Eventually.of_forall (goeMatrix_symmetric σ))
  exact lift_randomized_output μ ν (primitiveGaussian (Fin n × Fin n))
    (primitiveGaussian (Fin n × Fin n)) (Function.uncurry (primitiveLift σ))
    (measurable_primitiveLift σ) (goeMatrix σ) (continuous_goeMatrix σ).measurable
    (primitiveLift_goe_law σ hσ)
    (hsym.mono (fun G hG => goeMatrix_primitiveLift σ hσ G hG)) F hF

theorem randomizedPrimitiveProposal_KL_le
    {A : Type*} [MeasurableSpace A] (n : ℕ) (β σ : ℝ) (hσ : σ ≠ 0)
    (ν : Measure A) [IsProbabilityMeasure ν]
    (F : Matrix (Fin n) (Fin n) ℝ × A → Spin n) (hF : Measurable F) :
    InformationTheory.klDiv (((primitiveGaussian (Fin n × Fin n)).prod ν).map
        (fun p => (F (goeMatrix σ p.1, p.2), p.1)))
      ((primitiveJointGibbsLaw n β σ).map Prod.swap) ≤
      InformationTheory.klDiv
        ((((primitiveGaussian (Fin n × Fin n)).map (goeMatrix σ)).prod ν).map
          (fun p => (p.1, F p))) (physicalJointGibbsLaw n β σ) := by
  have h := primitiveLiftJointLaw_spinFirst_KL_le n β σ hσ
    ((((primitiveGaussian (Fin n × Fin n)).map (goeMatrix σ)).prod ν).map
      (fun p => (p.1, F p)))
  have hOut : Measurable (fun p : EuclideanSpace ℝ (Fin n × Fin n) × A =>
      (p.1, F (goeMatrix σ p.1, p.2))) :=
    measurable_fst.prodMk (hF.comp
      (((continuous_goeMatrix σ).measurable.comp measurable_fst).prodMk measurable_snd))
  rw [primitiveLiftJointLaw_randomized_output n σ hσ ν F hF,
    Measure.map_map measurable_swap hOut] at h
  exact h

end SKConstants.Completion.N7
