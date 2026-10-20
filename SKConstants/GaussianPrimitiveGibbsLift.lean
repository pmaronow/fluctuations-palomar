module

public import SKConstants.GaussianPrimitiveLift
public import SKConstants.ConditionalGibbsDisintegration
public import SKConstants.GaussianEntropy

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal
set_option maxHeartbeats 800000

namespace SKConstants

lemma lift_compProd {X N Z S : Type*} [MeasurableSpace X] [MeasurableSpace N]
    [MeasurableSpace Z] [MeasurableSpace S]
    (μ : Measure X) (ν : Measure N) [SFinite μ] [SFinite ν]
    (κ : Kernel X S) [IsSFiniteKernel κ]
    (L : X × N → Z) (hL : Measurable L) (g : Z → X) (hg : Measurable g)
    (hinv : ∀ᵐ x ∂μ, ∀ a, g (L (x,a)) = x) :
    ((μ ⊗ₘ κ).prod ν).map (fun p => (L (p.1.1,p.2),p.1.2)) =
      ((μ.prod ν).map L) ⊗ₘ κ.comap g hg := by
  have hΦ : Measurable (fun p : (X × S) × N => (L (p.1.1,p.2),p.1.2)) :=
    (hL.comp (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd
  apply Measure.ext_of_lintegral
  intro f hf
  have hF : Measurable (fun p : (X × S) × N => f (L (p.1.1,p.2),p.1.2)) := hf.comp hΦ
  have hinner : Measurable (fun z : Z => ∫⁻ s, f (z,s) ∂κ (g z)) :=
    hf.lintegral_kernel_prod_right' (κ := κ.comap g hg)
  rw [lintegral_map hf hΦ, lintegral_prod _ hF.aemeasurable,
    Measure.lintegral_compProd hF.lintegral_prod_right',
    Measure.lintegral_compProd hf]
  simp only [Kernel.comap_apply]
  rw [lintegral_map hinner hL]
  change (∫⁻ x, ∫⁻ s, ∫⁻ a, f (L (x,a),s) ∂ν ∂κ x ∂μ) =
    ∫⁻ p, ((fun z : Z => ∫⁻ s, f (z,s) ∂κ (g z)) ∘ L) p ∂μ.prod ν
  rw [lintegral_prod _ (hinner.comp hL).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [hinv] with x hx
  have hxs : Measurable (fun p : S × N => f (L (x,p.2),p.1)) :=
    hf.comp ((hL.comp (measurable_const.prodMk measurable_snd)).prodMk measurable_fst)
  rw [lintegral_lintegral_swap hxs.aemeasurable]
  apply lintegral_congr
  intro a
  simp only [Function.comp_def, hx a]

namespace GaussianProposal

def physicalJointGibbsLaw (n : ℕ) (beta sigma : ℝ) :
    Measure (Matrix (Fin n) (Fin n) ℝ × Spin n) :=
  ((primitiveGaussian (Fin n × Fin n)).map (goeMatrix sigma)) ⊗ₘ gibbsKernel n beta

instance physicalJointGibbsLaw_isProbability (n : ℕ) (beta sigma : ℝ) :
    IsProbabilityMeasure (physicalJointGibbsLaw n beta sigma) := by
  unfold physicalJointGibbsLaw
  infer_instance

def primitiveLiftJointMap (n : ℕ) (sigma : ℝ) :
    (Matrix (Fin n) (Fin n) ℝ × Spin n) × EuclideanSpace ℝ (Fin n × Fin n) →
      EuclideanSpace ℝ (Fin n × Fin n) × Spin n :=
  fun p => (primitiveLift sigma p.1.1 p.2,p.1.2)

lemma measurable_primitiveLiftJointMap (n : ℕ) (sigma : ℝ) :
    Measurable (primitiveLiftJointMap n sigma) :=
  ((measurable_primitiveLift sigma).comp
    (measurable_fst.fst.prodMk measurable_snd)).prodMk measurable_fst.snd

def primitiveLiftJointLaw (n : ℕ) (sigma : ℝ)
    (Q : Measure (Matrix (Fin n) (Fin n) ℝ × Spin n)) :
    Measure (EuclideanSpace ℝ (Fin n × Fin n) × Spin n) :=
  (Q.prod (primitiveGaussian (Fin n × Fin n))).map (primitiveLiftJointMap n sigma)

instance primitiveLiftJointLaw_isProbability (n : ℕ) (sigma : ℝ)
    (Q : Measure (Matrix (Fin n) (Fin n) ℝ × Spin n)) [IsProbabilityMeasure Q] :
    IsProbabilityMeasure (primitiveLiftJointLaw n sigma Q) := by
  unfold primitiveLiftJointLaw
  exact Measure.isProbabilityMeasure_map_iff
    (measurable_primitiveLiftJointMap n sigma).aemeasurable |>.mpr inferInstance

theorem primitiveLiftJointLaw_spin (n : ℕ) (sigma : ℝ)
    (Q : Measure (Matrix (Fin n) (Fin n) ℝ × Spin n)) [SFinite Q] :
    (primitiveLiftJointLaw n sigma Q).snd = Q.snd := by
  unfold primitiveLiftJointLaw Measure.snd
  rw [Measure.map_map measurable_snd (measurable_primitiveLiftJointMap n sigma)]
  change (Q.prod (primitiveGaussian (Fin n × Fin n))).map (Prod.snd ∘ Prod.fst) = _
  rw [← Measure.map_map measurable_snd measurable_fst,
    Measure.map_fst_prod, measure_univ, one_smul]

theorem primitiveLiftJointLaw_gaussian (n : ℕ) (sigma : ℝ) (hsigma : sigma ≠ 0)
    (Q : Measure (Matrix (Fin n) (Fin n) ℝ × Spin n)) [SFinite Q]
    (hQ : Q.fst = (primitiveGaussian (Fin n × Fin n)).map (goeMatrix sigma)) :
    (primitiveLiftJointLaw n sigma Q).fst = primitiveGaussian (Fin n × Fin n) := by
  have hcoord : Measurable (fun p : (Matrix (Fin n) (Fin n) ℝ × Spin n) ×
      EuclideanSpace ℝ (Fin n × Fin n) => (p.1.1,p.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hm : (Q.prod (primitiveGaussian (Fin n × Fin n))).map
      (fun p => (p.1.1,p.2)) = Q.fst.prod (primitiveGaussian (Fin n × Fin n)) := by
    simpa only [Measure.fst, Measure.map_id, Prod.map_def, id_eq] using
      (Measure.map_prod_map Q (primitiveGaussian (Fin n × Fin n)) measurable_fst
        (measurable_id : Measurable (id : EuclideanSpace ℝ (Fin n × Fin n) → _))).symm
  unfold primitiveLiftJointLaw Measure.fst
  rw [Measure.map_map measurable_fst (measurable_primitiveLiftJointMap n sigma)]
  change (Q.prod (primitiveGaussian (Fin n × Fin n))).map
    ((Function.uncurry (primitiveLift sigma)) ∘ (fun p => (p.1.1,p.2))) = _
  rw [← Measure.map_map (measurable_primitiveLift sigma) hcoord, hm, hQ]
  exact primitiveLift_goe_law sigma hsigma

theorem primitiveLiftJointLaw_recovers_physical (n : ℕ) (sigma : ℝ) (hsigma : sigma ≠ 0)
    (Q : Measure (Matrix (Fin n) (Fin n) ℝ × Spin n)) [SFinite Q]
    (hQ : ∀ᵐ p ∂Q, p.1.IsSymm) :
    (primitiveLiftJointLaw n sigma Q).map (Prod.map (goeMatrix sigma) id) = Q := by
  have hg : Measurable (Prod.map (goeMatrix (ι := Fin n) sigma)
      (id : Spin n → Spin n)) := (continuous_goeMatrix sigma).measurable.prodMap measurable_id
  have hp : ∀ᵐ p ∂Q.prod (primitiveGaussian (Fin n × Fin n)), p.1.1.IsSymm :=
    ae_of_ae_map (μ := Q.prod (primitiveGaussian (Fin n × Fin n)))
      (f := Prod.fst) (p := fun p : Matrix (Fin n) (Fin n) ℝ × Spin n => p.1.IsSymm)
      measurable_fst.aemeasurable (by
      simpa only [Measure.map_fst_prod, measure_univ, one_smul] using hQ)
  unfold primitiveLiftJointLaw
  rw [Measure.map_map hg (measurable_primitiveLiftJointMap n sigma)]
  calc
    _ = (Q.prod (primitiveGaussian (Fin n × Fin n))).map Prod.fst := by
      apply Measure.map_congr
      filter_upwards [hp] with p hp
      exact Prod.ext (goeMatrix_primitiveLift sigma hsigma p.1.1 hp p.2) rfl
    _ = Q := by rw [Measure.map_fst_prod, measure_univ, one_smul]

theorem primitiveLiftJointLaw_recovers_physical_of_gaussian (n : ℕ)
    (sigma : ℝ) (hsigma : sigma ≠ 0)
    (Q : Measure (Matrix (Fin n) (Fin n) ℝ × Spin n)) [SFinite Q]
    (hQ : Q.fst = (primitiveGaussian (Fin n × Fin n)).map (goeMatrix sigma)) :
    (primitiveLiftJointLaw n sigma Q).map (Prod.map (goeMatrix sigma) id) = Q := by
  have hsym : ∀ᵐ W ∂Q.fst, W.IsSymm := by
    rw [hQ]
    have hs : MeasurableSet {W : Matrix (Fin n) (Fin n) ℝ | W.IsSymm} := by
      change MeasurableSet {W : Matrix (Fin n) (Fin n) ℝ | W.transpose=W}
      exact (isClosed_eq (by fun_prop) continuous_id).measurableSet
    exact (ae_map_iff (continuous_goeMatrix sigma).measurable.aemeasurable hs).mpr
      (Filter.Eventually.of_forall (goeMatrix_symmetric sigma))
  exact primitiveLiftJointLaw_recovers_physical n sigma hsigma Q
    (ae_of_ae_map (μ := Q) (f := Prod.fst) measurable_fst.aemeasurable hsym)

theorem primitiveLiftJointLaw_gibbs (n : ℕ) (beta sigma : ℝ) (hsigma : sigma ≠ 0) :
    primitiveLiftJointLaw n sigma (physicalJointGibbsLaw n beta sigma) =
      primitiveJointGibbsLaw n beta sigma := by
  have hinv : ∀ᵐ W ∂((primitiveGaussian (Fin n × Fin n)).map (goeMatrix sigma)),
      ∀ A, goeMatrix sigma (primitiveLift sigma W A)=W := by
    have hs : MeasurableSet {W : Matrix (Fin n) (Fin n) ℝ | W.IsSymm} := by
      change MeasurableSet {W : Matrix (Fin n) (Fin n) ℝ | W.transpose=W}
      exact (isClosed_eq (by fun_prop) continuous_id).measurableSet
    have hsym : ∀ᵐ W ∂((primitiveGaussian (Fin n × Fin n)).map (goeMatrix sigma)),
        W.IsSymm := (ae_map_iff (continuous_goeMatrix sigma).measurable.aemeasurable hs).mpr
      (Filter.Eventually.of_forall (goeMatrix_symmetric sigma))
    filter_upwards [hsym] with W hW
    exact fun A => goeMatrix_primitiveLift sigma hsigma W hW A
  unfold primitiveLiftJointLaw physicalJointGibbsLaw primitiveLiftJointMap
  have h := lift_compProd ((primitiveGaussian (Fin n × Fin n)).map (goeMatrix sigma))
    (primitiveGaussian (Fin n × Fin n)) (gibbsKernel n beta)
    (Function.uncurry (primitiveLift sigma)) (measurable_primitiveLift sigma)
    (goeMatrix sigma) (continuous_goeMatrix sigma).measurable hinv
  rw [primitiveLift_goe_law sigma hsigma] at h
  simpa only [Function.uncurry, primitiveJointGibbsLaw] using h

theorem primitiveJointGibbsLaw_physical_pushforward (n : ℕ) (beta sigma : ℝ)
    (hsigma : sigma ≠ 0) :
    (primitiveJointGibbsLaw n beta sigma).map (Prod.map (goeMatrix sigma) id) =
      physicalJointGibbsLaw n beta sigma := by
  rw [← primitiveLiftJointLaw_gibbs n beta sigma hsigma]
  apply primitiveLiftJointLaw_recovers_physical_of_gaussian n sigma hsigma
  exact Measure.fst_compProd _ _

theorem primitiveLiftJointLaw_KL_le (n : ℕ) (beta sigma : ℝ) (hsigma : sigma ≠ 0)
    (Q : Measure (Matrix (Fin n) (Fin n) ℝ × Spin n)) [IsProbabilityMeasure Q] :
    klDiv (primitiveLiftJointLaw n sigma Q) (primitiveJointGibbsLaw n beta sigma) ≤
      klDiv Q (physicalJointGibbsLaw n beta sigma) := by
  rw [← primitiveLiftJointLaw_gibbs n beta sigma hsigma]
  have h := klDiv_map_le (Q.prod (primitiveGaussian (Fin n × Fin n)))
    ((physicalJointGibbsLaw n beta sigma).prod (primitiveGaussian (Fin n × Fin n)))
    (measurable_primitiveLiftJointMap n sigma)
  simpa only [primitiveLiftJointLaw, klDiv_prod_add, klDiv_self, add_zero] using h

theorem primitiveLiftJointLaw_spinFirst_KL_le (n : ℕ) (beta sigma : ℝ)
    (hsigma : sigma ≠ 0)
    (Q : Measure (Matrix (Fin n) (Fin n) ℝ × Spin n)) [IsProbabilityMeasure Q] :
    klDiv ((primitiveLiftJointLaw n sigma Q).map Prod.swap)
      ((primitiveJointGibbsLaw n beta sigma).map Prod.swap) ≤
      klDiv Q (physicalJointGibbsLaw n beta sigma) :=
  (klDiv_map_le _ _ measurable_swap).trans
    (primitiveLiftJointLaw_KL_le n beta sigma hsigma Q)

end GaussianProposal
end SKConstants
