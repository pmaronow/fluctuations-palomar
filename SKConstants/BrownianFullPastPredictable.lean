module
public import SKConstants.PredictableGaussianSums
public import SKConstants.GaussianTwoDriverBrownian

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology
namespace SKConstants

lemma indepFun_static_prod_left
    {A Ω E F : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {f : Ω → E} {g : Ω → F} (hf : AEMeasurable f Q) (hg : AEMeasurable g Q)
    (hi : IndepFun f g Q) :
    IndepFun (fun u : A × Ω => (u.1, f u.2)) (fun u : A × Ω => g u.2) (P.prod Q) := by
  have hfg : HasLaw (fun ω => (f ω,g ω)) ((Q.map f).prod (Q.map g)) Q :=
    hi.hasLaw_prod ⟨hf,rfl⟩ ⟨hg,rfl⟩
  have hfst : HasLaw (Prod.fst : A × Ω → A) P (P.prod Q) :=
    ⟨measurable_fst.aemeasurable,measurePreserving_fst.map_eq⟩
  have hsnd : HasLaw (Prod.snd : A × Ω → Ω) Q (P.prod Q) :=
    ⟨measurable_snd.aemeasurable,measurePreserving_snd.map_eq⟩
  have hj := (indepFun_prod₀ (μ := P) (ν := Q) aemeasurable_id hfg.aemeasurable).hasLaw_prod
    hfst (hfg.comp hsnd)
  have hm := (measurePreserving_prodAssoc P (Q.map f) (Q.map g)).symm
    MeasurableEquiv.prodAssoc
  have hassoc : HasLaw (fun p : A × (E × F) => ((p.1,p.2.1),p.2.2))
      ((P.prod (Q.map f)).prod (Q.map g)) (P.prod ((Q.map f).prod (Q.map g))) :=
    ⟨hm.measurable.aemeasurable,hm.map_eq⟩
  have hwhole : HasLaw (fun u : A × Ω => ((u.1,f u.2),g u.2))
      ((P.prod (Q.map f)).prod (Q.map g)) (P.prod Q) := hassoc.comp hj
  have hleft : HasLaw (fun u : A × Ω => (u.1,f u.2))
      (P.prod (Q.map f)) (P.prod Q) :=
    (indepFun_prod₀ (μ := P) (ν := Q) aemeasurable_id hf).hasLaw_prod hfst
      ((show HasLaw f (Q.map f) Q from ⟨hf,rfl⟩).comp hsnd)
  have hright : HasLaw (fun u : A × Ω => g u.2) (Q.map g) (P.prod Q) :=
    (show HasLaw g (Q.map g) Q from ⟨hg,rfl⟩).comp hsnd
  exact (indepFun_iff_hasLaw_prodMk_prod hleft hright).2 hwhole

def brownianFullPast {Ω : Type*} (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (ω : Ω) : Iic T → ℝ := fun s => D s ω

def brownianPastRestrict {s T : ℝ≥0} (hs : s ≤ T)
    (w : Iic T → ℝ) : Iic s → ℝ := fun t => w ⟨t,t.property.trans hs⟩

lemma measurable_brownianPastRestrict {s T : ℝ≥0} (hs : s ≤ T) :
    Measurable (brownianPastRestrict hs) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

lemma brownianPastRestrict_fullPast {Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    {s T : ℝ≥0} (hs : s ≤ T) (ω : Ω) :
    brownianPastRestrict hs (brownianFullPast D T ω) = brownianFullPast D s ω := rfl

abbrev BrownianStaticPredictableCoefficient (A : Type*) (t : ℕ → ℝ≥0) :=
  (k : ℕ) → A × (Iic (t k) → ℝ) → ℝ

def brownianStaticCoefficient {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianStaticPredictableCoefficient A t) (k : ℕ)
    (u : A × Ω) : ℝ := H k (u.1,brownianFullPast D (t k) u.2)

def brownianStaticPredictableSum {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianStaticPredictableCoefficient A t) :=
  predictableGaussianSum (fun k u => brownianMeshIncrement D t k u.2)
    (brownianStaticCoefficient D t H)

def brownianStaticPredictableVariation {A Ω : Type*} (D : ℝ≥0 → Ω → ℝ)
    (t : ℕ → ℝ≥0) (H : BrownianStaticPredictableCoefficient A t) :=
  predictableGaussianVariation (brownianMeshVariance t) (brownianStaticCoefficient D t H)

def brownianStaticPastSum {A : Type*} (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : BrownianStaticPredictableCoefficient A t) (n : ℕ)
    (u : A × (Iic (t n) → ℝ)) : ℝ :=
  ∑ i : Fin n, H i (u.1,brownianPastRestrict (ht (Nat.le_of_lt i.isLt)) u.2) *
    (u.2 ⟨t (i+1),ht (by omega)⟩ - u.2 ⟨t i,ht (Nat.le_of_lt i.isLt)⟩)

def brownianStaticPastVariation {A : Type*} (t : ℕ → ℝ≥0) (ht : Monotone t)
    (H : BrownianStaticPredictableCoefficient A t) (n : ℕ)
    (u : A × (Iic (t n) → ℝ)) : ℝ :=
  ∑ i : Fin n, H i (u.1,brownianPastRestrict (ht (Nat.le_of_lt i.isLt)) u.2) ^ 2 *
    (brownianMeshVariance t i : ℝ)

lemma measurable_brownianStaticPastSum {A : Type*} [MeasurableSpace A]
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (brownianStaticPastSum t ht H n) := by
  apply Finset.measurable_sum
  intro i _
  exact ((hH i).comp (measurable_fst.prodMk
    ((measurable_brownianPastRestrict _).comp measurable_snd))).mul
    (((measurable_pi_apply _).comp measurable_snd).sub
      ((measurable_pi_apply _).comp measurable_snd))

lemma measurable_brownianStaticPastVariation {A : Type*} [MeasurableSpace A]
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    Measurable (brownianStaticPastVariation t ht H n) := by
  apply Finset.measurable_sum
  intro i _
  exact (((hH i).comp (measurable_fst.prodMk
    ((measurable_brownianPastRestrict _).comp measurable_snd))).pow_const 2).mul_const _

lemma aemeasurable_brownianStaticCoefficient {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (k : ℕ) :
    AEMeasurable (brownianStaticCoefficient D t H k) (P.prod Q) := by
  apply (hH k).comp_aemeasurable
  exact measurable_fst.aemeasurable.prodMk
    ((Measurable.of_eval (fun s : Iic (t k) => hmD s)).comp measurable_snd).aemeasurable

lemma brownianStaticPredictable_state_indep_increment {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (n : ℕ) :
    IndepFun (fun u => (brownianStaticPredictableSum D t H n u,
      brownianStaticCoefficient D t H n u,brownianStaticPredictableVariation D t H n u))
      (fun u : A × Ω => brownianMeshIncrement D t n u.2) (P.prod Q) := by
  have hi : IndepFun (brownianFullPast D (t n)) (brownianMeshIncrement D t n) Q := by
    have he : t n + brownianMeshVariance t n = t (n+1) :=
      add_tsub_cancel_of_le (ht (by omega))
    change IndepFun (fun ω (s : Iic (t n)) => D s ω)
      (fun ω => D (t (n+1)) ω - D (t n) ω) Q
    simpa only [Function.comp_def,Function.id_def,he] using
      ((hD.indepFun_shift (t n)).comp (φ := fun f : ℝ≥0 → ℝ => f (brownianMeshVariance t n))
        (ψ := id) (measurable_pi_apply _) measurable_id).symm
  have hj := indepFun_static_prod_left P Q
    (show AEMeasurable (brownianFullPast D (t n)) Q from
      (Measurable.of_eval (fun s : Iic (t n) => hmD s)).aemeasurable)
    ((hD.aemeasurable _).sub (hD.aemeasurable _)) hi
  let Φ := fun u : A × (Iic (t n) → ℝ) =>
    (brownianStaticPastSum t ht H n u,H n u,brownianStaticPastVariation t ht H n u)
  have hΦ : Measurable Φ := (measurable_brownianStaticPastSum t ht H hH n).prodMk
    ((hH n).prodMk (measurable_brownianStaticPastVariation t ht H hH n))
  convert hj.comp hΦ measurable_id using 1
  · funext u
    rw [brownianStaticPredictableSum,predictableGaussianSum_eq_fin_sum,
      brownianStaticPredictableVariation,predictableGaussianVariation_eq_fin_sum]
    rfl
  · rfl

theorem brownianStaticPredictableExponential_integral {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k)) (θ : ℝ) (n : ℕ) :
    Integrable (predictableGaussianExponential (fun k u => brownianMeshIncrement D t k u.2)
      (brownianStaticCoefficient D t H) (brownianMeshVariance t) θ n) (P.prod Q) ∧
    (∫ u, predictableGaussianExponential (fun k u => brownianMeshIncrement D t k u.2)
      (brownianStaticCoefficient D t H) (brownianMeshVariance t) θ n u ∂P.prod Q) = 1 := by
  have hsnd : HasLaw (Prod.snd : A × Ω → Ω) Q (P.prod Q) :=
    ⟨measurable_snd.aemeasurable,measurePreserving_snd.map_eq⟩
  exact predictableGaussianExponential_integral (P.prod Q) _ _ _
    (fun k => (brownianMeshIncrement_hasLaw hD t ht k).comp hsnd)
    (aemeasurable_brownianStaticCoefficient P Q D hD hmD t H hH)
    (brownianStaticPredictable_state_indep_increment P Q D hD hmD t ht H hH) θ n

theorem brownianStaticPredictableSum_L2_isometry {A Ω : Type*}
    [MeasurableSpace A] [MeasurableSpace Ω]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (D : ℝ≥0 → Ω → ℝ) (hD : IsPreBrownianReal D Q) (hmD : ∀ s, Measurable (D s))
    (t : ℕ → ℝ≥0) (ht : Monotone t) (H : BrownianStaticPredictableCoefficient A t)
    (hH : ∀ k, Measurable (H k))
    (hHsq : ∀ k, Integrable (fun u => brownianStaticCoefficient D t H k u ^ 2) (P.prod Q))
    (n : ℕ) :
    Integrable (fun u => brownianStaticPredictableSum D t H n u ^ 2) (P.prod Q) ∧
    Integrable (brownianStaticPredictableVariation D t H n) (P.prod Q) ∧
    (∫ u, brownianStaticPredictableSum D t H n u ^ 2 ∂P.prod Q) =
      ∫ u, brownianStaticPredictableVariation D t H n u ∂P.prod Q := by
  have hsnd : HasLaw (Prod.snd : A × Ω → Ω) Q (P.prod Q) :=
    ⟨measurable_snd.aemeasurable,measurePreserving_snd.map_eq⟩
  exact predictableGaussianSum_L2_isometry (P.prod Q) _ _ _
    (fun k => (brownianMeshIncrement_hasLaw hD t ht k).comp hsnd)
    (aemeasurable_brownianStaticCoefficient P Q D hD hmD t H hH) hHsq
    (brownianStaticPredictable_state_indep_increment P Q D hD hmD t ht H hH) n

end SKConstants
