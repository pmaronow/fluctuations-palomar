module

public import CavityRestFiniteFeatureLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable
variable {S ι:Type*} [Fintype S] [Nonempty S] [Fintype ι]

def clockFeatureWeight (w:S→ℝ) (φ:S→(ι→ℝ)→L[ℝ]ℝ) :
    {as:List PositiveMass} → (T:ClockTree S as) → (ℕ→ι→ℝ≥0) → T.Assignment → (S→ℝ) → ℝ
  | _,.leaf,_,σ => fun x => spinWeight w (fun σ => ContinuousLinearMap.proj σ) x σ
  | _,@ClockTree.step _ a as T,q,σ => shiftedMean (featureLaw φ (q 0)) a.val
      (hamiltonianHierarchy w (featureSteps φ (clockSteps as (fun j => q (j+1)))))
      (clockFeatureWeight w φ T (fun j => q (j+1)) σ)
  | _,.fork T U,q,σ => fun x => clockFeatureWeight w φ T q σ.1 x*clockFeatureWeight w φ U q σ.2 x

theorem clockFeatureWeight_measurable (w:S→ℝ) (φ:S→(ι→ℝ)→L[ℝ]ℝ)
    {as:List PositiveMass} (T:ClockTree S as) (q:ℕ→ι→ℝ≥0) (σ:T.Assignment) :
    Measurable (clockFeatureWeight w φ T q σ) := by
  induction T generalizing q with
  | leaf =>
    change Measurable (fun x:S→ℝ => w σ*Real.exp (x σ)/(∑τ,w τ*Real.exp (x τ)))
    fun_prop
  | @step a as T ih =>
    change Measurable (fun x:S→ℝ =>
      (∫z,clockFeatureWeight w φ T (fun j=>q (j+1)) σ (x+z)*
        Real.exp (a.val*hamiltonianHierarchy w
          (featureSteps φ (clockSteps as (fun j=>q (j+1)))) (x+z)) ∂(featureLaw φ (q 0)))/
      (∫z,Real.exp (a.val*hamiltonianHierarchy w
        (featureSteps φ (clockSteps as (fun j=>q (j+1)))) (x+z)) ∂(featureLaw φ (q 0))))
    have hF:Measurable (fun p:(S→ℝ)×(S→ℝ)=>Real.exp (a.val*hamiltonianHierarchy w
        (featureSteps φ (clockSteps as (fun j=>q (j+1)))) (p.1+p.2))) :=
      (((hamiltonianHierarchy_measurable w _).comp (measurable_fst.add measurable_snd)).const_mul a.val).exp
    have hA:Measurable (fun p:(S→ℝ)×(S→ℝ)=>clockFeatureWeight w φ T
      (fun j=>q (j+1)) σ (p.1+p.2)) := (ih _ σ).comp (measurable_fst.add measurable_snd)
    exact (hA.mul hF).stronglyMeasurable.integral_prod_right'.measurable.div
      hF.stronglyMeasurable.integral_prod_right'.measurable
  | fork T U ihT ihU => exact (ihT q σ.1).mul (ihU q σ.2)

theorem ClockTree.weight_featureLaw (w:S→ℝ) (φ:S→(ι→ℝ)→L[ℝ]ℝ)
    {as:List PositiveMass} (T:ClockTree S as) (q:ℕ→ι→ℝ≥0) (σ:T.Assignment) (x:ι→ℝ) :
    T.weight w φ q σ x=clockFeatureWeight w φ T q σ (featureVector φ x) := by
  induction T generalizing q x with
  | leaf => rfl
  | @step a as T ih =>
    simp only [ClockTree.weight_step,clockFeatureWeight,shiftedMean,tiltedMean]
    simp_rw [ih,gaussianHierarchy_featureLaw,map_add]
    have hF:Measurable (fun z:S→ℝ=>Real.exp (a.val*hamiltonianHierarchy w
        (featureSteps φ (clockSteps as (fun j=>q (j+1)))) (featureVector φ x+z))) :=
      (((hamiltonianHierarchy_measurable w _).comp (measurable_const.add measurable_id)).const_mul a.val).exp
    have hA:Measurable (fun z:S→ℝ=>clockFeatureWeight w φ T (fun j=>q (j+1)) σ
        (featureVector φ x+z)) := (clockFeatureWeight_measurable w φ T _ σ).comp
          (measurable_const.add measurable_id)
    exact congrArg₂ (fun a b:ℝ=>a/b)
      (featureLaw_integral φ (q 0) _ (hA.mul hF)).symm
      (featureLaw_integral φ (q 0) _ hF).symm
  | fork T U ihT ihU => exact congrArg₂ (·*·) (ihT q σ.1 x) (ihU q σ.2 x)

theorem ClockTree.disorderWeight_featureLaw (w:S→ℝ) (φ:S→(ι→ℝ)→L[ℝ]ℝ)
    {as:List PositiveMass} (T:ClockTree S as) (l:ι→ℝ) (q:ℕ→ι→ℝ)
    (σ:T.Assignment) (x:ι→ℝ) :
    T.disorderWeight w φ l q σ x=
      ∫z,clockFeatureWeight w φ T (cumulativeIncrements (q 0) (fun j=>q (j+1))) σ
        (featureVector φ x+z) ∂(featureLaw φ (fun i=>(q 0 i-l i).toNNReal)) := by
  unfold ClockTree.disorderWeight
  simp_rw [ClockTree.weight_featureLaw,map_add]
  exact (featureLaw_integral φ _ _ ((clockFeatureWeight_measurable w φ T _ σ).comp
    (measurable_const.add measurable_id))).symm

end OAI.SKFluctuations.Hierarchy

namespace OAI.SKFluctuations
open Set MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

theorem restFiniteSteps_clockSteps (n:ℕ) (as:List PositiveMass) (q:ℕ→RestCoordinate n→ℝ≥0) :
    restFiniteSteps n (clockSteps as q)=clockSteps as (fun j=>restFiniteVariance n (q j)) := by
  induction as generalizing q with
  | nil => rfl
  | cons a as ih => exact congrArg (List.cons _) (ih (fun j=>q (j+1)))

theorem restFinite_clockFeatureWeight (n:ℕ) (hn:0<n) {as:List PositiveMass}
    (T:ClockTree (Spin n) as) (q:ℕ→RestCoordinate n→ℝ≥0) (σ:T.Assignment) (x:Spin n→ℝ) :
    clockFeatureWeight (restWeight n) (restFeature n) T q σ x=
      clockFeatureWeight (uniformWeight n) (finiteFeature n) T
        (fun j=>restFiniteVariance n (q j)) σ x := by
  induction T generalizing q x with
  | leaf => rfl
  | @step a as T ih =>
    simp only [clockFeatureWeight]
    rw [restFiniteFeature_law n hn,restFiniteSteps_featureSteps n hn,restFiniteSteps_clockSteps]
    rw [funext (ih (fun j=>q (j+1)) σ)]
    rfl
  | fork T U ihT ihU => exact congrArg₂ (·*·) (ihT q σ.1 x) (ihU q σ.2 x)

theorem restFinite_clockTree_weight (n:ℕ) (hn:0<n) {as:List PositiveMass}
    (T:ClockTree (Spin n) as) (q:ℕ→RestCoordinate n→ℝ≥0) (σ:T.Assignment) (x:RestCoordinate n→ℝ) :
    T.weight (restWeight n) (restFeature n) q σ x=
      T.weight (uniformWeight n) (finiteFeature n) (fun j=>restFiniteVariance n (q j)) σ
        (restFiniteState n x) := by
  rw [ClockTree.weight_featureLaw,ClockTree.weight_featureLaw,
    restFiniteFeatureVector_state n hn,restFinite_clockFeatureWeight n hn]

theorem restFinite_clockTree_expect (n:ℕ) (hn:0<n) {as:List PositiveMass}
    (T:ClockTree (Spin n) as) (q:ℕ→RestCoordinate n→ℝ≥0) (P:T.Assignment→ℝ) (x:RestCoordinate n→ℝ) :
    T.expect (restWeight n) (restFeature n) q P x=
      T.expect (uniformWeight n) (finiteFeature n) (fun j=>restFiniteVariance n (q j)) P
        (restFiniteState n x) := by
  unfold ClockTree.expect
  simp_rw [restFinite_clockTree_weight n hn]

theorem restFinite_clockTree_disorderWeight (n:ℕ) (hn:0<n) {as:List PositiveMass}
    (T:ClockTree (Spin n) as) (l:RestCoordinate n→ℝ) (q:ℕ→RestCoordinate n→ℝ)
    (σ:T.Assignment) (x:RestCoordinate n→ℝ) :
    T.disorderWeight (restWeight n) (restFeature n) l q σ x=
      T.disorderWeight (uniformWeight n) (finiteFeature n) (restFiniteRealVariance n l)
        (fun j=>restFiniteRealVariance n (q j)) σ (restFiniteState n x) := by
  rw [ClockTree.disorderWeight_featureLaw,ClockTree.disorderWeight_featureLaw,
    restFiniteFeatureVector_state n hn,restFiniteFeature_law n hn]
  have hsub:restFiniteRealVariance n (fun i=>q 0 i-l i)=
      fun i=>restFiniteRealVariance n (q 0) i-restFiniteRealVariance n l i :=
    restFiniteRealVariance_sub n (q 0) l
  rw [restFiniteVariance_toNNReal,hsub]
  simp_rw [restFinite_clockFeatureWeight n hn]
  rw [restFinite_cumulativeIncrements]

theorem restFinite_clockTree_disorderExpect (n:ℕ) (hn:0<n) {as:List PositiveMass}
    (T:ClockTree (Spin n) as) (l:RestCoordinate n→ℝ) (q:ℕ→RestCoordinate n→ℝ)
    (P:T.Assignment→ℝ) (x:RestCoordinate n→ℝ) :
    T.disorderExpect (restWeight n) (restFeature n) l q P x=
      T.disorderExpect (uniformWeight n) (finiteFeature n) (restFiniteRealVariance n l)
        (fun j=>restFiniteRealVariance n (q j)) P (restFiniteState n x) := by
  unfold ClockTree.disorderExpect
  simp_rw [restFinite_clockTree_disorderWeight n hn]

theorem restFinite_clockTree_expect_original_root (n:ℕ) (hn:0<n) {as:List PositiveMass}
    (T:ClockTree (Spin n) as) (q:ℕ→RestCoordinate n→ℝ≥0) (P:T.Assignment→ℝ)
    {R:Type*} [MeasurableSpace R] (μ:Measure R) (x:R→RestCoordinate n→ℝ) :
    (∫p,T.expect (restWeight n) (restFeature n) q P (x p) ∂μ)=
      ∫p,T.expect (uniformWeight n) (finiteFeature n) (fun j=>restFiniteVariance n (q j)) P
        (restFiniteState n (x p)) ∂μ := by
  simp_rw [restFinite_clockTree_expect n hn]

end OAI.SKFluctuations
