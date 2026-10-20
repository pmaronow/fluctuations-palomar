module

public import SKFluctuationsOAI.Probability.SKFluctuations.CavityActualEndpoint
public import SKFluctuationsOAI.Probability.SKFluctuations.CompletedFeatureKernel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open Set MeasureTheory ProbabilityTheory Hierarchy Cavity
open scoped BigOperators NNReal
attribute [local instance] Classical.propDecidable

def restFiniteEdgeScale (n:ℕ) : ℝ≥0 :=
  ⟨(n:ℝ)/(n+1:ℕ),by positivity⟩

def restFiniteVariance (n:ℕ) (q:RestCoordinate n→ℝ≥0) : FeatureIndex n→ℝ≥0
  | Sum.inl i => q (.inr i)
  | Sum.inr none => 0
  | Sum.inr (some e) => restFiniteEdgeScale n*q (.inl e)

def restFiniteState (n:ℕ) (x:RestCoordinate n→ℝ) : FeatureIndex n→ℝ
  | Sum.inl i => x (.inr i)
  | Sum.inr none => 0
  | Sum.inr (some e) => Real.sqrt (n:ℝ)/Real.sqrt (n+1:ℕ)*x (.inl e)

theorem restFiniteState_measurable (n:ℕ) : Measurable (restFiniteState n) := by
  apply Measurable.of_eval
  intro i
  cases i with
  | inl i => exact measurable_pi_apply _
  | inr i => cases i <;> simp only [restFiniteState] <;> fun_prop

theorem restFiniteFeature_state (n:ℕ) (hn:0<n) (σ:Spin n) (x:RestCoordinate n→ℝ) :
    finiteFeature n σ (restFiniteState n x)=restFeature n σ x := by
  have hsq:Real.sqrt (n:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  rw [finiteFeature_apply,restFeature_apply,Fintype.sum_sum_type,Fintype.sum_option,Fintype.sum_sum_type]
  simp only [featureCoefficient,liftedCoefficients,restFiniteState,restCoefficient,mul_zero,zero_add,
    one_mul]
  have he(e:Edge n):
      (1/Real.sqrt (n:ℝ)*spinValue (σ e.val.1)*spinValue (σ e.val.2))*
        (Real.sqrt (n:ℝ)/Real.sqrt (n+1:ℕ)*x (.inl e))=
      spinValue (σ e.val.1)*spinValue (σ e.val.2)/Real.sqrt (n+1:ℕ)*x (.inl e) := by
    field_simp
  simp_rw [he]
  exact add_comm _ _

theorem restFiniteFeature_law (n:ℕ) (hn:0<n) (q:RestCoordinate n→ℝ≥0) :
    featureLaw (restFeature n) q=featureLaw (finiteFeature n) (restFiniteVariance n q) := by
  apply Subtype.ext
  apply featureVector_law_eq
  intro σ τ
  have hc(ρ:Spin n)(i:RestCoordinate n):restFeature n ρ (Pi.single i 1)=restCoefficient n ρ i := by
    simp [restFeature_apply,Pi.single_apply]
  have hf(ρ:Spin n)(i:FeatureIndex n):finiteFeature n ρ (Pi.single i 1)=featureCoefficient n ρ i := by
    simp [finiteFeature_apply,Pi.single_apply]
  simp only [hc,hf,Fintype.sum_sum_type,Fintype.sum_option,restCoefficient,
    restFiniteVariance,featureCoefficient,liftedCoefficients,NNReal.coe_zero,NNReal.coe_mul,
    restFiniteEdgeScale,zero_mul,one_mul,zero_add]
  have hs:Real.sqrt (n:ℝ)^2=(n:ℝ):=Real.sq_sqrt (Nat.cast_nonneg n)
  have ht:Real.sqrt (n+1:ℕ)^2=(n+1:ℕ):=Real.sq_sqrt (Nat.cast_nonneg _)
  have hn0:(n:ℝ)≠0:=ne_of_gt (Nat.cast_pos.mpr hn)
  have he(e:Edge n):
      (q (.inl e):ℝ)*(spinValue (σ e.val.1)*spinValue (σ e.val.2)/Real.sqrt (n+1:ℕ))*
        (spinValue (τ e.val.1)*spinValue (τ e.val.2)/Real.sqrt (n+1:ℕ))=
      (((n:ℝ)/(n+1:ℕ))*(q (.inl e):ℝ))*
        (1/Real.sqrt (n:ℝ)*spinValue (σ e.val.1)*spinValue (σ e.val.2))*
        (1/Real.sqrt (n:ℝ)*spinValue (τ e.val.1)*spinValue (τ e.val.2)) := by
    calc
      _ = (q (.inl e):ℝ)/(Real.sqrt (n+1:ℕ))^2*
        (spinValue (σ e.val.1)*spinValue (σ e.val.2)*spinValue (τ e.val.1)*spinValue (τ e.val.2)) := by ring
      _ = (q (.inl e):ℝ)/(n+1:ℕ)*
        (spinValue (σ e.val.1)*spinValue (σ e.val.2)*spinValue (τ e.val.1)*spinValue (τ e.val.2)) := by rw [ht]
      _ = (((n:ℝ)/(n+1:ℕ))*(q (.inl e):ℝ))/(Real.sqrt (n:ℝ))^2*
        (spinValue (σ e.val.1)*spinValue (σ e.val.2)*spinValue (τ e.val.1)*spinValue (τ e.val.2)) := by
          rw [hs]
          field_simp
      _ = _ := by ring
  simp_rw [he]
  exact add_comm _ _

theorem restFiniteFeatureVector_state (n:ℕ) (hn:0<n) (x:RestCoordinate n→ℝ) :
    featureVector (finiteFeature n) (restFiniteState n x)=featureVector (restFeature n) x := by
  ext σ
  exact restFiniteFeature_state n hn σ x

def restFiniteSteps (n:ℕ) (steps:List (GaussianStep (RestCoordinate n))) :
    List (GaussianStep (FeatureIndex n)) := steps.map (fun s => (s.1,restFiniteVariance n s.2))

@[simp] theorem restFiniteSteps_length (n:ℕ) (steps:List (GaussianStep (RestCoordinate n))) :
    (restFiniteSteps n steps).length=steps.length := List.length_map _

@[simp] theorem restFiniteSteps_append (n:ℕ) (pre post:List (GaussianStep (RestCoordinate n))) :
    restFiniteSteps n (pre++post)=restFiniteSteps n pre++restFiniteSteps n post := List.map_append

theorem restFiniteSteps_ordered (n:ℕ) {a:ℝ} (steps:List (GaussianStep (RestCoordinate n)))
    (ho:OrderedSteps a steps) : OrderedSteps a (restFiniteSteps n steps) := by
  induction steps generalizing a with
  | nil => exact ho
  | cons s steps ih => exact ⟨ho.1,ho.2.1,ho.2.2.1,ih ho.2.2.2⟩

theorem restFiniteSteps_featureSteps (n:ℕ) (hn:0<n) (steps:List (GaussianStep (RestCoordinate n))) :
    featureSteps (restFeature n) steps=featureSteps (finiteFeature n) (restFiniteSteps n steps) := by
  induction steps with
  | nil => rfl
  | cons s steps ih =>
    simp only [featureSteps,restFiniteSteps,List.map_cons]
    rw [restFiniteFeature_law n hn s.2]
    exact congrArg (List.cons _) ih

theorem restFiniteSteps_split (n:ℕ) (u:ℝ) (steps:List (GaussianStep (RestCoordinate n))) :
    (restFiniteSteps n (splitClockSteps u steps).1,restFiniteSteps n (splitClockSteps u steps).2)=
      splitClockSteps u (restFiniteSteps n steps) := by
  induction steps with
  | nil => rfl
  | cons s steps ih =>
    simp only [splitClockSteps,restFiniteSteps,List.map_cons]
    split_ifs with hs
    · have hp:=congrArg Prod.fst ih
      have ht:=congrArg Prod.snd ih
      simp only [restFiniteSteps] at hp ht
      rw [List.map_cons,hp,ht]
    · rfl

theorem restFinite_gaussianHierarchy (n:ℕ) (hn:0<n)
    (steps:List (GaussianStep (RestCoordinate n))) (x:RestCoordinate n→ℝ) :
    gaussianHierarchy (restWeight n) (restFeature n) steps x=
      gaussianHierarchy (uniformWeight n) (finiteFeature n) (restFiniteSteps n steps) (restFiniteState n x) := by
  rw [gaussianHierarchy_featureLaw,gaussianHierarchy_featureLaw,
    restFiniteSteps_featureSteps n hn,restFiniteFeatureVector_state n hn]
  rfl

theorem restFinite_gaussianHierarchyMean (n:ℕ) (hn:0<n) (A:Spin n→ℝ)
    (steps:List (GaussianStep (RestCoordinate n))) (x:RestCoordinate n→ℝ) :
    gaussianHierarchyMean (restWeight n) (restFeature n) A steps x=
      gaussianHierarchyMean (uniformWeight n) (finiteFeature n) A (restFiniteSteps n steps) (restFiniteState n x) := by
  rw [gaussianHierarchyMean_featureLaw,gaussianHierarchyMean_featureLaw,
    restFiniteSteps_featureSteps n hn,restFiniteFeatureVector_state n hn]
  rfl

theorem restFinite_prefixTest (n:ℕ) (hn:0<n)
    (pre post:List (GaussianStep (RestCoordinate n)))
    (A:(Spin n→ℝ)→ℝ) (hA:Measurable A) (x:RestCoordinate n→ℝ) :
    prefixTest pre (gaussianHierarchy (restWeight n) (restFeature n) post)
      (fun y => A (featureVector (restFeature n) y)) x=
    prefixTest (restFiniteSteps n pre)
      (gaussianHierarchy (uniformWeight n) (finiteFeature n) (restFiniteSteps n post))
      (fun y => A (featureVector (finiteFeature n) y)) (restFiniteState n x) := by
  rw [prefixTest_featureLaw _ _ _ _ A hA,prefixTest_featureLaw _ _ _ _ A hA,
    restFiniteSteps_featureSteps n hn,restFiniteSteps_featureSteps n hn,
    restFiniteFeatureVector_state n hn]
  rfl

theorem restFinite_stepPairDisorder (n:ℕ) (hn:0<n) (q:RestCoordinate n→ℝ≥0)
    (pre post:List (GaussianStep (RestCoordinate n))) (P:Spin n→Spin n→ℝ) (x:RestCoordinate n→ℝ) :
    stepPairDisorder (restWeight n) (restFeature n) q pre post P x=
      stepPairDisorder (uniformWeight n) (finiteFeature n) (restFiniteVariance n q)
        (restFiniteSteps n pre) (restFiniteSteps n post) P (restFiniteState n x) := by
  rw [stepPairDisorder_featureLaw,stepPairDisorder_featureLaw,restFiniteFeature_law n hn,
    restFiniteSteps_featureSteps n hn,restFiniteSteps_featureSteps n hn,
    restFiniteFeatureVector_state n hn]
  rfl

theorem restFiniteVariance_sub (n:ℕ) (q r:RestCoordinate n→ℝ≥0) :
    restFiniteVariance n (q-r)=restFiniteVariance n q-restFiniteVariance n r := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i <;> simp [restFiniteVariance,mul_tsub]

theorem restFiniteSteps_sampleClockSteps (n:ℕ) (q:ℝ→RestCoordinate n→ℝ≥0)
    (a:ℝ) (as:List PositiveMass) :
    restFiniteSteps n (sampleClockSteps q a as)=
      sampleClockSteps (fun u=>restFiniteVariance n (q u)) a as := by
  induction as generalizing a with
  | nil => rfl
  | cons b bs ih =>
    simp only [sampleClockSteps,restFiniteSteps,List.map_cons]
    exact congrArg₂ List.cons (congrArg (Prod.mk b.val) (restFiniteVariance_sub n (q b.val) (q a)))
      (ih b.val)

def restFiniteRealVariance (n:ℕ) (q:RestCoordinate n→ℝ) : FeatureIndex n→ℝ
  | Sum.inl i => q (.inr i)
  | Sum.inr none => 0
  | Sum.inr (some e) => (restFiniteEdgeScale n:ℝ)*q (.inl e)

theorem restFiniteRealVariance_sub (n:ℕ) (q r:RestCoordinate n→ℝ) :
    restFiniteRealVariance n (q-r)=restFiniteRealVariance n q-restFiniteRealVariance n r := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i <;> simp [restFiniteRealVariance,mul_sub]

theorem restFiniteVariance_toNNReal (n:ℕ) (q:RestCoordinate n→ℝ) :
    restFiniteVariance n (fun i=>(q i).toNNReal)=fun i=>(restFiniteRealVariance n q i).toNNReal := by
  funext i
  cases i with
  | inl i => rfl
  | inr i => cases i <;> simp [restFiniteVariance,restFiniteRealVariance,
      Real.toNNReal_mul (restFiniteEdgeScale n).coe_nonneg]

theorem restFinite_cumulativeIncrements (n:ℕ) (l:RestCoordinate n→ℝ) (q:ℕ→RestCoordinate n→ℝ) :
    (fun j=>restFiniteVariance n (cumulativeIncrements l q j))=
      cumulativeIncrements (restFiniteRealVariance n l) (fun j=>restFiniteRealVariance n (q j)) := by
  funext j
  cases j with
  | zero =>
    change restFiniteVariance n (fun i=>(q 0 i-l i).toNNReal)=
      fun i=>(restFiniteRealVariance n (q 0) i-restFiniteRealVariance n l i).toNNReal
    rw [restFiniteVariance_toNNReal]
    exact congrArg (fun f:FeatureIndex n→ℝ=>fun i=>(f i).toNNReal)
      (restFiniteRealVariance_sub n (q 0) l)
  | succ j =>
    change restFiniteVariance n (fun i=>(q (j+1) i-q j i).toNNReal)=
      fun i=>(restFiniteRealVariance n (q (j+1)) i-restFiniteRealVariance n (q j) i).toNNReal
    rw [restFiniteVariance_toNNReal]
    exact congrArg (fun f:FeatureIndex n→ℝ=>fun i=>(f i).toNNReal)
      (restFiniteRealVariance_sub n (q (j+1)) (q j))

end OAI.SKFluctuations
