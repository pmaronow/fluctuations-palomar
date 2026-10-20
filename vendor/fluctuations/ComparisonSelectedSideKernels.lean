module

public import ComparisonSelectedUnitSampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Set Hierarchy
open scoped BigOperators NNReal ENNReal
namespace WholeUnitSideKernel

theorem physical_selected_left_weight_normalized (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n)))
    (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b i : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hai : a < i) (hib : i ≤ b)
    (hunit : ∀u:Fin K,x u.val < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val) :
    (∑k,pathMassDifferences steps 0 k*
      (if k∈J then left a (x (unit k).val) (x ((unit k).val+1)) i else 0))=1 := by
  have hm : 0 < i-a := sub_pos.mpr hai
  have h := physical_selected_unit_weight_normalized steps J unit
    (fun u=>leftFraction (x u.val) (x (u.val+1)) i)
    (fun u=>by rw [hmass]; exact sub_pos.mpr (hunit u)) hm
    (left_finite_fraction_sum x K hstart hend hai.le hib)
  have hw (k : Fin (steps.length+1)) :
      leftFraction (x (unit k).val) (x ((unit k).val+1)) i /
        ((i-a)*physicalSelectedUnitMass steps J unit (unit k))=
      left a (x (unit k).val) (x ((unit k).val+1)) i := by
    rw [hmass]
    unfold left
    rw [div_div]
    congr 1
    ring
  simpa only [hw] using h

theorem physical_selected_right_weight_normalized (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n)))
    (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b i : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hai : a ≤ i) (hib : i < b)
    (hunit : ∀u:Fin K,x u.val < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val) :
    (∑k,pathMassDifferences steps 0 k*
      (if k∈J then right b (x (unit k).val) (x ((unit k).val+1)) i else 0))=1 := by
  have hm : 0 < b-i := sub_pos.mpr hib
  have h := physical_selected_unit_weight_normalized steps J unit
    (fun u=>rightFraction (x u.val) (x (u.val+1)) i)
    (fun u=>by rw [hmass]; exact sub_pos.mpr (hunit u)) hm
    (right_finite_fraction_sum x K hstart hend hai hib.le)
  have hw (k : Fin (steps.length+1)) :
      rightFraction (x (unit k).val) (x ((unit k).val+1)) i /
        ((b-i)*physicalSelectedUnitMass steps J unit (unit k))=
      right b (x (unit k).val) (x ((unit k).val+1)) i := by
    rw [hmass]
    unfold right
    rw [div_div]
    congr 1
    ring
  simpa only [hw] using h

theorem physical_selected_left_variance_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b i tau : ℝ} (hstart : x 0=a) (hend : x K=b)
    (hai : a < i) (hib : i ≤ b) (hunit : ∀u:Fin K,x u.val < x (u.val+1))
    (htau : 0 ≤ tau)
    (henergy : ∀u:Fin K,physicalSelectedUnitEnergy n steps q0 J unit u ≤ tau*(x (u.val+1)-x u.val)) :
    variance (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0
      (fun k=>if k∈J then left a (x (unit k).val) (x ((unit k).val+1)) i else 0) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) ≤ tau/(i-a) := by
  have h := physical_selected_unit_variance_le n steps ha q0 J unit
    (fun u=>x (u.val+1)-x u.val)
    (fun u=>leftFraction (x u.val) (x (u.val+1)) i)
    (fun u=>sub_pos.mpr (hunit u))
    (fun u=>(leftFraction_bounds (hunit u).le).1)
    (fun u=>(leftFraction_bounds (hunit u).le).2)
    htau henergy (sub_pos.mpr hai)
    (left_finite_fraction_sum x K hstart hend hai.le hib)
  have hw : (fun k:Fin (steps.length+1)=>if k∈J then
      leftFraction (x (unit k).val) (x ((unit k).val+1)) i /
        ((i-a)*(x ((unit k).val+1)-x (unit k).val)) else 0)=
      (fun k=>if k∈J then left a (x (unit k).val) (x ((unit k).val+1)) i else 0) := by
    funext k
    congr 1
    unfold left
    rw [div_div]
    congr 1
    ring
  rw [hw] at h
  exact h

theorem physical_selected_right_variance_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b i tau : ℝ} (hstart : x 0=a) (hend : x K=b)
    (hai : a ≤ i) (hib : i < b) (hunit : ∀u:Fin K,x u.val < x (u.val+1))
    (htau : 0 ≤ tau)
    (henergy : ∀u:Fin K,physicalSelectedUnitEnergy n steps q0 J unit u ≤ tau*(x (u.val+1)-x u.val)) :
    variance (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0
      (fun k=>if k∈J then right b (x (unit k).val) (x ((unit k).val+1)) i else 0) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) ≤ tau/(b-i) := by
  have h := physical_selected_unit_variance_le n steps ha q0 J unit
    (fun u=>x (u.val+1)-x u.val)
    (fun u=>rightFraction (x u.val) (x (u.val+1)) i)
    (fun u=>sub_pos.mpr (hunit u))
    (fun u=>(rightFraction_bounds (hunit u).le).1)
    (fun u=>(rightFraction_bounds (hunit u).le).2)
    htau henergy (sub_pos.mpr hib)
    (right_finite_fraction_sum x K hstart hend hai hib.le)
  have hw : (fun k:Fin (steps.length+1)=>if k∈J then
      rightFraction (x (unit k).val) (x ((unit k).val+1)) i /
        ((b-i)*(x ((unit k).val+1)-x (unit k).val)) else 0)=
      (fun k=>if k∈J then right b (x (unit k).val) (x ((unit k).val+1)) i else 0) := by
    funext k
    congr 1
    unfold right
    rw [div_div]
    congr 1
    ring
  rw [hw] at h
  exact h

theorem physical_selected_left_variance_continuousOn (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ)
    {a b δ : ℝ} (hδ : 0 < δ) (hunit : ∀u:Fin K,x u.val < x (u.val+1)) :
    ContinuousOn (fun i=>variance (fun z=>(physicalPinnedPair (uniformWeight n)
      (finiteFeature n) (spinSource n) steps 0
      (fun k=>if k∈J then left a (x (unit k).val) (x ((unit k).val+1)) i else 0) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps))
      (Icc (a+δ) b) := by
  apply physical_selected_weight_variance_continuousOn n steps ha q0
  intro k
  by_cases hk : k∈J
  · simp only [hk,ite_true]
    exact left_continuousOn hδ (hunit (unit k))
  · simp only [hk,ite_false]
    exact continuousOn_const

theorem physical_selected_right_variance_continuousOn (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ)
    {a b δ : ℝ} (hδ : 0 < δ) (hunit : ∀u:Fin K,x u.val < x (u.val+1)) :
    ContinuousOn (fun i=>variance (fun z=>(physicalPinnedPair (uniformWeight n)
      (finiteFeature n) (spinSource n) steps 0
      (fun k=>if k∈J then right b (x (unit k).val) (x ((unit k).val+1)) i else 0) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps))
      (Icc a (b-δ)) := by
  apply physical_selected_weight_variance_continuousOn n steps ha q0
  intro k
  by_cases hk : k∈J
  · simp only [hk,ite_true]
    exact right_continuousOn hδ (hunit (unit k))
  · simp only [hk,ite_false]
    exact continuousOn_const
theorem physical_selected_left_variance_integral_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b δ tau : ℝ} (hstart : x 0=a) (hend : x K=b)
    (hδ : 0 < δ) (hδb : δ ≤ b-a)
    (hunit : ∀u:Fin K,x u.val < x (u.val+1)) (htau : 0 ≤ tau)
    (henergy : ∀u:Fin K,physicalSelectedUnitEnergy n steps q0 J unit u ≤
      tau*(x (u.val+1)-x u.val)) :
    (∫i in (a+δ)..b,variance (fun z=>(physicalPinnedPair (uniformWeight n)
      (finiteFeature n) (spinSource n) steps 0
      (fun k=>if k∈J then left a (x (unit k).val) (x ((unit k).val+1)) i else 0) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)) ≤
      tau*Real.log ((b-a)/δ) := by
  have hab : a+δ ≤ b := by linarith
  have hv := physical_selected_left_variance_continuousOn n K steps ha q0 J unit x (a:=a) (b:=b) hδ hunit
  have hvI := (show ContinuousOn _ (uIcc (a+δ) b) by
    simpa only [uIcc_of_le hab] using hv).intervalIntegrable (μ:=volume)
  have hi : IntervalIntegrable (fun i:ℝ=>(i-a)⁻¹) volume (a+δ) b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (continuous_id.sub continuous_const).continuousOn
    intro i hi
    have hii : i∈Icc (a+δ) b := by simpa only [uIcc_of_le hab] using hi
    change i-a≠0
    exact sub_ne_zero.mpr (by linarith [hii.1])
  have hle := intervalIntegral.integral_mono_on hab hvI (hi.const_mul tau)
    (fun i hi=>by
      simpa only [div_eq_mul_inv] using physical_selected_left_variance_le n K steps ha q0 J unit x
        hstart hend (by linarith [hi.1]) hi.2 hunit htau henergy)
  have he : (∫i in (a+δ)..b,tau*(i-a)⁻¹)=tau*Real.log ((b-a)/δ) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun x:ℝ=>x⁻¹) a]
    have hsub : a+δ-a=δ := by ring
    rw [hsub,integral_inv_of_pos hδ (by linarith)]
  exact hle.trans_eq he

theorem physical_selected_right_variance_integral_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b δ tau : ℝ} (hstart : x 0=a) (hend : x K=b)
    (hδ : 0 < δ) (hδb : δ ≤ b-a)
    (hunit : ∀u:Fin K,x u.val < x (u.val+1)) (htau : 0 ≤ tau)
    (henergy : ∀u:Fin K,physicalSelectedUnitEnergy n steps q0 J unit u ≤
      tau*(x (u.val+1)-x u.val)) :
    (∫i in a..(b-δ),variance (fun z=>(physicalPinnedPair (uniformWeight n)
      (finiteFeature n) (spinSource n) steps 0
      (fun k=>if k∈J then right b (x (unit k).val) (x ((unit k).val+1)) i else 0) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)) ≤
      tau*Real.log ((b-a)/δ) := by
  have hab : a ≤ b-δ := by linarith
  have hv := physical_selected_right_variance_continuousOn n K steps ha q0 J unit x (a:=a) (b:=b) hδ hunit
  have hvI := (show ContinuousOn _ (uIcc a (b-δ)) by
    simpa only [uIcc_of_le hab] using hv).intervalIntegrable (μ:=volume)
  have hi : IntervalIntegrable (fun i:ℝ=>(b-i)⁻¹) volume a (b-δ) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (continuous_const.sub continuous_id).continuousOn
    intro i hi
    have hii : i∈Icc a (b-δ) := by simpa only [uIcc_of_le hab] using hi
    change b-i≠0
    exact sub_ne_zero.mpr (by linarith [hii.2])
  have hle := intervalIntegral.integral_mono_on hab hvI (hi.const_mul tau)
    (fun i hi=>by
      simpa only [div_eq_mul_inv] using physical_selected_right_variance_le n K steps ha q0 J unit x
        hstart hend hi.1 (by linarith [hi.2]) hunit htau henergy)
  have he : (∫i in a..(b-δ),tau*(b-i)⁻¹)=tau*Real.log ((b-a)/δ) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x:ℝ=>x⁻¹) b]
    have hsub : b-(b-δ)=δ := by ring
    rw [hsub,integral_inv_of_pos hδ (by linarith)]
  exact hle.trans_eq he

end WholeUnitSideKernel
end OAI.SKFluctuations
