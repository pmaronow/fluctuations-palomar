module

public import ComparisonContinuumSideKernel

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Set Hierarchy
open scoped BigOperators NNReal ENNReal
namespace WholeUnitSideKernel

theorem left_finite_fraction_sum (x : ℕ → ℝ) (K : ℕ) {a b i : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hai : a ≤ i) (hib : i ≤ b) :
    (∑u:Fin K,leftFraction (x u.val) (x (u.val+1)) i)=i-a := by
  rw [Fin.sum_univ_eq_sum_range (fun u=>leftFraction (x u) (x (u+1)) i)]
  rw [left_fraction_sum,hstart,hend,min_eq_left hib,min_eq_right hai]

theorem right_finite_fraction_sum (x : ℕ → ℝ) (K : ℕ) {a b i : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hai : a ≤ i) (hib : i ≤ b) :
    (∑u:Fin K,rightFraction (x u.val) (x (u.val+1)) i)=b-i := by
  rw [Fin.sum_univ_eq_sum_range (fun u=>rightFraction (x u) (x (u+1)) i)]
  rw [right_fraction_sum,hstart,hend,max_eq_right hib,max_eq_left hai]

theorem physical_left_weight_normalized (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b i : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hai : a < i) (hib : i ≤ b)
    (hunit : ∀u:Fin K,x u.val < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSamplingUnitMass steps unit u=x (u.val+1)-x u.val) :
    (∑k,pathMassDifferences steps 0 k*
      left a (x (unit k).val) (x ((unit k).val+1)) i)=1 := by
  have hm : 0 < i-a := sub_pos.mpr hai
  have h := physical_whole_unit_side_weight_normalized steps unit
    (fun u=>leftFraction (x u.val) (x (u.val+1)) i)
    (fun u=>by rw [hmass]; exact sub_pos.mpr (hunit u)) hm
    (left_finite_fraction_sum x K hstart hend hai.le hib)
  have hw (k : Fin (steps.length+1)) :
      leftFraction (x (unit k).val) (x ((unit k).val+1)) i /
        ((i-a)*physicalSamplingUnitMass steps unit (unit k))=
      left a (x (unit k).val) (x ((unit k).val+1)) i := by
    rw [hmass]
    unfold left
    rw [div_div]
    congr 1
    ring
  simpa only [hw] using h

theorem physical_right_weight_normalized (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n)))
    (unit : Fin (steps.length+1) → Fin K) (x : ℕ → ℝ) {a b i : ℝ}
    (hstart : x 0=a) (hend : x K=b) (hai : a ≤ i) (hib : i < b)
    (hunit : ∀u:Fin K,x u.val < x (u.val+1))
    (hmass : ∀u:Fin K,physicalSamplingUnitMass steps unit u=x (u.val+1)-x u.val) :
    (∑k,pathMassDifferences steps 0 k*
      right b (x (unit k).val) (x ((unit k).val+1)) i)=1 := by
  have hm : 0 < b-i := sub_pos.mpr hib
  have h := physical_whole_unit_side_weight_normalized steps unit
    (fun u=>rightFraction (x u.val) (x (u.val+1)) i)
    (fun u=>by rw [hmass]; exact sub_pos.mpr (hunit u)) hm
    (right_finite_fraction_sum x K hstart hend hai hib.le)
  have hw (k : Fin (steps.length+1)) :
      rightFraction (x (unit k).val) (x ((unit k).val+1)) i /
        ((b-i)*physicalSamplingUnitMass steps unit (unit k))=
      right b (x (unit k).val) (x ((unit k).val+1)) i := by
    rw [hmass]
    unfold right
    rw [div_div]
    congr 1
    ring
  simpa only [hw] using h

theorem physical_left_variance_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b i tau : ℝ} (hstart : x 0=a) (hend : x K=b)
    (hai : a < i) (hib : i ≤ b) (hunit : ∀u:Fin K,x u.val < x (u.val+1))
    (htau : 0 ≤ tau)
    (henergy : ∀u:Fin K,physicalSamplingUnitEnergy n steps q0 unit u ≤ tau*(x (u.val+1)-x u.val)) :
    variance (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0
      (fun k=>left a (x (unit k).val) (x ((unit k).val+1)) i) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) ≤ tau/(i-a) := by
  have h := physical_whole_unit_side_variance_le n steps ha q0 unit
    (fun u=>x (u.val+1)-x u.val)
    (fun u=>leftFraction (x u.val) (x (u.val+1)) i)
    (fun u=>sub_pos.mpr (hunit u))
    (fun u=>(leftFraction_bounds (hunit u).le).1)
    (fun u=>(leftFraction_bounds (hunit u).le).2)
    htau henergy (sub_pos.mpr hai)
    (left_finite_fraction_sum x K hstart hend hai.le hib)
  have hw : (fun k:Fin (steps.length+1)=>
      leftFraction (x (unit k).val) (x ((unit k).val+1)) i /
        ((i-a)*(x ((unit k).val+1)-x (unit k).val)))=
      (fun k=>left a (x (unit k).val) (x ((unit k).val+1)) i) := by
    funext k
    unfold left
    rw [div_div]
    congr 1
    ring
  rw [hw] at h
  exact h

theorem physical_right_variance_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b i tau : ℝ} (hstart : x 0=a) (hend : x K=b)
    (hai : a ≤ i) (hib : i < b) (hunit : ∀u:Fin K,x u.val < x (u.val+1))
    (htau : 0 ≤ tau)
    (henergy : ∀u:Fin K,physicalSamplingUnitEnergy n steps q0 unit u ≤ tau*(x (u.val+1)-x u.val)) :
    variance (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n)
      (spinSource n) steps 0
      (fun k=>right b (x (unit k).val) (x ((unit k).val+1)) i) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) ≤ tau/(b-i) := by
  have h := physical_whole_unit_side_variance_le n steps ha q0 unit
    (fun u=>x (u.val+1)-x u.val)
    (fun u=>rightFraction (x u.val) (x (u.val+1)) i)
    (fun u=>sub_pos.mpr (hunit u))
    (fun u=>(rightFraction_bounds (hunit u).le).1)
    (fun u=>(rightFraction_bounds (hunit u).le).2)
    htau henergy (sub_pos.mpr hib)
    (right_finite_fraction_sum x K hstart hend hai hib.le)
  have hw : (fun k:Fin (steps.length+1)=>
      rightFraction (x (unit k).val) (x ((unit k).val+1)) i /
        ((b-i)*(x ((unit k).val+1)-x (unit k).val)))=
      (fun k=>right b (x (unit k).val) (x ((unit k).val+1)) i) := by
    funext k
    unfold right
    rw [div_div]
    congr 1
    ring
  rw [hw] at h
  exact h

theorem variance_linearCombination_continuousOn {Ω I : Type*}
    [MeasurableSpace Ω] [Fintype I] (mu : Measure Ω) [IsFiniteMeasure mu]
    (Y : I → Ω → ℝ) (w : ℝ → I → ℝ) (A : Set ℝ)
    (hY : ∀k,MemLp (Y k) 2 mu) (hw : ∀k,ContinuousOn (fun i=>w i k) A) :
    ContinuousOn (fun i=>variance (fun z=>∑k,w i k*Y k z) mu) A := by
  have he (i : ℝ) : variance (fun z=>∑k,w i k*Y k z) mu=
      ∑k,∑l,w i k*(w i l*covariance (Y k) (Y l) mu) := by
    rw [variance_fun_sum (fun k=>(hY k).const_mul (w i k))]
    simp only [covariance_const_mul_left,covariance_const_mul_right]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [he]
  apply continuousOn_finset_sum
  intro k _
  apply continuousOn_finset_sum
  intro l _
  exact (hw k).mul ((hw l).mul continuousOn_const)

theorem physical_left_variance_continuousOn (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b δ : ℝ} (hδ : 0 < δ)
    (hunit : ∀u:Fin K,x u.val < x (u.val+1)) :
    ContinuousOn (fun i=>variance (fun z=>(physicalPinnedPair (uniformWeight n)
      (finiteFeature n) (spinSource n) steps 0
      (fun k=>left a (x (unit k).val) (x ((unit k).val+1)) i) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps))
      (Icc (a+δ) b) := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hY (k : Fin (steps.length+1)) : MemLp (terminalScore X (steps.length+1) k.val) 2 mu :=
    terminalScore_memLp (actualSpinPath_rooted_martingale n steps ha q0)
      (R:=1) (fun j=>ae_of_all _ (fun z=>actualSpinPath_norm_le n steps ha id j z)) _ _ _
  have he (i : ℝ) :
      (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        steps 0 (fun k=>left a (x (unit k).val) (x ((unit k).val+1)) i) z.1 z.2).1)=
      (fun z=>∑k:Fin (steps.length+1),
        (pathMassDifferences steps 0 k*left a (x (unit k).val) (x ((unit k).val+1)) i)*
          terminalScore X (steps.length+1) k.val z) := by
    funext z
    have hh := physicalPinnedPair_fst_eq_window n steps ha
      (fun k=>left a (x (unit k).val) (x ((unit k).val+1)) i) id z
    simpa only [terminalWindow,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,X,id_eq] using hh
  simp_rw [he]
  apply variance_linearCombination_continuousOn mu _ _ _ hY
  intro k
  exact continuousOn_const.mul (left_continuousOn hδ (hunit (unit k)))

theorem physical_right_variance_continuousOn (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b δ : ℝ} (hδ : 0 < δ)
    (hunit : ∀u:Fin K,x u.val < x (u.val+1)) :
    ContinuousOn (fun i=>variance (fun z=>(physicalPinnedPair (uniformWeight n)
      (finiteFeature n) (spinSource n) steps 0
      (fun k=>right b (x (unit k).val) (x ((unit k).val+1)) i) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps))
      (Icc a (b-δ)) := by
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let X := actualSpinPath n steps id
  have := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 steps ha
  have hY (k : Fin (steps.length+1)) : MemLp (terminalScore X (steps.length+1) k.val) 2 mu :=
    terminalScore_memLp (actualSpinPath_rooted_martingale n steps ha q0)
      (R:=1) (fun j=>ae_of_all _ (fun z=>actualSpinPath_norm_le n steps ha id j z)) _ _ _
  have he (i : ℝ) :
      (fun z=>(physicalPinnedPair (uniformWeight n) (finiteFeature n) (spinSource n)
        steps 0 (fun k=>right b (x (unit k).val) (x ((unit k).val+1)) i) z.1 z.2).1)=
      (fun z=>∑k:Fin (steps.length+1),
        (pathMassDifferences steps 0 k*right b (x (unit k).val) (x ((unit k).val+1)) i)*
          terminalScore X (steps.length+1) k.val z) := by
    funext z
    have hh := physicalPinnedPair_fst_eq_window n steps ha
      (fun k=>right b (x (unit k).val) (x ((unit k).val+1)) i) id z
    simpa only [terminalWindow,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,X,id_eq] using hh
  simp_rw [he]
  apply variance_linearCombination_continuousOn mu _ _ _ hY
  intro k
  exact continuousOn_const.mul (right_continuousOn hδ (hunit (unit k)))

theorem physical_left_variance_integral_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b δ tau : ℝ} (hstart : x 0=a) (hend : x K=b)
    (hδ : 0 < δ) (hδb : δ ≤ b-a)
    (hunit : ∀u:Fin K,x u.val < x (u.val+1)) (htau : 0 ≤ tau)
    (henergy : ∀u:Fin K,physicalSamplingUnitEnergy n steps q0 unit u ≤
      tau*(x (u.val+1)-x u.val)) :
    (∫i in (a+δ)..b,variance (fun z=>(physicalPinnedPair (uniformWeight n)
      (finiteFeature n) (spinSource n) steps 0
      (fun k=>left a (x (unit k).val) (x ((unit k).val+1)) i) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)) ≤
      tau*Real.log ((b-a)/δ) := by
  have hab : a+δ ≤ b := by linarith
  have hv := physical_left_variance_continuousOn n K steps ha q0 unit x (a:=a) (b:=b) hδ hunit
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
      simpa only [div_eq_mul_inv] using physical_left_variance_le n K steps ha q0 unit x
        hstart hend (by linarith [hi.1]) hi.2 hunit htau henergy)
  have he : (∫i in (a+δ)..b,tau*(i-a)⁻¹)=tau*Real.log ((b-a)/δ) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun x:ℝ=>x⁻¹) a]
    have hsub : a+δ-a=δ := by ring
    rw [hsub,integral_inv_of_pos hδ (by linarith)]
  exact hle.trans_eq he

theorem physical_right_variance_integral_le (n K : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) (unit : Fin (steps.length+1) → Fin K)
    (x : ℕ → ℝ) {a b δ tau : ℝ} (hstart : x 0=a) (hend : x K=b)
    (hδ : 0 < δ) (hδb : δ ≤ b-a)
    (hunit : ∀u:Fin K,x u.val < x (u.val+1)) (htau : 0 ≤ tau)
    (henergy : ∀u:Fin K,physicalSamplingUnitEnergy n steps q0 unit u ≤
      tau*(x (u.val+1)-x u.val)) :
    (∫i in a..(b-δ),variance (fun z=>(physicalPinnedPair (uniformWeight n)
      (finiteFeature n) (spinSource n) steps 0
      (fun k=>right b (x (unit k).val) (x ((unit k).val+1)) i) z.1 z.2).1)
      (rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)) ≤
      tau*Real.log ((b-a)/δ) := by
  have hab : a ≤ b-δ := by linarith
  have hv := physical_right_variance_continuousOn n K steps ha q0 unit x (a:=a) (b:=b) hδ hunit
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
      simpa only [div_eq_mul_inv] using physical_right_variance_le n K steps ha q0 unit x
        hstart hend hi.1 (by linarith [hi.2]) hunit htau henergy)
  have he : (∫i in a..(b-δ),tau*(b-i)⁻¹)=tau*Real.log ((b-a)/δ) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x:ℝ=>x⁻¹) b]
    have hsub : b-(b-δ)=δ := by ring
    rw [hsub,integral_inv_of_pos hδ (by linarith)]
  exact hle.trans_eq he

end WholeUnitSideKernel
end OAI.SKFluctuations
