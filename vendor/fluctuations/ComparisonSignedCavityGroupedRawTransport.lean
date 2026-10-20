module

public import ComparisonSignedCavityGroupedPrefixLaw
public import SKFluctuationsOAI.Probability.SKFluctuations.FiniteRetainedGridReady

@[expose] public section

noncomputable section
set_option maxHeartbeats 2500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations
open Hierarchy Cavity

theorem physical_norm_power_at_cut_eq_prefix_test (n l : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (hs : OrderedSteps a (pre++tail)) (μ : Measure (FeatureIndex n→ℝ)) [IsFiniteMeasure μ] :
    (∫ p,‖actualSpinPath n (pre++tail) id pre.length p‖^(2*l)
      ∂physicalPathLaw μ n (pre++tail) id measurable_id) =
      ∫ x,prefixTest pre (gaussianHierarchy (uniformWeight n) (finiteFeature n) tail)
        (fun y=>(hierarchyPairMean (uniformWeight n) (finiteFeature n) (orderedOverlap n) tail y)^l)
        x ∂μ := by
  have hI := physicalCutNormPower_integrable n (pre++tail) hs μ id measurable_id pre.length (2*l)
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) (pre++tail) hs
  unfold physicalPathLaw at hI ⊢
  rw [Measure.integral_compProd hI]
  simp_rw [pow_mul,actualSpinPath_norm_sq_at_cut n pre tail hs]
  simp only [Kernel.comap_apply,id_eq]
  simp_rw [integral_actualCutField_test (uniformWeight_pos n) (finiteFeature n) pre tail hs
    ((hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n) (orderedOverlap n)
      tail (hs.suffix pre tail) 0).pow l)]

theorem physical_norm_power_original_prefix (n l : ℕ)
    (pre mid tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (hs : OrderedSteps a (pre++(mid++tail)))
    (μ : Measure (FeatureIndex n→ℝ)) [IsFiniteMeasure μ] :
    let μlow := actualPrefixFieldLaw (uniformWeight n) (finiteFeature n)
      pre (mid++tail) μ id measurable_id
    (∫ p,‖actualSpinPath n (mid++tail) id mid.length p‖^(2*l)
      ∂physicalPathLaw μlow n (mid++tail) id measurable_id) =
      ∫ p,‖actualSpinPath n (pre++(mid++tail)) id (pre.length+mid.length) p‖^(2*l)
        ∂physicalPathLaw μ n (pre++(mid++tail)) id measurable_id := by
  dsimp only
  haveI := actualPrefixFieldLaw_finite (uniformWeight_pos n) (finiteFeature n)
    pre (mid++tail) hs μ id measurable_id
  have ht := hs.suffix pre (mid++tail)
  have htail := ht.suffix mid tail
  let B := fun y=>(hierarchyPairMean (uniformWeight n) (finiteFeature n) (orderedOverlap n) tail y)^l
  have hB : BddSmooth 0 B := (hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (orderedOverlap n) tail htail 0).pow l
  obtain ⟨C,hC⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) tail htail
  have hmpos : ∀ st ∈ mid,0<st.1 := fun st hst=>ht.mem_pos st (List.mem_append_left tail hst)
  have hM := prefixTest_smooth0 hC hB mid hmpos
  rw [physical_norm_power_at_cut_eq_prefix_test n l mid tail ht,
    integral_actualPrefixFieldLaw (uniformWeight_pos n) (finiteFeature n) pre (mid++tail)
      hs μ id measurable_id hM]
  have hs' : OrderedSteps a ((pre++mid)++tail) := by simpa only [List.append_assoc] using hs
  have H := physical_norm_power_at_cut_eq_prefix_test n l (pre++mid) tail hs' μ
  rw [List.append_assoc] at H
  simp only [List.length_append] at H
  rw [H]
  apply integral_congr_ae
  exact Eventually.of_forall fun x=>by
    rw [prefixTest_append,prefixContinuation_hierarchy]
    rfl

theorem physical_norm_power_original_prefix_cut (n l : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a : ℝ}
    (hs : OrderedSteps a (pre++tail))
    (μ : Measure (FeatureIndex n→ℝ)) [IsFiniteMeasure μ] (k : ℕ) (hk : k ≤ tail.length) :
    let μlow := actualPrefixFieldLaw (uniformWeight n) (finiteFeature n) pre tail μ id measurable_id
    (∫ p,‖actualSpinPath n tail id k p‖^(2*l)
      ∂physicalPathLaw μlow n tail id measurable_id) =
      ∫ p,‖actualSpinPath n (pre++tail) id (pre.length+k) p‖^(2*l)
        ∂physicalPathLaw μ n (pre++tail) id measurable_id := by
  have he : tail.take k++tail.drop k=tail := List.take_append_drop _ _
  have hl : (tail.take k).length=k := List.length_take_of_le hk
  have H := physical_norm_power_original_prefix n l pre (tail.take k) (tail.drop k)
    (by simpa only [he] using hs) μ
  rw [he] at H
  simpa only [hl] using H

theorem physicalCutMass_original_prefix {ι : Type} (pre tail : List (GaussianStep ι))
    (a : ℝ) (k : ℕ) :
    physicalCutMass (prefixEndMass a pre) tail k=physicalCutMass a (pre++tail) (pre.length+k) := by
  induction pre generalizing a with
  | nil => simp only [prefixEndMass,List.nil_append,List.length_nil,Nat.zero_add]
  | cons st pre ih => simpa only [prefixEndMass,List.length_cons,List.cons_append,
      Nat.succ_add,physicalCutMass] using ih st.1

theorem physicalRawRatio_original_prefix_le (n l : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) {a xs : ℝ}
    (hs : OrderedSteps a (pre++tail)) (hxs : 0<xs)
    (μ : Measure (FeatureIndex n→ℝ)) [IsProbabilityMeasure μ] :
    let μlow := actualPrefixFieldLaw (uniformWeight n) (finiteFeature n) pre tail μ id measurable_id
    physicalRawRatio n l tail (prefixEndMass a pre) xs μlow id measurable_id ≤
      physicalRawRatio n l (pre++tail) a xs μ id measurable_id := by
  dsimp only
  let μlow := actualPrefixFieldLaw (uniformWeight n) (finiteFeature n) pre tail μ id measurable_id
  haveI : IsProbabilityMeasure μlow := actualPrefixFieldLaw_probability (uniformWeight_pos n)
    (finiteFeature n) pre tail hs μ id measurable_id
  have ht := prefixEndMass_ordered pre tail hs
  have := hierarchyPathKernel_markov (uniformWeight_pos n) (finiteFeature n) tail ht
  haveI : IsProbabilityMeasure (physicalPathLaw μlow n tail id measurable_id) := by
    unfold physicalPathLaw; infer_instance
  change max 1 _ ≤ _
  apply max_le (physicalRawRatio_one_le n l (pre++tail) a xs μ id measurable_id)
  apply Finset.sup'_le
  intro k hk
  have hk' : k ≤ tail.length+1 := by have := Finset.mem_range.mp hk; omega
  have hpos : 0<Real.sqrt (xs+physicalCutMass (prefixEndMass a pre) tail k) :=
    Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg hxs (physicalCutMass_mem tail ht k).1)
  apply (div_le_iff₀ hpos).2
  by_cases hcut : k ≤ tail.length
  · have H := physicalRawRatio_bound n l (pre++tail) hs hxs μ id measurable_id
      (show pre.length+k ≤ (pre++tail).length+1 by simp only [List.length_append]; omega)
    have he := physical_norm_power_original_prefix_cut n (2*l) pre tail hs μ k hcut
    simp only [show 2*(2*l)=4*l by omega] at he
    rw [←he,←physicalCutMass_original_prefix pre tail a k] at H
    exact H
  · have he : k=tail.length+1 := by omega
    have hmass : physicalCutMass (prefixEndMass a pre) tail k=1 := by
      have hterminal (bs : List (GaussianStep (FeatureIndex n))) (c : ℝ) :
          physicalCutMass c bs (bs.length+1)=1 := by
        induction bs generalizing c with
        | nil => rfl
        | cons st bs ih => exact ih st.1
      rw [he]; exact hterminal tail _
    have hI := physicalCutNormPower_integrable n tail ht μlow id measurable_id k (4*l)
    have hi : (∫ p,‖actualSpinPath n tail id k p‖^(4*l)
        ∂physicalPathLaw μlow n tail id measurable_id) ≤ 1 := by
      have H := integral_mono hI (integrable_const (1:ℝ)) fun p=>
        (pow_le_pow_left₀ (norm_nonneg _) (actualSpinPath_norm_le n tail ht id k p) (4*l)).trans_eq
          (one_pow _)
      simpa only [integral_const,probReal_univ,smul_eq_mul,mul_one] using H
    have hsqrt : 1 ≤ Real.sqrt (xs+physicalCutMass (prefixEndMass a pre) tail k) := by
      rw [hmass]; exact Real.le_sqrt_of_sq_le (by nlinarith)
    have hr := Real.rpow_le_rpow (integral_nonneg fun p=>pow_nonneg (norm_nonneg _) _) hi
      (by positivity : 0 ≤ ((4*l:ℕ):ℝ)⁻¹)
    simp only [Real.one_rpow] at hr
    apply hr.trans
    have hQ := physicalRawRatio_one_le n l (pre++tail) a xs μ id measurable_id
    nlinarith

theorem original_boundary_raw_ratio_le_full (n l : ℕ) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (q : ℕ→FeatureIndex n→ℝ) (low : ℕ)
    (hlow : low ≤ as.length) {xs : ℝ} (hxs : 0<xs) :
    let inc := cumulativeIncrements (q 0) (fun j=>q (j+1))
    let steps := clockSteps as inc
    let μ := Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))
    physicalRawRatio n l (originalBoundaryTailSteps n as q low)
      (physicalCutMass 0 steps low) xs (originalBoundaryPrefixLaw n as q low) id measurable_id ≤
      physicalRawRatio n l steps 0 xs μ id measurable_id := by
  dsimp only
  let inc := cumulativeIncrements (q 0) (fun j=>q (j+1))
  let ps := clockSteps (as.take low) inc
  let ts := originalBoundaryTailSteps n as q low
  have hfull : clockSteps as inc=ps++ts := clockSteps_take_drop as inc low hlow
  have hlen : ps.length=low := by dsimp [ps]; rw [length_clockSteps,List.length_take_of_le hlow]
  have hs : OrderedSteps 0 (ps++ts) := by rw [←hfull]; exact clockSteps_ordered ho inc
  have hc : prefixEndMass 0 ps=physicalCutMass 0 (clockSteps as inc) low := by
    rw [hfull]
    simpa only [physicalCutMass,hlen,Nat.add_zero] using physicalCutMass_original_prefix ps ts 0 0
  have H := physicalRawRatio_original_prefix_le n l ps ts hs hxs
    (Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i))))
  dsimp only at H
  rw [hc,←hfull] at H
  simpa only [originalBoundaryPrefixLaw,originalBoundaryTailSteps,ps,ts,inc] using H

end OAI.SKFluctuations
