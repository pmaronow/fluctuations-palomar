module

public import PhysicalCapIndexedTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000

theorem physicalFiniteCapEnergy_band_rooted_eq_path_increment (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex n) (q₀ : FeatureIndex n → ℝ≥0)
    (common mid tail : List (GaussianStep (FeatureIndex n)))
    (ha : OrderedSteps 0 ((common++mid)++tail)) :
    let hfull : OrderedSteps 0 (common++(mid++tail)) := by
      simpa only [List.append_assoc] using ha
    let hmid := hfull.suffix common (mid++tail)
    zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q₀ k))
      (prefixTest common (gaussianHierarchy (uniformWeight n) (finiteFeature n) (mid++tail))
        (physicalFiniteCapEnergy n d e mid tail hmid)) 0 =
      physicalPathSecondMoment n ((common++mid)++tail) q₀ (common++mid).length-
        physicalPathSecondMoment n ((common++mid)++tail) q₀ common.length := by
  dsimp only
  let hfull : OrderedSteps 0 (common++(mid++tail)) := by
    simpa only [List.append_assoc] using ha
  let hmid := hfull.suffix common (mid++tail)
  let htail := hmid.suffix mid tail
  obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) (mid++tail) hmid
  obtain ⟨Ct,hFt⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos n) (finiteFeature n) tail htail
  have hpos : ∀st∈common,0<st.1 := fun st hs=>hfull.mem_pos st (List.mem_append_left _ hs)
  have hposmid : ∀st∈mid,0<st.1 := fun st hs=>hmid.mem_pos st (List.mem_append_left _ hs)
  have hA := prefixTest_smooth0 hFt (physicalSpinMeanSq_smooth n tail htail) mid hposmid
  have hB := physicalSpinMeanSq_smooth n (mid++tail) hmid
  rw [funext (physicalFiniteCapEnergy_eq_increment n d e mid tail hmid),
    funext (prefixTest_subtract hF hA hB common hpos)]
  have hrootA := prefixTest_smooth0 hF hA common hpos
  have hrootB := prefixTest_smooth0 hF hB common hpos
  have hmap : Measurable (fun z : FeatureIndex n→ℝ => (0:FeatureIndex n→ℝ)+z) :=
    measurable_const.add measurable_id
  rw [show zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q₀ k))
      (fun x=>prefixTest common (gaussianHierarchy (uniformWeight n) (finiteFeature n) (mid++tail))
        (prefixTest mid (gaussianHierarchy (uniformWeight n) (finiteFeature n) tail)
          (physicalSpinMeanSq n tail)) x-
        prefixTest common (gaussianHierarchy (uniformWeight n) (finiteFeature n) (mid++tail))
          (physicalSpinMeanSq n (mid++tail)) x) 0 =
      zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q₀ k))
        (prefixTest common (gaussianHierarchy (uniformWeight n) (finiteFeature n) (mid++tail))
          (prefixTest mid (gaussianHierarchy (uniformWeight n) (finiteFeature n) tail)
            (physicalSpinMeanSq n tail))) 0-
      zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q₀ k))
        (prefixTest common (gaussianHierarchy (uniformWeight n) (finiteFeature n) (mid++tail))
          (physicalSpinMeanSq n (mid++tail))) 0 from
        integral_sub (hrootA.integrable_comp_measurable hmap) (hrootB.integrable_comp_measurable hmap)]
  have happ : prefixTest common (gaussianHierarchy (uniformWeight n) (finiteFeature n) (mid++tail))
      (prefixTest mid (gaussianHierarchy (uniformWeight n) (finiteFeature n) tail)
        (physicalSpinMeanSq n tail))=
      prefixTest (common++mid) (gaussianHierarchy (uniformWeight n) (finiteFeature n) tail)
        (physicalSpinMeanSq n tail) := by
    rw [prefixTest_append,prefixContinuation_hierarchy]
  rw [happ,physicalPrefixMeanSq_eq_pathSecondMoment n (common++mid) tail ha q₀,
    physicalPrefixMeanSq_eq_pathSecondMoment n common (mid++tail) hfull q₀,List.append_assoc]

theorem physicalFiniteCapIndexedTrace_band_rooted_le_path_increment (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q₀ : FeatureIndex (n+1) → ℝ≥0)
    (durations : List ℝ≥0) (common mid tail : List (GaussianStep (FeatureIndex (n+1))))
    {g : ℝ} (ha : OrderedSteps 0 ((common++mid)++tail)) (hg : 0<g)
    (hfield : ∀st∈mid,∀j,st.2 (Sum.inl j)=st.2 (Sum.inl 0))
    (hslope : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1)))=>
      g*(w:ℝ) ≤ st.2 (Sum.inl 0)) durations mid) :
    zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q₀ k))
      (physicalFiniteCapIndexedTrace n d e (List.replicate common.length 0++durations)
        (common++mid) tail ha) 0 ≤
      (physicalPathSecondMoment (n+1) ((common++mid)++tail) q₀ (common++mid).length-
        physicalPathSecondMoment (n+1) ((common++mid)++tail) q₀ common.length)/((n+1:ℝ)*g) := by
  let hfull : OrderedSteps 0 (common++(mid++tail)) := by
    simpa only [List.append_assoc] using ha
  let hmid := hfull.suffix common (mid++tail)
  obtain ⟨C,hF⟩ := gaussianHierarchy_lipschitz (uniformWeight_pos (n+1)) (finiteFeature (n+1)) (mid++tail) hmid
  have hpos : ∀st∈common,0<st.1 := fun st hs=>hfull.mem_pos st (List.mem_append_left _ hs)
  have htrace := physicalFiniteCapIndexedTrace_smooth n d e durations mid tail hmid
  have henergy := physicalFiniteCapEnergy_smooth (n+1) d e mid tail hmid
  have hpoint (x : FeatureIndex (n+1)→ℝ) :
      (n+1:ℝ)*g*physicalFiniteCapIndexedTrace n d e durations mid tail hmid x≤
        physicalFiniteCapEnergy (n+1) d e mid tail hmid x :=
    (physicalFiniteCapIndexedTrace_le_fieldTrace n d e durations mid tail hmid hslope x).trans
      (physicalFiniteCapFieldTrace_le_energy n d e mid tail hmid hfield x)
  have hmono := prefixTest_mono hF (htrace.const_mul ((n+1:ℝ)*g)) henergy hpoint common hpos
  have hrootTrace := prefixTest_smooth0 hF (htrace.const_mul ((n+1:ℝ)*g)) common hpos
  have hrootEnergy := prefixTest_smooth0 hF henergy common hpos
  have hmap : Measurable (fun z : FeatureIndex (n+1)→ℝ => (0:FeatureIndex (n+1)→ℝ)+z) :=
    measurable_const.add measurable_id
  have hi := integral_mono (μ:=Measure.pi fun k=>gaussianReal 0 (q₀ k))
    (hrootTrace.integrable_comp_measurable hmap)
    (hrootEnergy.integrable_comp_measurable hmap) (fun z=>hmono (0+z))
  change zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q₀ k))
      (prefixTest common (gaussianHierarchy (uniformWeight (n+1)) (finiteFeature (n+1)) (mid++tail))
        (fun x=>(n+1:ℝ)*g*physicalFiniteCapIndexedTrace n d e durations mid tail hmid x)) 0 ≤
    zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q₀ k))
      (prefixTest common (gaussianHierarchy (uniformWeight (n+1)) (finiteFeature (n+1)) (mid++tail))
        (physicalFiniteCapEnergy (n+1) d e mid tail hmid)) 0 at hi
  rw [rootedPrefixTest_const_mul hF htrace common hpos q₀ ((n+1:ℝ)*g) 0,
    physicalFiniteCapEnergy_band_rooted_eq_path_increment (n+1) d e q₀ common mid tail ha] at hi
  rw [funext (physicalFiniteCapIndexedTrace_zero_prefix n d e durations common mid tail ha hmid)]
  exact (le_div_iff₀ (mul_pos (by positivity : 0<(n+1:ℝ)) hg)).mpr (by
    simpa only [mul_comm] using hi)

end OAI.SKFluctuations.LaplaceWindowFormalization
