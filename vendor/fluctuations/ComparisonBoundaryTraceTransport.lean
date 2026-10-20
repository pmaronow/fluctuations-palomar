module

public import PhysicalBoundaryCapLaw
public import PhysicalLocalCapTrace
public import WholePathPhysicalTrace
public import PhysicalCutCovarianceTrace
public import ComparisonSelectedUnitSampling

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped BigOperators NNReal ENNReal Topology

theorem physicalWeightedCutSquareTrace_le_filled_and_mesh (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q0 : FeatureIndex (n+1) → ℝ≥0)
    (durations : List ℝ≥0) (pre tail : List (GaussianStep (FeatureIndex (n+1))))
    {mesh : ℝ} (ha : OrderedSteps 0 (pre++tail))
    (hlen : durations.length ≤ pre.length) (hm : 0 ≤ mesh)
    (hmesh : ∀w∈durations,(w:ℝ) ≤ mesh) :
    physicalWeightedCutSum durations (fun k=>
      ∫p,physicalCutSourceSquareTrace (n+1) (pre++tail) id k p
        ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) q0 (pre++tail)) ≤
      2*zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q0 k))
        (physicalFiniteCapIndexedTrace n d e durations pre tail ha) 0+2*mesh := by
  rw [← physicalFiniteCapBoundaryTrace_rooted_eq_weightedCuts (n+1) q0 durations pre tail ha hlen]
  have hmap : Measurable (fun z:FeatureIndex (n+1) → ℝ=>(0:FeatureIndex (n+1) → ℝ)+z) :=
    measurable_const.add measurable_id
  have hcap := physicalFiniteCapIndexedTrace_smooth n d e durations pre tail ha
  have henergy := physicalFiniteCapEnergy_smooth (n+1) d e pre tail ha
  have h := integral_mono (μ:=Measure.pi fun k=>gaussianReal 0 (q0 k))
    ((physicalFiniteCapBoundaryTrace_smooth (n+1) durations pre tail ha).integrable_comp_measurable hmap)
    (((hcap.const_mul 2).add (henergy.const_mul (2*mesh))).integrable_comp_measurable hmap)
    (fun z=>physicalFiniteCapBoundaryTrace_le_indexedTrace n d e durations pre tail ha hm hmesh (0+z))
  rw [integral_add ((hcap.const_mul 2).integrable_comp_measurable hmap)
    ((henergy.const_mul (2*mesh)).integrable_comp_measurable hmap),integral_const_mul,integral_const_mul] at h
  have he := physicalFiniteCapEnergy_rooted_le_endpoint (n+1) d e q0 pre tail (M:=1) ha 0 (by
    rw [physicalPrefixMeanSq_eq_pathSecondMoment (n+1) pre tail ha q0]
    exact physicalPathSecondMoment_le_one (n+1) (pre++tail) ha q0 (by simp))
  change _ ≤ 2*zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q0 k))
    (physicalFiniteCapIndexedTrace n d e durations pre tail ha) 0+
    2*mesh*zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q0 k))
      (physicalFiniteCapEnergy (n+1) d e pre tail ha) 0 at h
  exact h.trans (add_le_add le_rfl (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2*mesh)))

theorem physicalWeightedCutSquareTrace_band_le_increment (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q0 : FeatureIndex (n+1) → ℝ≥0)
    (durations : List ℝ≥0) (common mid tail : List (GaussianStep (FeatureIndex (n+1))))
    {mesh g : ℝ} (ha : OrderedSteps 0 ((common++mid)++tail))
    (hlen : durations.length ≤ mid.length) (hm : 0 ≤ mesh)
    (hmesh : ∀w∈durations,(w:ℝ) ≤ mesh) (hg : 0 < g)
    (hfield : ∀st∈mid,∀j,st.2 (Sum.inl j)=st.2 (Sum.inl 0))
    (hslope : List.Forall₂ (fun (w:ℝ≥0) (st:GaussianStep (FeatureIndex (n+1)))=>
      g*(w:ℝ) ≤ st.2 (Sum.inl 0)) durations mid) :
    physicalWeightedCutSum durations (fun k=>
      ∫p,physicalCutSourceSquareTrace (n+1) ((common++mid)++tail) id (common.length+k) p
        ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) q0 ((common++mid)++tail)) ≤
      2*(physicalPathSecondMoment (n+1) ((common++mid)++tail) q0 (common++mid).length-
        physicalPathSecondMoment (n+1) ((common++mid)++tail) q0 common.length)/((n+1:ℝ)*g)+2*mesh := by
  have hlen' : (List.replicate common.length 0++durations).length ≤ (common++mid).length := by
    simp only [List.length_append,List.length_replicate]
    omega
  have hmesh' : ∀w∈List.replicate common.length (0:ℝ≥0)++durations,(w:ℝ) ≤ mesh := by
    intro w hw
    rcases List.mem_append.mp hw with hw|hw
    · have hz:w=0 := List.eq_of_mem_replicate hw
      simpa only [hz,NNReal.coe_zero] using hm
    · exact hmesh w hw
  have hboundary := physicalWeightedCutSquareTrace_le_filled_and_mesh n d e q0 _ (common++mid) tail
    ha hlen' hm hmesh'
  rw [physicalWeightedCutSum_zero_prefix] at hboundary
  have hfilled := physicalFiniteCapIndexedTrace_band_rooted_le_path_increment n d e q0 durations
    common mid tail ha hg hfield hslope
  convert hboundary.trans (add_le_add (mul_le_mul_of_nonneg_left hfilled (by norm_num : (0:ℝ) ≤ 2)) le_rfl) using 1 <;> ring

theorem physicalCutSusceptibility_massCellSum_le_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {c a start : ℝ}
    (hc : OrderedSteps c steps) (ha0 : 0 < a) (q0 : FeatureIndex n → ℝ≥0)
    (band : List PositiveMass) (hband : MassOrdered start band) (offset : ℕ)
    (hcut : ∀j < band.length,a ≤ physicalCutMass c steps (offset+j)) :
    massCellSum band start (fun j=>
      ∫p,physicalCutSusceptibility n steps id (offset+j) p
        ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) ≤
      (massCellSum band start (fun j=>
        ∫p,physicalCutSourceSquareTrace n steps id (offset+j) p
          ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps))/a := by
  calc
    _ ≤ massCellSum band start (fun j=>
        (∫p,physicalCutSourceSquareTrace n steps id (offset+j) p
          ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps)/a) := by
      apply massCellSum_mono band hband
      intro j hj
      simpa only [rootedHierarchyPathLaw,Kernel.comap_id] using
        physicalCutSusceptibility_integral_le_square_of_cutMass n steps hc ha0
          (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id (offset+j) (hcut j hj)
    _ = _ := by
      simp only [div_eq_mul_inv,mul_comm _ a⁻¹]
      rw [massCellSum_const_mul]

end OAI.SKFluctuations.LaplaceWindowFormalization
