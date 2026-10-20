module

public import ComparisonActualCutLedger
public import ComparisonNativeVarianceBinGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3000000

theorem radius_finite_centered_overlap_le_mean_square
    {S I : Type*} [Fintype S] [Fintype I]
    (p : S→ℝ) (z : S→I→ℝ) (hp : ∑s,p s=1) (c : ℝ) :
    (∑s,∑t,p s*p t*((∑i,z s i*z t i)-c)^2) ≤
      (FiniteSpinCovariance.meanSq p z-c)^2+
        2*(FiniteSpinCovariance.meanSq p z*Real.sqrt (FiniteSpinCovariance.traceCovSq p z))+
        FiniteSpinCovariance.traceCovSq p z := by
  rw [FiniteSpinCovariance.centered_overlap_decomposition p z hp c]
  have h := FiniteSpinCovariance.meanCovMean_le_sqrt_trace p z
  linarith

theorem radius_hierarchy_centered_overlap_le_mean_square
    {S I J : Type*} [Fintype S] [Nonempty S] [Fintype I] [Fintype J]
    {w : S→ℝ} (hw : ∀s,0<w s) (phi : S→(J→ℝ)→L[ℝ] ℝ) (z : S→I→ℝ)
    (steps : List (GaussianStep J)) {a : ℝ} (ha : OrderedSteps a steps) (x : J→ℝ) (c : ℝ) :
    hierarchyPairMean w phi (fun s t=>((∑i,z s i*z t i)-c)^2) steps x ≤
      ((∑i,(hierarchyVectorMean w phi z steps x i)^2)-c)^2+
        2*((∑i,(hierarchyVectorMean w phi z steps x i)^2)*
          Real.sqrt (hierarchyVectorTraceCovSq w phi z steps x))+
        hierarchyVectorTraceCovSq w phi z steps x := by
  rw [hierarchyVectorTraceCovSq_eq_atoms hw phi z steps ha x,
    hierarchyVectorMean_eq_atoms hw phi z steps ha x]
  simpa only [hierarchyPairMean,FiniteSpinCovariance.meanSq,mul_comm] using
    radius_finite_centered_overlap_le_mean_square
      (fun s=>hierarchyAtom w phi steps s x) z (hierarchyAtom_sum hw phi steps ha x) c

theorem radius_physical_centered_overlap_le_mean_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) {a : ℝ} (ha : OrderedSteps a steps)
    (x : FeatureIndex n→ℝ) (c : ℝ) :
    hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun s t=>(orderedOverlap n s t-c)^2) steps x ≤
      ((∑i,(actualSpinMean n steps x i)^2)-c)^2+
        2*((∑i,(actualSpinMean n steps x i)^2)*Real.sqrt (physicalSpinTraceCovSq n steps x))+
        physicalSpinTraceCovSq n steps x := by
  simpa only [orderedOverlap_normalized,physicalSpinTraceCovSq,physicalSpinCovariance,
    hierarchyVectorTraceCovSq,hierarchyVectorMean,actualSpinMean] using
    radius_hierarchy_centered_overlap_le_mean_square (uniformWeight_pos n) (finiteFeature n)
      (normalizedSpin n) steps ha x c

theorem radius_physical_prefix_defect_le_fourth_covariance (n : ℕ)
    (pre tail : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 (pre++tail))
    (q0 : FeatureIndex n→ℝ≥0) :
    let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
    let X := actualSpinPath n (pre++tail) id
    let c := physicalPathSecondMoment n (pre++tail) q0 pre.length
    let H4 := ∫z,‖X pre.length z‖^4∂mu
    let C := ∫z,physicalSpinTraceCovSq n tail (actualCutField pre tail z.1 z.2)∂mu
    physicalCutPairDefectSecond n pre tail q0 c≤H4+2*(Real.sqrt H4*Real.sqrt C)+C := by
  dsimp only
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 (pre++tail)
  let X := actualSpinPath n (pre++tail) id
  let y := fun z : PhysicalPathState (FeatureIndex n→ℝ) n (pre++tail)=>
    actualCutField pre tail z.1 z.2
  let C := fun z=>physicalSpinTraceCovSq n tail (y z)
  let c := physicalPathSecondMoment n (pre++tail) q0 pre.length
  let := rootedHierarchyPathLaw_probability (uniformWeight_pos n) (finiteFeature n) q0 (pre++tail) ha
  have htail := ha.suffix pre tail
  have hy : Measurable y := actualCutField_measurable_joint pre tail
  have hC0 z : 0≤C z := Finset.sum_nonneg (fun _ _=>Finset.sum_nonneg (fun _ _=>sq_nonneg _))
  have hCs := physicalSpinTraceCovSq_smooth n tail htail
  have hCI : Integrable C mu := hCs.integrable_comp_measurable hy
  have hCr : MemLp (fun z=>Real.sqrt (C z)) 2 mu := by
    obtain ⟨B,_,hB⟩ := hCs.bound
    apply MemLp.of_bound ((hCs.continuous.measurable.comp hy).sqrt).aestronglyMeasurable (Real.sqrt B)
    filter_upwards [] with z
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt ((le_abs_self (C z)).trans (by simpa only [Real.norm_eq_abs] using hB (y z)))
  have hN : MemLp (fun z=>‖X pre.length z‖^2) 2 mu :=
    physical_sqnorm_memLp n (pre++tail) ha id measurable_id mu pre.length 2
  have hF := hN.sub (memLp_const c)
  have hFI : Integrable (fun z=>(‖X pre.length z‖^2-c)^2) mu := by
    simpa only [Pi.sub_apply] using hF.integrable_sq
  have hNI := hN.integrable_mul hCr
  have hDI := (hierarchyPairMean_smooth (uniformWeight_pos n) (finiteFeature n)
    (fun s t=>(orderedOverlap n s t-c)^2) tail htail 0).integrable_comp_measurable hy (μ:=mu)
  have hpoint z : hierarchyPairMean (uniformWeight n) (finiteFeature n)
      (fun s t=>(orderedOverlap n s t-c)^2) tail (y z)≤
      (‖X pre.length z‖^2-c)^2+2*(‖X pre.length z‖^2*Real.sqrt (C z))+C z := by
    have h := radius_physical_centered_overlap_le_mean_square n tail htail (y z) c
    have he : (∑i,(actualSpinMean n tail (y z) i)^2)=‖X pre.length z‖^2 := by
      rw [actualSpinPath_norm_sq_at_cut n pre tail ha,hierarchyPairMean_overlap_eq_norm n tail htail]
      simp only [EuclideanSpace.real_norm_sq_eq,actualSpinMean,y]
    rw [he] at h
    exact h
  have hInt := integral_mono hDI ((hFI.add (hNI.const_mul 2)).add hCI) hpoint
  have hAdd1 := integral_add (hFI.add (hNI.const_mul 2)) hCI
  have hAdd2 := integral_add hFI (hNI.const_mul 2)
  simp only [Pi.add_apply,Pi.mul_apply] at hInt hAdd1 hAdd2
  rw [hAdd1,hAdd2,integral_const_mul] at hInt
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all mu (fun z=>sq_nonneg ‖X pre.length z‖))
    (ae_of_all mu (fun z=>Real.sqrt_nonneg (C z))) (by simpa using hN) (by simpa using hCr)
  simp only [Real.rpow_two,Real.sq_sqrt (hC0 _),←pow_mul] at hCS
  norm_num only at hCS
  rw [←Real.sqrt_eq_rpow,←Real.sqrt_eq_rpow] at hCS
  have hcenter : (∫z,(‖X pre.length z‖^2-c)^2∂mu)≤∫z,‖X pre.length z‖^4∂mu := by
    have hv := variance_eq_sub hN
    rw [variance_eq_integral hN.aestronglyMeasurable.aemeasurable] at hv
    change (∫z,(‖X pre.length z‖^2-c)^2∂mu)=_
      at hv
    simp only [Pi.pow_apply,←pow_mul] at hv
    norm_num only at hv
    linarith [sq_nonneg (∫z,‖X pre.length z‖^2∂mu)]
  dsimp only [physicalCutPairDefectSecond,mu,X,C,y,c] at hInt hCS hcenter ⊢
  linarith

theorem radius_actualCenteredCutReplicaDefect_le_raw_covariance (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) {xs y : ℝ} (hxs : 0<xs)
    {i : ℕ} (hi : i ≤ steps.length) (hui : xs+physicalCutMass 0 steps i≤y) :
    let Q := physicalRawRatio n 2 steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id
    let C := actualCutCovarianceEnergy n steps q0 i
    actualCutReplicaDefect n steps q0 i (physicalPathSecondMoment n steps q0 i)≤
      Q^4*y^2+2*(Q^2*y*Real.sqrt C)+C := by
  dsimp only
  let Q := physicalRawRatio n 2 steps 0 xs (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id
  let mu := rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps
  let pre := steps.take i
  let tail := steps.drop i
  have he : pre++tail=steps := List.take_append_drop i steps
  have hl : pre.length=i := by simp [pre,min_eq_left hi]
  have ho : OrderedSteps 0 (pre++tail) := by simpa only [he] using ha
  have h := radius_physical_prefix_defect_le_fourth_covariance n pre tail ho q0
  dsimp only at h
  rw [physicalCutPairDefectSecond_eq_actualCutReplicaDefect n pre tail ho q0,
    ←actualCutCovarianceEnergy_at_prefix] at h
  rw [he,hl] at h
  have hy : 0≤y := (add_nonneg hxs.le (physicalCutMass_mem steps ha i).1).trans hui
  have hraw := physicalRawRatio_half_moment n 2 (by norm_num) steps ha hxs
    (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id (show i ≤ steps.length+1 by omega)
  rw [←rootedHierarchyPathLaw_eq_physical] at hraw
  norm_num only at hraw
  have hfour : (∫z,‖actualSpinPath n steps id i z‖^4∂mu)≤Q^4*y^2 :=
    hraw.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (add_nonneg hxs.le (physicalCutMass_mem steps ha i).1) hui 2)
      (by positivity : 0≤Q^4))
  have hsqrt := Real.sqrt_le_sqrt hfour
  have heq : Q^4*y^2=(Q^2*y)^2 := by ring
  rw [heq,Real.sqrt_sq (mul_nonneg (sq_nonneg Q) hy)] at hsqrt
  have hcross := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg (actualCutCovarianceEnergy n steps q0 i))
  dsimp only [mu,Q] at hfour hsqrt hcross
  linarith

end OAI.SKFluctuations
