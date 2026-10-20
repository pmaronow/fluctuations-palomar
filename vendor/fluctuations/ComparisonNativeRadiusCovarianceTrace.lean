module

public import ComparisonNativeRadiusLinearConvergence

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem physical_radius_weight_covariance_le_source_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n→ℝ≥0) (w : Fin (steps.length+1)→ℝ)
    (hw : ∀i,0 ≤ w i) {a : ℝ} (ha0 : 0<a)
    (hcut : ∀i,w i ≠ 0→a ≤ physicalCutMass 0 steps i.val) :
    (∑i,pathMassDifferences steps 0 i*w i*actualCutCovarianceEnergy n steps q0 i.val) ≤
      nativeWeightedSquareEnergy n steps q0 Finset.univ id w/a^2 := by
  unfold nativeWeightedSquareEnergy
  simp only [nativeSelectedColumn_atIndex,Finset.mem_univ,ite_true,id_eq]
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : w i=0
  · simp only [hi,mul_zero,zero_mul,zero_div,le_refl]
  · have h := physicalCutSpinTraceCovSq_integral_le_square_of_cutMass n steps ha ha0
      (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id i.val (hcut i hi)
    try simp only [←rootedHierarchyPathLaw_eq_physical] at h
    have hw0 : 0 ≤ pathMassDifferences steps 0 i*w i :=
      mul_nonneg (pathMassDifferences_nonneg steps ha i) (hw i)
    simpa only [actualCutCovarianceEnergy,mul_div_assoc,rootedHierarchyPathLaw,Kernel.comap_id]
      using mul_le_mul_of_nonneg_left h hw0

theorem comparison_native_radius_weight_covariance_le_filled
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (d lam : ℝ) (b h : ℝ→ℝ) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (w : Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1)→ℝ)
    {a B : ℝ} (ha : 0<a) (hB : 0 ≤ B) (hw : ∀i,0 ≤ w i) (hbound : ∀i,w i ≤ B)
    (hcut : ∀i,w i ≠ 0→a ≤ physicalCutMass 0 (sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as) i.val) :
    let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
    let steps := sampleClockSteps q 0 as
    (∑i,pathMassDifferences steps 0 i*w i*actualCutCovarianceEnergy (n+1) steps (q 0) i.val) ≤
      (2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        q α as Finset.univ id w r∂comparisonPhysicalRadiusMeasure
          hc hk hkc hm hM n dphys e d lam b h α as ho)+2*(mesh*B))/a^2 := by
  dsimp only
  let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
  have hv := physical_radius_weight_covariance_le_source_square (n+1) (sampleClockSteps q 0 as)
    (sampleClockSteps_ordered q _ ho) (q 0) w hw ha hcut
  have hs := comparisonNativeWeightedSquareEnergy_le_integral hc hk hkc hm hM
    n dphys e d lam b h α as ho he hmesh hmesh0 Finset.univ id w hw hB hbound
  exact hv.trans (div_le_div_of_nonneg_right hs (sq_nonneg a))

theorem comparison_native_plain_radius_trace_eventually
    {N d lam a z : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hd : 0<d) (hnd : 1/N ≤ d) (hlam : 0<lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (ha : 0<a) (haz : a ≤ z) (hz : z ≤ 1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z))
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo a z)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫_r in A,(1:ℝ)
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α (as j) (ho j)) ≤
      (S z-S a)/F+epsilon := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let weight := fun (_:ℝ)=>(1:ℝ)
  have hF : 0<F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hS : MonotoneOn S (Icc a z) :=
    ((comparisonVariableEndpoint_radius_moments hc hk hkc hm hM (n+1) (by omega)
      b h hd.ne' hlam.le hlb hb hh hh0 α).1).mono (Icc_subset_Icc ha.le hz)
  have hAC := actual_variableEndpoint_radius_overlap_absolutelyContinuous hc hk hkc hm hM
    n dphys e b h hb hh hh0 hd.ne' hlam.le hlb α ha haz hz Kb hparent Kh hfield
  have hwm : AEStronglyMeasurable weight volume :=
    aestronglyMeasurable_const
  have hbudget := reciprocal_density_derivative_budget haz hS hAC hA
    (hAD.trans Ioo_subset_Icc_self) hwm (by norm_num : (0:ℝ) ≤ 1)
    (fun r _=>by norm_num [weight])
    (fun r _=>by norm_num [weight])
  have ht := comparisonPhysicalRadiusTrace_boundedWeight_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α as mesh ho hend hmesh hmesh0 hlim
    ha haz hz Kb Kh hparent hfield hA hAD weight hwm 1
    (fun r _=>by norm_num [weight])
    (fun r _=>by norm_num [weight]) hepsilon
  filter_upwards [ht] with j hj
  apply hj.trans
  have hb := div_le_div_of_nonneg_right hbudget hF.le
  have hb2 : (∫r in A,weight r*deriv S r)/F ≤ (S z-S a)/F := by
    simpa only [one_mul] using hb
  linarith

theorem comparison_native_original_radius_covariance_eventually
    {N d lam a z kmin : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hd : 0<d) (hnd : 1/N ≤ d) (hlam : 0<lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (ha : 0<a) (haz : a ≤ z) (hz : z ≤ 1) (hkmin : 0<kmin)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z))
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo a z)
    (hfloor : ∀r∈A,kmin ≤ k r)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let q := completedPathClock (n+1) bf hf
    let f := comparisonRadiusMassWeight R α.val.val A 1 kmin
    let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      let steps := sampleClockSteps q 0 (as j)
      let w := comparisonOriginalRadiusWeights q (as j) f
      (∑i,pathMassDifferences steps 0 i*w i*actualCutCovarianceEnergy (n+1) steps (q 0) i.val) ≤
        8*(S z-S a)/(α.val.val a^2*F)+epsilon := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let f := comparisonRadiusMassWeight R α.val.val A 1 kmin
  let w := fun j=>comparisonOriginalRadiusWeights q (as j) f
  let W := fun j r=>deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
    q α (as j) Finset.univ id (w j) r
  let fixed := A.indicator (fun _=>(1:ℝ))
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let mu := fun j=>comparisonPhysicalRadiusMeasure hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)
  let B := 1/kmin
  let err := epsilon*α.val.val a^2/48
  have haI : a∈Icc (0:ℝ) 1 := ⟨ha.le,haz.trans hz⟩
  have hAD01 : A⊆Icc (0:ℝ) 1 := hAD.trans
    (Ioo_subset_Icc_self.trans (Icc_subset_Icc ha.le hz))
  have hamass : 0<α.val.val a := by
    have ht := inverseConstraint_strictMonoOn hc hk hkc α.property (by norm_num) haI ha
    simpa only [α.property.1] using ht
  have herr : 0<err := by dsimp [err];positivity
  have hfL := comparisonRadiusMassWeight_memLp_two R α.val.val
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α).measurable hA (by norm_num : (0:ℝ)<1) hkmin
  have hiF : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hfL.integrable (by norm_num))
  have hwbound j i : w j i∈Icc (0:ℝ) (1/kmin) := by
    simpa only [w,comparisonOriginalRadiusWeights,one_mul] using
      MassCellAveraging.originalCoefficient_mem_Icc f (as j) (ho j) (by positivity) hiF
        (fun u _=>comparisonRadiusMassWeight_bounds R α.val.val A (by norm_num : (0:ℝ)<1) hkmin u) i.val
  have hcolB j r : comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
      Finset.univ id (w j) r∈Icc (0:ℝ) B := by
    apply radiusCellEnergyDensity_mem_Icc_bound R
      (comparisonSweepQuantile_monotone hc hk hkc hm hM α) (as j) (ho j) _ (by positivity)
    intro i
    unfold nativeSelectedColumn
    split_ifs
    · exact hwbound j _
    · exact ⟨le_rfl,by positivity⟩
    · exact ⟨le_rfl,by positivity⟩
  have hLip : LipschitzOnWith ⟨M 1,hM⟩ α.val.val (uIcc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using inverseIntegralConstraints_lipschitz hm hM α.property
  have hACalpha : AbsolutelyContinuousOnInterval α.val.val 0 1 := hLip.absolutelyContinuousOnInterval
  have hiD : IntegrableOn (deriv α.val.val) (Icc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hACalpha.intervalIntegrable_deriv
  have hiW j : IntegrableOn (W j) (Icc (0:ℝ) 1) := by
    have hcmeas := comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α (as j)
      Finset.univ id (w j)
    have hbnd : ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
        ‖comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
          Finset.univ id (w j) r‖ ≤ B := by
      filter_upwards [] with r
      rw [Real.norm_eq_abs,abs_of_nonneg (hcolB j r).1]
      exact (hcolB j r).2
    simpa only [W,IntegrableOn,mul_comm] using hiD.bdd_mul hcmeas.aestronglyMeasurable.restrict hbnd
  have hiFixed : IntegrableOn fixed (Icc (0:ℝ) 1) :=
    (integrable_const (1:ℝ)).indicator hA
  have herror := comparison_originalRadiusWeights_linear_tendsto_L1 hc hk hkc hm hM
    q α hA hAD01 (by norm_num : (0:ℝ)<1) hkmin hfloor as mesh ho hend hmesh hlim
  have htrace := comparison_native_plain_radius_trace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α as mesh ho hend hmesh hmesh0 hlim
    ha haz hz Kb Kh hparent hfield hA hAD herr
  have hmeshError : Tendsto (fun j=>mesh j*B) atTop (𝓝 0) := by simpa using hlim.mul_const B
  filter_upwards [htrace,(tendsto_order.mp herror).2 err herr,
    (tendsto_order.mp hlim).2 (α.val.val a/2) (by positivity),
    (tendsto_order.mp hmeshError).2 err herr] with j hjtrace hjerror hjmesh hjmeshB
  have hdom := comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)
  have hsupport : (mu j).restrict (Icc (0:ℝ) 1)=mu j :=
    Measure.restrict_eq_self_of_ae_mem ((ae_restrict_mem measurableSet_Icc).filter_mono (ae_mono hdom))
  have hmoving := dominated_setIntegral_difference_le (Icc (0:ℝ) 1) (Icc (0:ℝ) 1)
    (Subset.refl _) (mu j) (hdom.trans Measure.restrict_le_self) fixed (W j) hiFixed (hiW j)
  rw [hsupport] at hmoving
  have hfixedInt : (∫r,fixed r∂mu j)=(∫_r in A,(1:ℝ)∂mu j) :=
    integral_indicator hA
  rw [hfixedInt] at hmoving
  have hfilled : (∫r,W j r∂mu j) ≤ (S z-S a)/F+2*err := by
    dsimp only [W,w,f,R,fixed,mu] at hmoving
    dsimp only [R,bf,hf,S,F] at hjtrace ⊢
    linarith
  have hcut i (hnz : w j i ≠ 0) : α.val.val a/2 ≤ physicalCutMass 0 (sampleClockSteps q 0 (as j)) i.val := by
    have ht := comparisonOriginalRadiusWeights_native_cut_floor hc hk hkc hm hM q α
      haI hAD 1 kmin (as j) (ho j) (hmesh j) i hnz
    linarith
  have hv := comparison_native_radius_weight_covariance_le_filled hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j) (hend j) (hmesh j) (hmesh0 j) (w j)
    (by positivity : 0<α.val.val a/2) (by positivity : 0 ≤ B) (fun i=>(hwbound j i).1) (fun i=>(hwbound j i).2) hcut
  have hbudget : (2*(∫r,W j r∂mu j)+2*(mesh j*B))/(α.val.val a/2)^2 ≤
      8*(S z-S a)/(α.val.val a^2*F)+epsilon := by
    apply (div_le_iff₀ (by positivity : 0<(α.val.val a/2)^2)).mpr
    have hfscaled := mul_le_mul_of_nonneg_left hfilled (show (0:ℝ)≤2 by norm_num)
    have hcancel : (8*(S z-S a)/(α.val.val a^2*F)+epsilon)*(α.val.val a/2)^2=
        2*((S z-S a)/F)+epsilon*α.val.val a^2/4 := by
      field_simp [hamass.ne'];ring
    rw [hcancel]
    dsimp [err] at hfscaled hjmeshB
    have hpositive := mul_pos hepsilon (sq_pos_of_pos hamass)
    linarith
  exact hv.trans hbudget

end
end OAI.SKFluctuations.LaplaceWindowFormalization
