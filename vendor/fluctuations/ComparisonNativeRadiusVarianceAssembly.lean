module

public import ComparisonNativeRadiusCoefficientBounds
public import ComparisonMassCellSquareConvergence
public import ComparisonVaryingContactWeights

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

theorem comparison_originalRadiusWeights_square_tendsto_L1 {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Icc (0:ℝ) 1)
    {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin) (hfloor : ∀r∈A,kmin ≤ k r)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hlim : Tendsto mesh atTop (𝓝 0)) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let f := comparisonRadiusMassWeight R α.val.val A x kmin
    Tendsto (fun j=>∫r in Icc (0:ℝ) 1,
      |deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        Finset.univ id (fun i=>(comparisonOriginalRadiusWeights q (as j) f i)^2) r-
        A.indicator (comparisonReciprocalDensityWeight α.val.val x kmin) r|) atTop (𝓝 0) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let f := comparisonRadiusMassWeight R α.val.val A x kmin
  have hf := comparisonRadiusMassWeight_memLp_two R α.val.val
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α).measurable hA hx hkmin
  have hlimNative := MassCellAveraging.sample_square_sweep_tendsto_L1 hc hk hkc hm hM
    α f hf as mesh ho hmesh hend hlim
  have heq (j:ℕ) : (∫r in Icc (0:ℝ) 1,
      |deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
        Finset.univ id (fun i=>(comparisonOriginalRadiusWeights q (as j) f i)^2) r-
        A.indicator (comparisonReciprocalDensityWeight α.val.val x kmin) r|)=
      ∫r in Icc (0:ℝ) 1,
        |deriv α.val.val r*(MassCellAveraging.sample f 0 (as j) (α.val.val r))^2-
          deriv α.val.val r*(f (α.val.val r))^2| := by
    apply integral_congr_ae
    filter_upwards [comparison_originalRadiusWeights_column_ae hc hk hkc hm hM q α f (as j) (ho j) (hend j),
      comparisonRadiusMassWeight_square_pullback hc hk hkc hm hM α hA hAD hx hkmin hfloor]
      with r hcol hfixed
    rw [hcol,←hfixed]
  convert hlimNative using 1
  funext j
  exact heq j

theorem comparison_native_original_radius_variance_eventually
    {N d lam a z x kmin : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hd : 0<d) (hnd : 1/N ≤ d) (hlam : 0<lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (ha : 0<a) (haz : a ≤ z) (hz : z ≤ 1) (hx : 0<x) (hkmin : 0<kmin)
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
    let f := comparisonRadiusMassWeight R α.val.val A x kmin
    let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      let steps := sampleClockSteps q 0 (as j)
      let w := comparisonOriginalRadiusWeights q (as j) f
      variance (fun p=>(physicalPinnedPair (uniformWeight (n+1)) (finiteFeature (n+1))
        (spinSource (n+1)) steps 0 w p.1 p.2).1)
        (rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps) ≤
        4*(S z-S a)/(α.val.val a*x^2*kmin*F)+epsilon := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let f := comparisonRadiusMassWeight R α.val.val A x kmin
  let w := fun j=>comparisonOriginalRadiusWeights q (as j) f
  let W := fun j r=>deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
    q α (as j) Finset.univ id (fun i=>(w j i)^2) r
  let fixed := A.indicator (comparisonReciprocalDensityWeight α.val.val x kmin)
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let mu := fun j=>comparisonPhysicalRadiusMeasure hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)
  let B := (1/(x*kmin))^2
  let err := epsilon*α.val.val a/24
  have haI : a∈Icc (0:ℝ) 1 := ⟨ha.le,haz.trans hz⟩
  have hAD01 : A⊆Icc (0:ℝ) 1 := hAD.trans
    (Ioo_subset_Icc_self.trans (Icc_subset_Icc ha.le hz))
  have hamass : 0<α.val.val a := by
    have ht := inverseConstraint_strictMonoOn hc hk hkc α.property (by norm_num) haI ha
    simpa only [α.property.1] using ht
  have herr : 0<err := by dsimp [err];positivity
  have hfL := comparisonRadiusMassWeight_memLp_two R α.val.val
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α).measurable hA hx hkmin
  have hiF : IntervalIntegrable f volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hfL.integrable (by norm_num))
  have hwbound j i : w j i∈Icc (0:ℝ) (1/(x*kmin)) :=
    MassCellAveraging.originalCoefficient_mem_Icc f (as j) (ho j) (by positivity) hiF
      (fun u _=>comparisonRadiusMassWeight_bounds R α.val.val A hx hkmin u) i.val
  have hsqbound j i : (w j i)^2 ≤ B := by
    have hw := hwbound j i
    exact pow_le_pow_left₀ hw.1 hw.2 2
  have hcolB j r : comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
      Finset.univ id (fun i=>(w j i)^2) r∈Icc (0:ℝ) B := by
    apply radiusCellEnergyDensity_mem_Icc_bound R
      (comparisonSweepQuantile_monotone hc hk hkc hm hM α) (as j) (ho j) _ (by positivity)
    intro i
    unfold nativeSelectedColumn
    split_ifs
    · exact ⟨sq_nonneg _,hsqbound j _⟩
    · exact ⟨le_rfl,by positivity⟩
    · exact ⟨le_rfl,by positivity⟩
  have hLip : LipschitzOnWith ⟨M 1,hM⟩ α.val.val (uIcc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using inverseIntegralConstraints_lipschitz hm hM α.property
  have hACalpha : AbsolutelyContinuousOnInterval α.val.val 0 1 := hLip.absolutelyContinuousOnInterval
  have hiD : IntegrableOn (deriv α.val.val) (Icc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hACalpha.intervalIntegrable_deriv
  have hiW j : IntegrableOn (W j) (Icc (0:ℝ) 1) := by
    have hcmeas := comparisonNativeUnitColumnWeight_measurable hc hk hkc hm hM q α (as j)
      Finset.univ id (fun i=>(w j i)^2)
    have hbnd : ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),
        ‖comparisonNativeUnitColumnWeight hc hk hkc hm hM q α (as j)
          Finset.univ id (fun i=>(w j i)^2) r‖ ≤ B := by
      filter_upwards [] with r
      rw [Real.norm_eq_abs,abs_of_nonneg (hcolB j r).1]
      exact (hcolB j r).2
    simpa only [W,IntegrableOn,mul_comm] using hiD.bdd_mul hcmeas.aestronglyMeasurable.restrict hbnd
  have hiFixed : IntegrableOn fixed (Icc (0:ℝ) 1) := by
    apply (memLp_of_bounded (p:=1) (a:=0) (b:=1/(x^2*kmin)) ?_ ?_).integrable le_rfl
    · exact Eventually.of_forall (fun r=>by
        by_cases hr : r∈A
        · rw [show fixed r=comparisonReciprocalDensityWeight α.val.val x kmin r from indicator_of_mem hr _]
          exact comparisonReciprocalDensityWeight_bounds α.val.val hx hkmin r
        · simp only [fixed,indicator_of_notMem hr];exact ⟨le_rfl,by positivity⟩)
    · exact ((comparisonReciprocalDensityWeight_measurable α.val.val x kmin).indicator hA).aestronglyMeasurable
  have herror := comparison_originalRadiusWeights_square_tendsto_L1 hc hk hkc hm hM
    q α hA hAD01 hx hkmin hfloor as mesh ho hend hmesh hlim
  have htrace := comparison_native_reciprocal_radius_trace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α as mesh ho hend hmesh hmesh0 hlim
    ha haz hz hx hkmin Kb Kh hparent hfield hA hAD herr
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
  have hfixedInt : (∫r,fixed r∂mu j)=(∫r in A,comparisonReciprocalDensityWeight α.val.val x kmin r∂mu j) :=
    integral_indicator hA
  rw [hfixedInt] at hmoving
  have hfilled : (∫r,W j r∂mu j) ≤ (S z-S a)/(x^2*kmin*F)+2*err := by
    dsimp only [W,w,f,R,fixed,mu] at hmoving
    dsimp only [R,bf,hf,S,F] at hjtrace ⊢
    linarith
  have hcut i (hnz : w j i ≠ 0) : α.val.val a/2 ≤ physicalCutMass 0 (sampleClockSteps q 0 (as j)) i.val := by
    have ht := comparisonOriginalRadiusWeights_native_cut_floor hc hk hkc hm hM q α
      haI hAD x kmin (as j) (ho j) (hmesh j) i hnz
    linarith
  have hv := comparison_native_radius_weight_variance_le_filled hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j) (hend j) (hmesh j) (hmesh0 j) (w j)
    (by positivity : 0<α.val.val a/2) (by positivity : 0 ≤ B) (hsqbound j) hcut
  have hbudget : (2*(∫r,W j r∂mu j)+2*(mesh j*B))/(α.val.val a/2) ≤
      4*(S z-S a)/(α.val.val a*x^2*kmin*F)+epsilon := by
    apply (div_le_iff₀ (by positivity : 0<α.val.val a/2)).mpr
    have hfscaled := mul_le_mul_of_nonneg_left hfilled (show (0:ℝ)≤2 by norm_num)
    have hcancel : (4*(S z-S a)/(α.val.val a*x^2*kmin*F)+epsilon)*(α.val.val a/2)=
        2*((S z-S a)/(x^2*kmin*F))+epsilon*α.val.val a/2 := by
      field_simp [hamass.ne'];ring
    rw [hcancel]
    dsimp [err] at hfscaled hjmeshB
    have hpositive := mul_pos hepsilon hamass
    linarith
  exact hv.trans hbudget

end
end OAI.SKFluctuations.LaplaceWindowFormalization
