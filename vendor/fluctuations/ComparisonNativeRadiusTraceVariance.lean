module

public import ComparisonNativeRadiusVariance
public import ComparisonPhysicalWeightedGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000
attribute [local instance] Classical.propDecidable

theorem reciprocal_density_derivative_budget {S weight : ℝ→ℝ} {a z K : ℝ}
    (haz : a ≤ z) (hS : MonotoneOn S (Icc a z))
    (hAC : AbsolutelyContinuousOnInterval S a z)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Icc a z)
    (hwm : AEStronglyMeasurable weight volume) (hK : 0 ≤ K)
    (hwb : ∀r∈A,‖weight r‖ ≤ K) (hw0 : ∀r∈A,0 ≤ weight r) :
    (∫r in A,weight r*deriv S r) ≤ K*(S z-S a) := by
  have hiD : IntegrableOn (deriv S) (Icc a z) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le haz).mp hAC.intervalIntegrable_deriv
  have hiA := hiD.mono_set hAD
  have hiProd : IntegrableOn (fun r=>weight r*deriv S r) A :=
    hiA.bdd_mul hwm.restrict (by
      filter_upwards [ae_restrict_mem hA] with r hr
      exact hwb r hr)
  have hn : 0 ≤ᵐ[volume.restrict (Icc a z)] deriv S := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (monotoneOn_deriv_ae_nonneg hS)] with r hr hd
    exact hd hr
  have hle : (∫r in A,weight r*deriv S r) ≤ ∫r in A,K*deriv S r := by
    apply integral_mono_ae hiProd (hiA.const_mul K)
    filter_upwards [ae_restrict_mem hA,
      ae_restrict_of_ae (monotoneOn_deriv_ae_nonneg hS)] with r hr hd
    have hwle : weight r ≤ K := (le_abs_self _).trans (by simpa using hwb r hr)
    exact mul_le_mul_of_nonneg_right hwle (hd (hAD hr))
  have hsub := setIntegral_mono_set hiD hn (Eventually.of_forall hAD)
  have htotal : (∫r in Icc a z,deriv S r)=S z-S a := by
    rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le haz]
    exact hAC.integral_deriv_eq_sub
  rw [integral_const_mul] at hle
  exact hle.trans (by rw [←htotal];exact mul_le_mul_of_nonneg_left hsub hK)

def comparisonReciprocalDensityWeight (α : ℝ→ℝ) (x kmin : ℝ) : ℝ→ℝ :=
  fun r=>1/(x^2*max kmin (deriv α r))

theorem comparisonReciprocalDensityWeight_bounds (α : ℝ→ℝ)
    {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin) (r : ℝ) :
    0 ≤ comparisonReciprocalDensityWeight α x kmin r ∧
      comparisonReciprocalDensityWeight α x kmin r ≤ 1/(x^2*kmin) := by
  have hp : 0<x^2 := sq_pos_of_pos hx
  have hm : 0 < max kmin (deriv α r) := hkmin.trans_le (le_max_left _ _)
  constructor
  · exact div_nonneg zero_le_one (mul_nonneg hp.le hm.le)
  · exact one_div_le_one_div_of_le (mul_pos hp hkmin)
      (mul_le_mul_of_nonneg_left (le_max_left _ _) hp.le)

theorem comparisonReciprocalDensityWeight_measurable (α : ℝ→ℝ) (x kmin : ℝ) :
    Measurable (comparisonReciprocalDensityWeight α x kmin) :=
  measurable_const.div (measurable_const.mul (measurable_const.max (stronglyMeasurable_deriv α).measurable))

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparison_native_radius_weight_variance_le_filled
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (d lam : ℝ) (b h : ℝ→ℝ) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (w : Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1)→ℝ)
    {a B : ℝ} (ha : 0<a) (hB : 0 ≤ B) (hbound : ∀i,(w i)^2 ≤ B)
    (hcut : ∀i,w i ≠ 0→a ≤ physicalCutMass 0 (sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as) i.val) :
    let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
    let steps := sampleClockSteps q 0 as
    variance (fun p=>(physicalPinnedPair (uniformWeight (n+1)) (finiteFeature (n+1))
      (spinSource (n+1)) steps 0 w p.1 p.2).1)
      (rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps) ≤
      (2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        q α as Finset.univ id (fun i=>(w i)^2) r∂comparisonPhysicalRadiusMeasure
          hc hk hkc hm hM n dphys e d lam b h α as ho)+2*(mesh*B))/a := by
  dsimp only
  let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
  let steps := sampleClockSteps q 0 as
  have hv := physical_radius_weight_variance_le_source_square (n+1) steps
    (sampleClockSteps_ordered q _ ho) (q 0) w ha hcut
  have heq : (∑i,pathMassDifferences steps 0 i*(w i)^2*
      ∫p,physicalCutSourceSquareTrace (n+1) steps id i.val p
        ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps)=
      nativeWeightedSquareEnergy (n+1) steps (q 0) Finset.univ id (fun i=>(w i)^2) := by
    unfold nativeWeightedSquareEnergy
    simp only [nativeSelectedColumn_atIndex,Finset.mem_univ,ite_true,id_eq]
  rw [heq] at hv
  have hs := comparisonNativeWeightedSquareEnergy_le_integral hc hk hkc hm hM
    n dphys e d lam b h α as ho he hmesh hmesh0 Finset.univ id (fun i=>(w i)^2)
    (fun i=>sq_nonneg _) hB hbound
  exact hv.trans (div_le_div_of_nonneg_right hs ha.le)

theorem comparison_native_reciprocal_radius_trace_eventually
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
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in A,comparisonReciprocalDensityWeight α.val.val x kmin r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α (as j) (ho j)) ≤
      (S z-S a)/(x^2*kmin*F)+epsilon := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let weight := comparisonReciprocalDensityWeight α.val.val x kmin
  have hF : 0<F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hS : MonotoneOn S (Icc a z) :=
    ((comparisonVariableEndpoint_radius_moments hc hk hkc hm hM (n+1) (by omega)
      b h hd.ne' hlam.le hlb hb hh hh0 α).1).mono (Icc_subset_Icc ha.le hz)
  have hAC := actual_variableEndpoint_radius_overlap_absolutelyContinuous hc hk hkc hm hM
    n dphys e b h hb hh hh0 hd.ne' hlam.le hlb α ha haz hz Kb hparent Kh hfield
  have hw (r:ℝ) := comparisonReciprocalDensityWeight_bounds α.val.val hx hkmin r
  have hwm : AEStronglyMeasurable weight volume :=
    (comparisonReciprocalDensityWeight_measurable α.val.val x kmin).aestronglyMeasurable
  have hbudget := reciprocal_density_derivative_budget haz hS hAC hA
    (hAD.trans Ioo_subset_Icc_self) hwm (by positivity : 0 ≤ 1/(x^2*kmin))
    (fun r _=>by simpa only [weight,Real.norm_eq_abs,abs_of_nonneg (hw r).1] using (hw r).2)
    (fun r _=>(hw r).1)
  have ht := comparisonPhysicalRadiusTrace_boundedWeight_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α as mesh ho hend hmesh hmesh0 hlim
    ha haz hz Kb Kh hparent hfield hA hAD weight hwm (1/(x^2*kmin))
    (fun r _=>by simpa only [weight,Real.norm_eq_abs,abs_of_nonneg (hw r).1] using (hw r).2)
    (fun r _=>(hw r).1) hepsilon
  filter_upwards [ht] with j hj
  apply hj.trans
  have hb := div_le_div_of_nonneg_right hbudget hF.le
  have hb2 : (∫r in A,weight r*deriv S r)/F ≤ (S z-S a)/(x^2*kmin*F) := by
    convert hb using 1 <;> ring
  linarith

end
end OAI.SKFluctuations.LaplaceWindowFormalization
