module

public import ComparisonSelectedContactSideTrace
public import ComparisonBoundaryTraceTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped BigOperators NNReal ENNReal Topology
set_option maxHeartbeats 1800000

def radiusBoundaryDurations (x : ℕ → ℝ) (K : ℕ) (S : Set ℝ) (f : ℝ → ℝ) : List ℝ≥0 :=
  List.ofFn (fun i : Fin K => (∫r in S ∩ Ioc (x i.val) (x (i.val+1)), f r).toNNReal)

theorem contactWeightedCutSum_ofFn {K : ℕ} (w : Fin K → ℝ≥0) (C : ℕ → ℝ) :
    physicalWeightedCutSum (List.ofFn w) C=∑i : Fin K, (w i:ℝ)*C i.val := by
  induction K generalizing C with
  | zero => simp [physicalWeightedCutSum]
  | succ K ih =>
    rw [List.ofFn_succ, physicalWeightedCutSum, ih, Fin.sum_univ_succ]
    rfl

theorem finiteRadiusCellDensity_weighted_integral (K : ℕ) (x C : ℕ → ℝ)
    (S : Set ℝ) (f : ℝ → ℝ) (hi : IntegrableOn f S) :
    (∫r in S, f r*finiteRadiusCellDensity K x C r)=
      ∑i : Fin K, (∫r in S ∩ Ioc (x i.val) (x (i.val+1)), f r)*C i.val := by
  have he i : (fun r => f r*(Ioc (x i) (x (i+1))).indicator (fun _ => C i) r)=
      (Ioc (x i) (x (i+1))).indicator (fun r => f r*C i) := by
    funext r
    by_cases hr : r∈Ioc (x i) (x (i+1)) <;> simp [hr]
  have hiTerm i : IntegrableOn (fun r => f r*(Ioc (x i) (x (i+1))).indicator (fun _ => C i) r) S := by
    rw [he]
    exact (hi.mul_const (C i)).indicator measurableSet_Ioc
  simp only [finiteRadiusCellDensity, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hiTerm i),
    Fin.sum_univ_eq_sum_range (fun i : ℕ => (∫r in S ∩ Ioc (x i) (x (i+1)), f r)*C i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [he, setIntegral_indicator measurableSet_Ioc, integral_mul_const]

theorem radiusBoundaryDurations_filled_sum (K : ℕ) (x C : ℕ → ℝ)
    (S : Set ℝ) (f : ℝ → ℝ) (hi : IntegrableOn f S) (hf : ∀r, 0 ≤ f r) :
    physicalWeightedCutSum (radiusBoundaryDurations x K S f) C=
      ∫r in S, f r*finiteRadiusCellDensity K x C r := by
  rw [radiusBoundaryDurations, contactWeightedCutSum_ofFn]
  simp only [Real.coe_toNNReal _ (integral_nonneg (fun r => hf r))]
  exact (finiteRadiusCellDensity_weighted_integral K x C S f hi).symm

theorem cellDensityMeasure_weighted_integral (K : ℕ) (x C : ℕ → ℝ)
    (hC : ∀i<K, 0 ≤ C i) (S : Set ℝ) (hS : MeasurableSet S) (f : ℝ → ℝ) :
    (∫r in S, f r∂volume.withDensity (fun r => ENNReal.ofReal (finiteRadiusCellDensity K x C r)))=
      ∫r in S, f r*finiteRadiusCellDensity K x C r := by
  have hm : Measurable (finiteRadiusCellDensity K x C) := by
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.indicator measurableSet_Ioc
  rw [restrict_withDensity hS,
    integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
      (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact ae_of_all _ (fun r => by
    change (ENNReal.ofReal (finiteRadiusCellDensity K x C r)).toReal*f r = f r*finiteRadiusCellDensity K x C r
    rw [ENNReal.toReal_ofReal (finiteRadiusCellDensity_nonneg hC r), mul_comm])

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1, c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def comparisonRadiusBoundaryDurations (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (S : Set ℝ) (w : ℝ → ℝ) : List ℝ≥0 :=
  radiusBoundaryDurations
    (fun j => comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as j))
    as.length S (fun r => deriv α.val.val r*w r)

def comparisonRadiusBoundarySquareEnergy (n dphys : ℕ)
    (_e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (d lam : ℝ) (b h : ℝ → ℝ)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (S : Set ℝ) (w : ℝ → ℝ) : ℝ :=
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let steps := sampleClockSteps q 0 as
  physicalWeightedCutSum (comparisonRadiusBoundaryDurations hc hk hkc hm hM α as S w)
    (fun j => ∫p, physicalCutSourceSquareTrace (n+1) steps id j p
      ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) steps)

def comparisonRadiusBoundaryFilledTrace (n dphys : ℕ)
    (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (d lam : ℝ) (b h : ℝ → ℝ)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (S : Set ℝ) (w : ℝ → ℝ) : ℝ :=
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let steps := sampleClockSteps q 0 as
  let ha : OrderedSteps 0 (steps++[]) := by
    simpa only [List.append_nil] using sampleClockSteps_ordered q _ ho
  zeroContinuation (Measure.pi fun j => gaussianReal 0 (q 0 j))
    (physicalFiniteCapIndexedTrace n dphys e
      (comparisonRadiusBoundaryDurations hc hk hkc hm hM α as S w) steps [] ha) 0

include hm hM in
theorem comparison_radiusWeight_integrableOn
    (α : inverseIntegralConstraints 0 0 k M)
    {a z : ℝ} (ha : 0 < a) (hz : z ≤ 1)
    (S : Set ℝ) (hS : MeasurableSet S) (hsub : S ⊆ Ioo a z)
    (w : ℝ → ℝ) (hw : Measurable w) {B : ℝ}
    (hwb : ∀r, ‖w r‖ ≤ B) :
    IntegrableOn (fun r => deriv α.val.val r*w r) S := by
  have hfMeas : AEStronglyMeasurable (fun r => deriv α.val.val r*w r) volume :=
    (stronglyMeasurable_deriv α.val.val).aestronglyMeasurable.mul
      hw.stronglyMeasurable.aestronglyMeasurable
  have hbound r (hr : r∈S) : ‖deriv α.val.val r*w r‖ ≤ M 1*B := by
    have hrr := hsub hr
    have hr01 : r∈Ioo (0:ℝ) 1 := ⟨ha.trans hrr.1, hrr.2.trans_le hz⟩
    have hd : ‖deriv α.val.val r‖ ≤ M 1 :=
      norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr01.1 hr01.2)
        (inverseIntegralConstraints_lipschitz hm hM α.property)
    rw [norm_mul]
    exact mul_le_mul hd (hwb r) (norm_nonneg _) hM
  have hSf : volume S≠⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc a z)≠⊤)
    (measure_mono (hsub.trans Ioo_subset_Icc_self))
  have hOne : IntegrableOn (fun _ : ℝ => (1:ℝ)) S := integrableOn_const hSf
  simpa only [IntegrableOn, mul_one] using hOne.bdd_mul hfMeas.restrict
    ((ae_restrict_mem hS).mono (fun r hr => hbound r hr))

theorem comparisonRadiusBoundaryDurations_mesh
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as)
    {a z : ℝ} (ha : 0 < a) (hz : z ≤ 1)
    (S : Set ℝ) (hS : MeasurableSet S) (hsub : S ⊆ Ioo a z)
    (w : ℝ → ℝ) (hw : Measurable w) {B : ℝ} (hB : 0 ≤ B)
    (hw0 : ∀r, 0 ≤ w r) (hwb : ∀r, w r ≤ B) :
    ∀v∈comparisonRadiusBoundaryDurations hc hk hkc hm hM α as S w, (v:ℝ) ≤ mesh*B := by
  intro v hv
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hv
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let u := partitionPoint 0 as i.val
  let t := partitionPoint 0 as (i.val+1)
  have hu : u∈Icc (0:ℝ) 1 := partitionPoint_mem as ho i.val
  have ht : t∈Icc (0:ℝ) 1 := partitionPoint_mem as ho (i.val+1)
  have hut : u ≤ t := partitionPoint_mono as ho (Nat.le_succ i.val)
  have hR := comparisonSweepQuantile_monotone hc hk hkc hm hM α
  have hRut : R u ≤ R t := hR hut
  have hcellsub : uIcc (R u) (R t) ⊆ Icc (0:ℝ) 1 := by
    rw [uIcc_of_le hRut]
    exact Icc_subset_Icc (comparisonSweepQuantile_bounds hc hk hkc hm hM α u).1
      (comparisonSweepQuantile_bounds hc hk hkc hm hM α t).2
  have hAC : AbsolutelyContinuousOnInterval α.val.val (R u) (R t) :=
    ((inverseIntegralConstraints_lipschitz hm hM α.property).mono hcellsub).absolutelyContinuousOnInterval
  have hIB : IntegrableOn (fun r => deriv α.val.val r*B) (Ioc (R u) (R t)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hRut).mp hAC.intervalIntegrable_deriv).mul_const B
  have hFTC : (∫r in Ioc (R u) (R t), deriv α.val.val r*B)=(t-u)*B := by
    rw [←intervalIntegral.integral_of_le hRut, intervalIntegral.integral_mul_const,
      hAC.integral_deriv_eq_sub,
      comparisonSweepQuantile_mass_spec hc hk hkc hm hM α ht,
      comparisonSweepQuantile_mass_spec hc hk hkc hm hM α hu]
  have hnorm r : ‖w r‖ ≤ B := by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 r)]; exact hwb r
  have hI := comparison_radiusWeight_integrableOn hm hM α ha hz S hS hsub w hw hnorm
  have hGate : Integrable (S.indicator (fun r => deriv α.val.val r*w r)) :=
    hI.integrable_indicator hS
  have hpoint r (_ : r∈Ioc (R u) (R t)) :
      S.indicator (fun r => deriv α.val.val r*w r) r ≤ deriv α.val.val r*B := by
    by_cases hr : r∈S
    · rw [indicator_of_mem hr]
      exact mul_le_mul_of_nonneg_left (hwb r) α.val.property.2.deriv_nonneg
    · rw [indicator_of_notMem hr]
      exact mul_nonneg α.val.property.2.deriv_nonneg hB
  have hineq := setIntegral_mono_on hGate.integrableOn hIB measurableSet_Ioc hpoint
  rw [setIntegral_indicator hS, inter_comm, hFTC] at hineq
  have hmcell : t-u ≤ mesh := massPartition_point_next_mesh as hmesh i.isLt
  rw [←hi]
  change ((∫r in S ∩ Ioc (R u) (R t), deriv α.val.val r*w r).toNNReal:ℝ) ≤ mesh*B
  rw [Real.coe_toNNReal _ (integral_nonneg (fun r => mul_nonneg α.val.property.2.deriv_nonneg (hw0 r)))]
  exact hineq.trans (mul_le_mul_of_nonneg_right hmcell hB)

theorem comparisonRadiusBoundaryFilledTrace_eq_integral
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (d lam : ℝ) (b h : ℝ → ℝ) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {a z : ℝ} (ha : 0 < a) (hz : z ≤ 1)
    (S : Set ℝ) (hS : MeasurableSet S) (hsub : S ⊆ Ioo a z)
    (w : ℝ → ℝ) (hw : Measurable w) {B : ℝ}
    (hw0 : ∀r, 0 ≤ w r) (hwb : ∀r, ‖w r‖ ≤ B) :
    comparisonRadiusBoundaryFilledTrace hc hk hkc hm hM n dphys e d lam b h α as ho S w=
      ∫r in S, deriv α.val.val r*w r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α as ho := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let steps := sampleClockSteps q 0 as
  let hsteps : OrderedSteps 0 (steps++[]) := by
    simpa only [List.append_nil] using sampleClockSteps_ordered q _ ho
  let C := fun j => physicalRootedCapCellTrace n dphys e (q 0) steps [] hsteps j
  let x := fun j => R (partitionPoint 0 as j)
  have hlen : (comparisonRadiusBoundaryDurations hc hk hkc hm hM α as S w).length ≤ steps.length := by
    simp only [comparisonRadiusBoundaryDurations, radiusBoundaryDurations, List.length_ofFn,
      steps, sampleClockSteps_length, le_refl]
  have hI := comparison_radiusWeight_integrableOn hm hM α ha hz S hS hsub w hw hwb
  have hf0 r : 0 ≤ deriv α.val.val r*w r := mul_nonneg α.val.property.2.deriv_nonneg (hw0 r)
  have hC j (_ : j<as.length) : 0 ≤ C j := (physicalRootedCapCellTrace_mem_Icc n dphys e _ _ _ _ j).1
  have he := physicalRootedCapIndexedTrace_eq_weightedCellSum n dphys e (q 0)
    (comparisonRadiusBoundaryDurations hc hk hkc hm hM α as S w) steps [] hsteps hlen
  change comparisonRadiusBoundaryFilledTrace hc hk hkc hm hM n dphys e d lam b h α as ho S w=
    physicalWeightedCutSum (radiusBoundaryDurations x as.length S (fun r => deriv α.val.val r*w r)) C at he
  rw [he, radiusBoundaryDurations_filled_sum _ _ _ _ _ hI hf0]
  have hmeasure := cellDensityMeasure_weighted_integral as.length x C hC S hS
    (fun r => deriv α.val.val r*w r)
  simpa only [comparisonPhysicalRadiusMeasure, comparisonPhysicalRadiusDensity,
    physicalRadiusCellEnergyDensity, Nat.zero_add, radiusCellEnergyDensity_eq_finite_sum,
    R, bf, hf, q, steps, hsteps, C, x] using hmeasure.symm

theorem comparisonRadiusBoundarySquareEnergy_le_integral
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (d lam : ℝ) (b h : ℝ → ℝ) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    {a z : ℝ} (ha : 0 < a) (hz : z ≤ 1)
    (S : Set ℝ) (hS : MeasurableSet S) (hsub : S ⊆ Ioo a z)
    (w : ℝ → ℝ) (hw : Measurable w) {B : ℝ} (hB : 0 ≤ B)
    (hw0 : ∀r, 0 ≤ w r) (hwb : ∀r, w r ≤ B) :
    comparisonRadiusBoundarySquareEnergy hc hk hkc hm hM n dphys e d lam b h α as S w ≤
      2*(∫r in S, deriv α.val.val r*w r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α as ho)+2*(mesh*B) := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u => (b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u => (h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let q := completedPathClock (n+1) bf hf
  let steps := sampleClockSteps q 0 as
  let hsteps : OrderedSteps 0 (steps++[]) := by
    simpa only [List.append_nil] using sampleClockSteps_ordered q _ ho
  have hlen : (comparisonRadiusBoundaryDurations hc hk hkc hm hM α as S w).length ≤ steps.length := by
    simp only [comparisonRadiusBoundaryDurations, radiusBoundaryDurations, List.length_ofFn,
      steps, sampleClockSteps_length, le_refl]
  have hdur := comparisonRadiusBoundaryDurations_mesh hc hk hkc hm hM
    α as ho hmesh ha hz S hS hsub w hw hB hw0 hwb
  have ht := physicalWeightedCutSquareTrace_le_filled_and_mesh n dphys e (q 0)
    (comparisonRadiusBoundaryDurations hc hk hkc hm hM α as S w) steps [] hsteps hlen
    (mul_nonneg hmesh0 hB) hdur
  have ht' : comparisonRadiusBoundarySquareEnergy hc hk hkc hm hM n dphys e d lam b h α as S w ≤
      2*comparisonRadiusBoundaryFilledTrace hc hk hkc hm hM n dphys e d lam b h α as ho S w+
        2*(mesh*B) := by
    let F := fun ss : List (GaussianStep (FeatureIndex (n+1))) =>
      physicalWeightedCutSum (comparisonRadiusBoundaryDurations hc hk hkc hm hM α as S w)
        (fun j => ∫p, physicalCutSourceSquareTrace (n+1) ss id j p
          ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) (q 0) ss)
    change F (steps++[]) ≤ _ at ht
    have hsame : F (steps++[])=F steps := congrArg F (List.append_nil steps)
    exact (le_of_eq hsame.symm).trans ht
  have hnorm r : ‖w r‖ ≤ B := by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 r)]; exact hwb r
  rwa [comparisonRadiusBoundaryFilledTrace_eq_integral hc hk hkc hm hM
    n dphys e d lam b h α as ho ha hz S hS hsub w hw hw0 hnorm] at ht'

theorem comparisonPhysicalSelectedContactBoundarySquareTrace_eventually
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d)
    (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H : ℝ→ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r=0→
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hpartEnd : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z))

    (v0 : ℝ) (x : ℕ → ℝ) (K : ℕ) {δ width : ℝ}
    (hv0 : 0 ≤ v0) (hv1 : v0+width ≤ 1)
    (hstart : x 0=0) (hxend : x K=width) (hδ : 0 < δ) (hwidth : 2*δ ≤ width)
    (hx : ∀i : Fin K, x i.val < x (i.val+1))
    (hxb : ∀i≤K, x i∈Icc (0:ℝ) width)
    {ε : ℝ} (hε : 0 < ε) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    ∀ᶠ j in atTop,
      comparisonRadiusBoundarySquareEnergy hc hk hkc hm hM n dphys e d lam b h α (as j)
        (Ioo a z∩selectedContactCells H R (partitionPoint 0 (as j)) (as j).length)
        (sideSquareRadiusWeight R v0 x K δ width) ≤
      (108*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam z))*
        Real.log (width/δ)+ε := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let w := sideSquareRadiusWeight R v0 x K δ width
  let col := fun i : Fin K => sideSquareColumn x δ width i.val
  let B := ∑i : Fin K, col i
  let S := fun j => Ioo a z∩selectedContactCells H R (partitionPoint 0 (as j)) (as j).length
  have hcol i : 0 ≤ col i := sideSquareColumn_nonneg x hwidth i.val
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hcol i)
  have hw : Measurable w := finiteRadiusWeight_measurable _ _ _
  have hw0 r : 0 ≤ w r := finiteRadiusWeight_nonneg _ _ _ hcol r
  have hwb r : w r ≤ B := finiteRadiusWeight_le_sum _ _ _ hcol r
  have hS j : MeasurableSet (S j) := measurableSet_Ioo.inter
    (selectedContactCells_measurable H R (partitionPoint 0 (as j)) (as j).length)
  have hsub j : S j ⊆ Ioo a z := fun _ hr => hr.1
  have ht := comparisonPhysicalSelectedContactSideSquareTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero
    as mesh ho hpartEnd hmesh hmesh0 hlim ha haz hz Kb Kh hparent hfield
    v0 x K hv0 hv1 hstart hxend hδ hwidth hx hxb (show 0<ε/4 by linarith)
  have hlimB : Tendsto (fun j => 2*(mesh j*B)) atTop (𝓝 0) := by
    simpa only [zero_mul, mul_zero] using (hlim.mul_const B).const_mul 2
  have herr := (tendsto_order.mp hlimB).2 (ε/2) (by linarith : 0<ε/2)
  let budget := (54*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam z))*Real.log (width/δ)
  have hdouble : 2*budget=(108*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam z))*Real.log (width/δ) := by
    dsimp only [budget]
    ring
  filter_upwards [ht, herr] with j hj he
  have hn := comparisonRadiusBoundarySquareEnergy_le_integral hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j) (hmesh j) (hmesh0 j) ha hz
    (S j) (hS j) (hsub j) w hw hB hw0 hwb
  change (∫r in S j, deriv α.val.val r*w r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)) ≤ budget+ε/4 at hj
  rw [←hdouble]
  change comparisonRadiusBoundarySquareEnergy hc hk hkc hm hM n dphys e d lam b h α (as j) (S j) w ≤ 2*budget+ε
  linarith only [hn, hj, he]

theorem comparison_radiusBoundaryWeight_cell_eq_physicalMass
    {ι : Type} (q : ℝ → ι → ℝ≥0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (i : Fin as.length) (S : Set ℝ) (w : ℝ → ℝ) (C : ℝ)
    (hcell : Ioc
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val))
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i.val+1))) ⊆ S)
    (hconst : ∀r∈Ioc
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val))
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i.val+1))), w r=C) :
    (∫r in S ∩ Ioc
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val))
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i.val+1))),
      deriv α.val.val r*w r)=
      pathMassDifferences (sampleClockSteps q 0 as) 0
        ⟨i.val, by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt i.isLt⟩*C := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let u := partitionPoint 0 as i.val
  let v := partitionPoint 0 as (i.val+1)
  have hu : u∈Icc (0:ℝ) 1 := partitionPoint_mem as ho i.val
  have hv : v∈Icc (0:ℝ) 1 := partitionPoint_mem as ho (i.val+1)
  have huv : u ≤ v := partitionPoint_mono as ho (Nat.le_succ i.val)
  have hinter : S ∩ Ioc (R u) (R v)=Ioc (R u) (R v) := inter_eq_right.mpr hcell
  have hEq : (∫r in Ioc (R u) (R v), deriv α.val.val r*w r)=
      (∫r in Ioc (R u) (R v), deriv α.val.val r*C) := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    change deriv α.val.val r*w r = deriv α.val.val r*C
    rw [hconst r hr]
  have hFTC := (inverse_cell_weight_integral α.val.val R
    (inverseIntegralConstraints_lipschitz hm hM α.property)
    (comparisonSweepQuantile_monotone hc hk hkc hm hM α)
    (fun u _ => comparisonSweepQuantile_bounds hc hk hkc hm hM α u)
    (fun u hu => comparisonSweepQuantile_mass_spec hc hk hkc hm hM α hu) hu hv huv C).2
  have hIntegral : (∫r in Ioc (R u) (R v), deriv α.val.val r*C)=(v-u)*C := by
    rw [←integral_indicator measurableSet_Ioc]
    convert hFTC using 1
    apply integral_congr_ae
    exact ae_of_all _ (fun r => by
      by_cases hr : r∈Ioc (R u) (R v) <;> simp [hr])
  change (∫r in S ∩ Ioc (R u) (R v), deriv α.val.val r*w r)=_
  have hmEq : pathMassDifferences (sampleClockSteps q 0 as) 0
      ⟨i.val, by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt i.isLt⟩=v-u := by
    have h := pathMassDifferences_eq_cutMass (sampleClockSteps q 0 as) 0
      ⟨i.val, by simpa only [sampleClockSteps_length] using Nat.lt_succ_of_lt i.isLt⟩
    simpa only [Fin.val_mk,
      physicalCutMass_sampleClockSteps q 0 as (i.val+1) (by omega),
      physicalCutMass_sampleClockSteps q 0 as i.val i.isLt.le, u, v] using h
  rw [hinter, hEq, hIntegral]
  exact congrArg (fun y => y*C) hmEq.symm

end
end OAI.SKFluctuations.LaplaceWindowFormalization
