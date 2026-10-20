module

public import ComparisonNativeUnitColumns
public import ComparisonContactBoundaryTransport
public import ComparisonSelectedCutTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped BigOperators NNReal ENNReal Topology
set_option maxHeartbeats 1800000

theorem radiusCellEnergyDensity_mul (R : ℝ → ℝ) (hR : Monotone R)
    {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as)
    (C D : ℕ → ℝ) (r : ℝ) :
    radiusCellEnergyDensity R u as C r*radiusCellEnergyDensity R u as D r=
      radiusCellEnergyDensity R u as (fun j=>C j*D j) r := by
  induction as generalizing u C D with
  | nil => simp [radiusCellEnergyDensity]
  | cons a as ih =>
    by_cases hr : r∈Ioc (R u) (R a.val)
    · simp only [radiusCellEnergyDensity,indicator_of_mem hr,
        radiusCellEnergyDensity_eq_zero_of_le R hR as ho.2.2 _ hr.2,add_zero]
    · simp only [radiusCellEnergyDensity,indicator_of_notMem hr,zero_add]
      exact ih ho.2.2 _ _

def nativeWeightedSquareEnergy (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0)
    {K : ℕ} (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (col : Fin K → ℝ) : ℝ :=
  ∑i,pathMassDifferences steps 0 i*nativeSelectedColumn J unit col i.val*
    ∫p,physicalCutSourceSquareTrace n steps id i.val p
      ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps

def nativeWeightedCovarianceEnergy (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0)
    {K : ℕ} (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (col : Fin K → ℝ) : ℝ :=
  ∑i,pathMassDifferences steps 0 i*nativeSelectedColumn J unit col i.val*
    actualCutCovarianceEnergy n steps q0 i.val

def nativeWeightedCutDurations {ι : Type} (steps : List (GaussianStep ι))
    {K : ℕ} (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (col : Fin K → ℝ) : List ℝ≥0 :=
  List.ofFn (fun i : Fin steps.length=>
    (pathMassDifferences steps 0 i.castSucc*nativeSelectedColumn J unit col i.val).toNNReal)

theorem nativeSelectedColumn_energy_grouping (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0)
    {K : ℕ} (J : Finset (Fin (steps.length+1)))
    (unit : Fin (steps.length+1) → Fin K) (col : Fin K → ℝ) :
    (∑u,physicalSelectedUnitEnergy n steps q0 J unit u*col u)=
      ∑i,pathMassDifferences steps 0 i*nativeSelectedColumn J unit col i.val*
        ∫p,physicalCutSusceptibility n steps id i.val p
          ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps := by
  unfold physicalSelectedUnitEnergy
  simp only [Finset.sum_mul,ite_mul,zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [nativeSelectedColumn_atIndex]
  by_cases hi : i∈J
  · simp only [hi,true_and,ite_true]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ,ite_true]
    ring
  · simp only [hi,false_and,ite_false,Finset.sum_const_zero,mul_zero,zero_mul]

theorem nativeWeightedCovarianceEnergy_le_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) {K : ℕ}
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → Fin K)
    (col : Fin K → ℝ) (hcol : ∀u,0 ≤ col u)
    {a : ℝ} (ha0 : 0<a) (hcut : ∀i∈J,a ≤ physicalCutMass 0 steps i.val) :
    nativeWeightedCovarianceEnergy n steps q0 J unit col ≤ 
      nativeWeightedSquareEnergy n steps q0 J unit col/a^2 := by
  unfold nativeWeightedCovarianceEnergy nativeWeightedSquareEnergy
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i∈J
  · have h := physicalCutSpinTraceCovSq_integral_le_square_of_cutMass n steps ha ha0
      (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id i.val (hcut i hi)
    try simp only [←rootedHierarchyPathLaw_eq_physical] at h
    have hw : 0 ≤ pathMassDifferences steps 0 i*nativeSelectedColumn J unit col i.val :=
      mul_nonneg (pathMassDifferences_nonneg steps ha i)
        (nativeSelectedColumn_nonneg J unit col hcol i.val)
    simpa only [actualCutCovarianceEnergy,mul_div_assoc,rootedHierarchyPathLaw,Kernel.comap_id]
      using mul_le_mul_of_nonneg_left h hw
  · simp only [nativeSelectedColumn_atIndex,hi,ite_false,mul_zero,zero_mul,zero_div,le_refl]

theorem nativeWeightedUnitEnergy_le_square (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) {K : ℕ}
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → Fin K)
    (col : Fin K → ℝ) (hcol : ∀u,0 ≤ col u)
    {a : ℝ} (ha0 : 0<a) (hcut : ∀i∈J,a ≤ physicalCutMass 0 steps i.val) :
    (∑u,physicalSelectedUnitEnergy n steps q0 J unit u*col u) ≤ 
      nativeWeightedSquareEnergy n steps q0 J unit col/a := by
  rw [nativeSelectedColumn_energy_grouping]
  unfold nativeWeightedSquareEnergy
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i∈J
  · have h := physicalCutSusceptibility_integral_le_square_of_cutMass n steps ha ha0
      (Measure.pi fun k=>gaussianReal 0 (q0 k)) id measurable_id i.val (hcut i hi)
    try simp only [←rootedHierarchyPathLaw_eq_physical] at h
    have hw : 0 ≤ pathMassDifferences steps 0 i*nativeSelectedColumn J unit col i.val :=
      mul_nonneg (pathMassDifferences_nonneg steps ha i)
        (nativeSelectedColumn_nonneg J unit col hcol i.val)
    simpa only [mul_div_assoc,rootedHierarchyPathLaw,Kernel.comap_id]
      using mul_le_mul_of_nonneg_left h hw
  · simp only [nativeSelectedColumn_atIndex,hi,ite_false,mul_zero,zero_mul,zero_div,le_refl]

theorem nativeWeightedSquareEnergy_eq_weightedCuts (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex n → ℝ≥0) {K : ℕ}
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → Fin K)
    (col : Fin K → ℝ) (hcol : ∀u,0 ≤ col u)
    (hlast : pathMassDifferences steps 0 (Fin.last steps.length)=0) :
    nativeWeightedSquareEnergy n steps q0 J unit col=
      physicalWeightedCutSum (nativeWeightedCutDurations steps J unit col) (fun k=>
        ∫p,physicalCutSourceSquareTrace n steps id k p
          ∂rootedHierarchyPathLaw (uniformWeight n) (finiteFeature n) q0 steps) := by
  unfold nativeWeightedSquareEnergy nativeWeightedCutDurations
  rw [Fin.sum_univ_castSucc,hlast,zero_mul,zero_mul,add_zero,contactWeightedCutSum_ofFn]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.coe_toNNReal _ (mul_nonneg (pathMassDifferences_nonneg steps ha i.castSucc)
    (nativeSelectedColumn_nonneg J unit col hcol i.val))]
  rfl

theorem nativeWeightedSquareEnergy_le_filled_and_mesh (n dphys : ℕ)
    (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (steps : List (GaussianStep (FeatureIndex (n+1)))) (ha : OrderedSteps 0 steps)
    (q0 : FeatureIndex (n+1) → ℝ≥0) {K : ℕ}
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1) → Fin K)
    (col : Fin K → ℝ) (hcol : ∀u,0 ≤ col u)
    (hlast : pathMassDifferences steps 0 (Fin.last steps.length)=0)
    {mesh B : ℝ} (hm : 0 ≤ mesh) (hB : 0 ≤ B)
    (hmass : ∀i : Fin steps.length,pathMassDifferences steps 0 i.castSucc ≤ mesh)
    (hbound : ∀u,col u ≤ B) :
    nativeWeightedSquareEnergy (n+1) steps q0 J unit col ≤ 
      2*zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q0 k))
        (physicalFiniteCapIndexedTrace n dphys e
          (nativeWeightedCutDurations steps J unit col) steps [] (a := 0) (by simpa using ha)) 0+
        2*(mesh*B) := by
  rw [nativeWeightedSquareEnergy_eq_weightedCuts (n+1) steps ha q0 J unit col hcol hlast]
  have hlen : (nativeWeightedCutDurations steps J unit col).length ≤ steps.length := by
    simp only [nativeWeightedCutDurations,List.length_ofFn,le_refl]
  have hdur : ∀w∈nativeWeightedCutDurations steps J unit col,(w:ℝ) ≤ mesh*B := by
    intro w hw
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hw
    rw [←hi,Real.coe_toNNReal _ (mul_nonneg (pathMassDifferences_nonneg steps ha i.castSucc)
      (nativeSelectedColumn_nonneg J unit col hcol i.val))]
    have hc : nativeSelectedColumn J unit col i.val ≤ B := by
      rw [show i.val=i.castSucc.val from rfl,nativeSelectedColumn_atIndex]
      split_ifs
      · exact hbound _
      · exact hB
    exact mul_le_mul (hmass i) hc (nativeSelectedColumn_nonneg J unit col hcol i.val) hm
  have ht := physicalWeightedCutSquareTrace_le_filled_and_mesh n dphys e q0
    (nativeWeightedCutDurations steps J unit col) steps [] (by simpa using ha)
    hlen (mul_nonneg hm hB) hdur
  let F := fun ss : List (GaussianStep (FeatureIndex (n+1)))=>
    physicalWeightedCutSum (nativeWeightedCutDurations steps J unit col) (fun k=>
      ∫p,physicalCutSourceSquareTrace (n+1) ss id k p
        ∂rootedHierarchyPathLaw (uniformWeight (n+1)) (finiteFeature (n+1)) q0 ss)
  change F (steps++[]) ≤ _ at ht
  have hsame := congrArg F (List.append_nil steps)
  exact (le_of_eq hsame.symm).trans ht

theorem selectedCellMass_sum_eq_biUnion {ι : Type}
    (steps : List (GaussianStep ι)) {B : ℕ}
    (J : Fin B → Finset (Fin (steps.length+1)))
    (hdisjoint : Pairwise (fun b c=>Disjoint (J b) (J c)))
    (i : Fin (steps.length+1)) :
    (∑b,WholeUnitSideKernel.physicalSelectedCellMass steps (J b) i)=
      WholeUnitSideKernel.physicalSelectedCellMass steps (Finset.univ.biUnion J) i := by
  by_cases hu : i∈Finset.univ.biUnion J
  · obtain ⟨b,_,hib⟩ := Finset.mem_biUnion.mp hu
    have hs : (∑c,WholeUnitSideKernel.physicalSelectedCellMass steps (J c) i)=
        WholeUnitSideKernel.physicalSelectedCellMass steps (J b) i := by
      apply Finset.sum_eq_single b
      · intro c _ hcb
        have hic : i∉J c := fun hic=>Finset.disjoint_left.mp (hdisjoint hcb) hic hib
        simp only [WholeUnitSideKernel.physicalSelectedCellMass,hic,ite_false]
      · simp
    rw [hs]
    simp only [WholeUnitSideKernel.physicalSelectedCellMass,hib,hu,ite_true]
  · have hn b : i∉J b := fun hi=>hu (Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ _,hi⟩)
    simp only [WholeUnitSideKernel.physicalSelectedCellMass,hn,hu,ite_false,Finset.sum_const_zero]

theorem nativeWeightedCovarianceEnergy_one (n : ℕ)
    (steps : List (GaussianStep (FeatureIndex n))) (q0 : FeatureIndex n → ℝ≥0)
    (J : Finset (Fin (steps.length+1))) :
    nativeWeightedCovarianceEnergy n steps q0 J (fun _=>(0:Fin 1)) (fun _=>1)=
      ∑i,WholeUnitSideKernel.physicalSelectedCellMass steps J i*
        actualCutCovarianceEnergy n steps q0 i.val := by
  unfold nativeWeightedCovarianceEnergy
  apply Finset.sum_congr rfl
  intro i _
  rw [nativeSelectedColumn_atIndex]
  by_cases hi : i∈J <;>
    simp only [WholeUnitSideKernel.physicalSelectedCellMass,hi,ite_true,ite_false,mul_one,
      mul_zero,zero_mul]

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def comparisonNativeCompletedClock (n : ℕ) (d lam : ℝ) (b h : ℝ → ℝ)
    (α : inverseIntegralConstraints 0 0 k M) : ℝ → FeatureIndex (n+1) → ℝ≥0 :=
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  completedPathClock (n+1)
    (fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal)
    (fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal)

theorem sampled_terminal_mass_zero {ι : Type} (q : ℝ → ι → ℝ≥0)
    (as : List PositiveMass) (he : partitionEnd 0 as=1) :
    pathMassDifferences (sampleClockSteps q 0 as) 0
      (Fin.last (sampleClockSteps q 0 as).length)=0 := by
  have hlast (ss : List (GaussianStep ι)) (u : ℝ) :
      pathMassDifferences ss u (Fin.last ss.length)=1-physicalCutMass u ss ss.length := by
    induction ss generalizing u with
    | nil => rfl
    | cons a ss ih =>
      simpa only [pathMassDifferences,←Fin.succ_last,Fin.cons_succ,List.length_cons,
        physicalCutMass] using ih a.1
  rw [hlast]
  simp only [sampleClockSteps_length]
  rw [physicalCutMass_sampleClockSteps q 0 as as.length le_rfl,partitionPoint_length,he,sub_self]

def nativeWeightedFilledTrace (n dphys : ℕ)
    (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (q : ℝ → FeatureIndex (n+1) → ℝ≥0) (as : List PositiveMass)
    (ho : MassOrdered 0 as) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1) → Fin K) (col : Fin K → ℝ) : ℝ :=
  zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q 0 k))
    (physicalFiniteCapIndexedTrace n dphys e
      (nativeWeightedCutDurations (sampleClockSteps q 0 as) J unit col)
      (sampleClockSteps q 0 as) [] (a := 0) (by simpa using sampleClockSteps_ordered q _ ho)) 0

theorem comparisonNativeUnitColumnWeight_filled_integral
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (d lam : ℝ) (b h : ℝ → ℝ) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1)))
    (unit : Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1) → Fin K)
    (col : Fin K → ℝ) (hcol : ∀u,0 ≤ col u) :
    nativeWeightedFilledTrace n dphys e
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) as ho J unit col=
      ∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) α as J unit col r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α as ho := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
  let steps := sampleClockSteps q 0 as
  let ha : OrderedSteps 0 (steps++[]) := by simpa using sampleClockSteps_ordered q _ ho
  let C := fun j=>physicalRootedCapCellTrace n dphys e (q 0) steps [] ha j
  let D := nativeSelectedColumn J unit col
  have hR := comparisonSweepQuantile_monotone hc hk hkc hm hM α
  have hC r : 0 ≤ radiusCellEnergyDensity R 0 as C r :=
    (radiusCellEnergyDensity_mem_Icc R hR as ho C
      (fun j=>physicalRootedCapCellTrace_mem_Icc n dphys e (q 0) steps [] ha j) r).1
  have hmeasure :
      (∫r,deriv α.val.val r*radiusCellEnergyDensity R 0 as D r
        ∂volume.withDensity (fun r=>ENNReal.ofReal (radiusCellEnergyDensity R 0 as C r)))=
      ∫r,deriv α.val.val r*radiusCellEnergyDensity R 0 as (fun j=>D j*C j) r := by
    rw [integral_withDensity_eq_integral_toReal_smul
      (radiusCellEnergyDensity_measurable R 0 as C).ennreal_ofReal
      (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    exact ae_of_all _ (fun r=>by
      change (ENNReal.ofReal (radiusCellEnergyDensity R 0 as C r)).toReal*
        (deriv α.val.val r*radiusCellEnergyDensity R 0 as D r)=
        deriv α.val.val r*radiusCellEnergyDensity R 0 as (fun j=>D j*C j) r
      rw [ENNReal.toReal_ofReal (hC r),←radiusCellEnergyDensity_mul R hR as ho D C r]
      ring)
  have hmass := comparison_filled_coefficients_mass_radius_eq hc hk hkc hm hM
    α (show (0:ℝ)∈Icc (0:ℝ) 1 by simp) as ho (fun j=>D j*C j)
  have hs := sampled_mass_weight_sum q as 0 (fun j=>D j*C j)
  simp only [he,sub_self,zero_mul,add_zero] at hs
  have htrace := physicalRootedCapIndexedTrace_eq_weightedCellSum n dphys e (q 0)
    (nativeWeightedCutDurations steps J unit col) steps [] ha (by
      simp only [nativeWeightedCutDurations,List.length_ofFn,le_refl])
  change nativeWeightedFilledTrace n dphys e q as ho J unit col=
    physicalWeightedCutSum (nativeWeightedCutDurations steps J unit col) C at htrace
  rw [htrace,nativeWeightedCutDurations,contactWeightedCutSum_ofFn]
  have hmassEq :
      (∑i : Fin steps.length,pathMassDifferences steps 0 i.castSucc*D i.val*C i.val)=
      massCellSum as 0 (fun j=>D j*C j) := by
    rw [←hs,Fin.sum_univ_castSucc,sampled_terminal_mass_zero q as he]
    simp only [zero_mul,add_zero]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_castSucc]
    change pathMassDifferences steps 0 i.castSucc*D i.val*C i.val=
      pathMassDifferences steps 0 i.castSucc*(D i.val*C i.val)
    ring
  have hl : (∑i : Fin steps.length,
      ((pathMassDifferences steps 0 i.castSucc*D i.val).toNNReal:ℝ)*C i.val)=
      massCellSum as 0 (fun j=>D j*C j) := by
    calc
      _ = ∑i : Fin steps.length,pathMassDifferences steps 0 i.castSucc*D i.val*C i.val := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Real.coe_toNNReal _ (mul_nonneg
          (pathMassDifferences_nonneg steps (sampleClockSteps_ordered q _ ho) i.castSucc)
          (nativeSelectedColumn_nonneg J unit col hcol i.val))]
      _ = _ := hmassEq
  rw [hl]
  have hr := hmeasure.trans hmass
  simpa only [comparisonNativeUnitColumnWeight,comparisonPhysicalRadiusMeasure,
    comparisonPhysicalRadiusDensity,physicalRadiusCellEnergyDensity,Nat.zero_add,
    comparisonNativeCompletedClock,R,q,steps,ha,C,D] using hr.symm

theorem comparison_nativeCutMass_lowerRadius {ι : Type}
    (q : ℝ → ι → ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    {a : ℝ} (hleft : ∀i∈J,a ≤ comparisonSweepQuantile hc hk hkc hm hM α
      (partitionPoint 0 as i.val)) :
    ∀i∈J,α.val.val a ≤ physicalCutMass 0 (sampleClockSteps q 0 as) i.val := by
  intro i hi
  have hu := partitionPoint_mem as ho i.val
  have h := α.val.property.2 (hleft i hi)
  rw [comparisonSweepQuantile_mass_spec hc hk hkc hm hM α hu] at h
  rw [physicalCutMass_sampleClockSteps q 0 as i.val (by
    have hii := i.isLt
    simp only [sampleClockSteps_length] at hii
    omega)]
  exact h

theorem comparisonNativeWeightedSquareEnergy_le_integral
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (d lam : ℝ) (b h : ℝ → ℝ) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1)))
    (unit : Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1) → Fin K)
    (col : Fin K → ℝ) (hcol : ∀u,0 ≤ col u) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀u,col u ≤ B) :
    let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
    nativeWeightedSquareEnergy (n+1) (sampleClockSteps q 0 as) (q 0) J unit col ≤ 
      2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        q α as J unit col r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α as ho)+2*(mesh*B) := by
  dsimp only
  let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
  let steps := sampleClockSteps q 0 as
  have ha := sampleClockSteps_ordered q _ ho
  have hmass (i : Fin steps.length) : pathMassDifferences steps 0 i.castSucc ≤ mesh := by
    have hi : i.val<as.length := by simpa only [steps,sampleClockSteps_length] using i.isLt
    have heq := pathMassDifferences_eq_cutMass steps 0 i.castSucc
    simp only [Fin.val_castSucc,steps,
      physicalCutMass_sampleClockSteps q 0 as i.val (Nat.le_of_lt hi),
      physicalCutMass_sampleClockSteps q 0 as (i.val+1) (by omega)] at heq
    rw [heq]
    exact massPartition_point_next_mesh as hmesh hi
  have ht := nativeWeightedSquareEnergy_le_filled_and_mesh n dphys e steps ha (q 0)
    J unit col hcol (sampled_terminal_mass_zero q as he) hmesh0 hB hmass hbound
  change _ ≤ 2*nativeWeightedFilledTrace n dphys e q as ho J unit col+2*(mesh*B) at ht
  rwa [comparisonNativeUnitColumnWeight_filled_integral hc hk hkc hm hM
    n dphys e d lam b h α as ho he J unit col hcol] at ht

theorem comparisonNativeWeightedCovarianceEnergy_le_integral
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (d lam : ℝ) (b h : ℝ → ℝ) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1)))
    (unit : Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1) → Fin K)
    (col : Fin K → ℝ) (hcol : ∀u,0 ≤ col u) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀u,col u ≤ B) {a : ℝ} (ha : 0<a) (ha1 : a ≤ 1)
    (hleft : ∀i∈J,a ≤ comparisonSweepQuantile hc hk hkc hm hM α
      (partitionPoint 0 as i.val)) :
    let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
    nativeWeightedCovarianceEnergy (n+1) (sampleClockSteps q 0 as) (q 0) J unit col ≤ 
      (2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        q α as J unit col r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α as ho)+2*(mesh*B))/(α.val.val a)^2 := by
  dsimp only
  let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
  have hαa : 0<α.val.val a := by
    have ht := inverseConstraint_strictMonoOn hc hk hkc α.property
      (show (0:ℝ)∈Icc (0:ℝ) 1 by simp) ⟨ha.le,ha1⟩ ha
    simpa only [α.property.1] using ht
  have hcutt := comparison_nativeCutMass_lowerRadius hc hk hkc hm hM q α as ho J hleft
  have hCov := nativeWeightedCovarianceEnergy_le_square (n+1) (sampleClockSteps q 0 as)
    (sampleClockSteps_ordered q _ ho) (q 0) J unit col hcol hαa hcutt
  have hs := comparisonNativeWeightedSquareEnergy_le_integral hc hk hkc hm hM
    n dphys e d lam b h α as ho he hmesh hmesh0 J unit col hcol hB hbound
  exact hCov.trans (div_le_div_of_nonneg_right hs (sq_nonneg _))

theorem comparisonNativeWeightedUnitEnergy_le_integral
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (d lam : ℝ) (b h : ℝ → ℝ) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1)))
    (unit : Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1) → Fin K)
    (col : Fin K → ℝ) (hcol : ∀u,0 ≤ col u) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀u,col u ≤ B) {a : ℝ} (ha : 0<a) (ha1 : a ≤ 1)
    (hleft : ∀i∈J,a ≤ comparisonSweepQuantile hc hk hkc hm hM α
      (partitionPoint 0 as i.val)) :
    let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
    (∑u,physicalSelectedUnitEnergy (n+1) (sampleClockSteps q 0 as) (q 0) J unit u*col u) ≤ 
      (2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        q α as J unit col r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α as ho)+2*(mesh*B))/α.val.val a := by
  dsimp only
  let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
  have hαa : 0<α.val.val a := by
    have ht := inverseConstraint_strictMonoOn hc hk hkc α.property
      (show (0:ℝ)∈Icc (0:ℝ) 1 by simp) ⟨ha.le,ha1⟩ ha
    simpa only [α.property.1] using ht
  have hcutt := comparison_nativeCutMass_lowerRadius hc hk hkc hm hM q α as ho J hleft
  have hUnit := nativeWeightedUnitEnergy_le_square (n+1) (sampleClockSteps q 0 as)
    (sampleClockSteps_ordered q _ ho) (q 0) J unit col hcol hαa hcutt
  have hs := comparisonNativeWeightedSquareEnergy_le_integral hc hk hkc hm hM
    n dphys e d lam b h α as ho he hmesh hmesh0 J unit col hcol hB hbound
  exact hUnit.trans (div_le_div_of_nonneg_right hs hαa.le)

theorem comparisonNativeSelectedUnionCovarianceEnergy_le_integral
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (d lam : ℝ) (b h : ℝ → ℝ) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    {B : ℕ}
    (J : Fin B → Finset (Fin ((sampleClockSteps
      (comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α) 0 as).length+1)))
    (hdisjoint : Pairwise (fun b c=>Disjoint (J b) (J c)))
    {a : ℝ} (ha : 0<a) (ha1 : a ≤ 1)
    (hleft : ∀b,∀i∈J b,a ≤ comparisonSweepQuantile hc hk hkc hm hM α
      (partitionPoint 0 as i.val)) :
    let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
    (∑i,(∑b,WholeUnitSideKernel.physicalSelectedCellMass (sampleClockSteps q 0 as) (J b) i)*
      actualCutCovarianceEnergy (n+1) (sampleClockSteps q 0 as) (q 0) i.val) ≤
      (2*(∫r,deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        q α as (Finset.univ.biUnion J) (fun _=>(0:Fin 1)) (fun _=>1) r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α as ho)+2*mesh)/(α.val.val a)^2 := by
  dsimp only
  let q := comparisonNativeCompletedClock hc hk hkc hm hM n d lam b h α
  have hfloor : ∀i∈Finset.univ.biUnion J,
      a ≤ comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val) := by
    intro i hi
    obtain ⟨bb,_,hbb⟩ := Finset.mem_biUnion.mp hi
    exact hleft bb i hbb
  have ht := comparisonNativeWeightedCovarianceEnergy_le_integral hc hk hkc hm hM
    n dphys e d lam b h α as ho he hmesh hmesh0 (Finset.univ.biUnion J)
    (fun _=>(0:Fin 1)) (fun _=>1) (fun _=>by norm_num) (show (0:ℝ) ≤ 1 by norm_num)
    (fun _=>le_rfl) ha ha1 hfloor
  dsimp only at ht
  rw [nativeWeightedCovarianceEnergy_one] at ht
  simp only [mul_one] at ht
  simp_rw [selectedCellMass_sum_eq_biUnion _ J hdisjoint]
  exact ht

end
end OAI.SKFluctuations.LaplaceWindowFormalization
