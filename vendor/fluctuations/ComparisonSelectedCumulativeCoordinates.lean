module

public import ComparisonSelectedCumulativeCompactness
public import ComparisonEffectiveCumulativeMass

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 1800000

theorem radiusCellEnergyDensity_zero_coefficients (R : ℝ→ℝ) (u : ℝ)
    (as : List PositiveMass) : radiusCellEnergyDensity R u as (fun _=>0)=(fun _=>0) := by
  induction as generalizing u with
  | nil=>rfl
  | cons a as ih=>
    funext r
    simp only [radiusCellEnergyDensity,indicator_zero,ih,add_zero]

theorem radiusCellEnergyDensity_prefix (R : ℝ→ℝ) (hR : Monotone R)
    {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as)
    (C : ℕ→ℝ) (m : ℕ) (r : ℝ) :
    radiusCellEnergyDensity R u as (fun i=>if i< m then C i else 0) r=
      (Iic (R (partitionPoint u as m))).indicator
        (radiusCellEnergyDensity R u as C) r := by
  induction as generalizing u C m with
  | nil=>simp [radiusCellEnergyDensity]
  | cons a as ih=>
    cases m with
    | zero=>
      simp only [Nat.not_lt_zero,ite_false,radiusCellEnergyDensity_zero_coefficients,
        partitionPoint,partitionValues_zero,id_eq]
      by_cases hr:r≤R u
      · rw [indicator_of_mem (show r∈Iic (R u) from hr)]
        exact (radiusCellEnergyDensity_eq_zero_of_le R hR (a::as) ho C hr).symm
      · rw [indicator_of_notMem (show r∉Iic (R u) from hr)]
    | succ m=>
      have haCut : R a.val≤R (partitionPoint a.val as m) :=
        hR (partitionPoint_mem as ho.2.2 m).1
      have htail : (fun i=>if i+1< m+1 then C (i+1) else 0)=
          (fun i=>if i< m then C (i+1) else 0) := by
        funext i
        simp
      simp only [radiusCellEnergyDensity,partitionPoint,partitionValues,
        Nat.zero_lt_succ,ite_true]
      rw [htail,ih ho.2.2]
      change _=(Iic (R (partitionPoint a.val as m))).indicator
        (fun t=>(Ioc (R u) (R a.val)).indicator (fun _=>C 0) t+
          radiusCellEnergyDensity R a.val as (fun i=>C (i+1)) t) r
      by_cases hr:r≤R (partitionPoint a.val as m)
      · simp only [indicator_of_mem (show r∈Iic (R (partitionPoint a.val as m)) from hr)]
      · have hnot:r∉Ioc (R u) (R a.val) := by
          intro hh
          exact hr (hh.2.trans haCut)
        simp only [indicator_of_notMem (show r∉Iic (R (partitionPoint a.val as m)) from hr),
          indicator_of_notMem hnot,add_zero]

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0< c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparison_selected_prefix_integral {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) (m : ℕ) :
    (∫r in Iic (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as m)),
      deriv α.val.val r*comparisonNativeUnitColumnWeight hc hk hkc hm hM
        q α as J (fun _=>(0:Fin 1)) (fun _=>1) r)=
    ∑i : Fin ((sampleClockSteps q 0 as).length+1),
      pathMassDifferences (sampleClockSteps q 0 as) 0 i*
        (if i∈J ∧ i.val< m then 1 else 0) := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let C := nativeSelectedColumn J (fun _=>(0:Fin 1)) (fun _=>1)
  have hfun : (fun r=>deriv α.val.val r*
      radiusCellEnergyDensity R 0 as (fun i=>if i< m then C i else 0) r)=
      (Iic (R (partitionPoint 0 as m))).indicator
        (fun r=>deriv α.val.val r*radiusCellEnergyDensity R 0 as C r) := by
    funext r
    rw [radiusCellEnergyDensity_prefix R
      (comparisonSweepQuantile_monotone hc hk hkc hm hM α) as ho C m]
    by_cases hr:r∈Iic (R (partitionPoint 0 as m)) <;> simp [hr]
  have hi := comparison_filled_coefficients_mass_radius_eq hc hk hkc hm hM α
    (show (0:ℝ)∈Icc (0:ℝ) 1 by simp) as ho (fun i=>if i< m then C i else 0)
  change (∫r,deriv α.val.val r*
    radiusCellEnergyDensity R 0 as (fun i=>if i< m then C i else 0) r)=
      massCellSum as 0 (fun i=>if i< m then C i else 0) at hi
  rw [hfun,integral_indicator measurableSet_Iic] at hi
  change (∫r in Iic (R (partitionPoint 0 as m)),
    deriv α.val.val r*radiusCellEnergyDensity R 0 as C r)=_
  rw [hi]
  have hs := sampled_mass_weight_sum q as 0 (fun i=>if i< m then C i else 0)
  simp only [he,sub_self,zero_mul,add_zero] at hs
  rw [←hs]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [C]
  rw [nativeSelectedColumn_atIndex]
  by_cases hJ:i∈J <;> by_cases hm:i.val< m <;> simp [hJ,hm]

theorem comparison_selected_cumulative_at_cut {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1))) (m : ℕ) :
    cumulativeCellMass (comparisonSelectedMassDensity hc hk hkc hm hM q α as J)
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as m))=
    ∑i : Fin ((sampleClockSteps q 0 as).length+1),
      pathMassDifferences (sampleClockSteps q 0 as) 0 i*
        (if i∈J ∧ i.val< m then 1 else 0) := by
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let cut := R (partitionPoint 0 as m)
  let w := comparisonNativeUnitColumnWeight hc hk hkc hm hM q α as J
    (fun _=>(0:Fin 1)) (fun _=>1)
  have hcut : cut∈Icc (0:ℝ) 1 := comparisonSweepQuantile_bounds hc hk hkc hm hM α _
  have hR0 : R 0=0 := by
    simpa only [α.property.1] using comparisonSweepQuantile_inverse hc hk hkc hm hM α
      (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)
  have heq : (Ioc (0:ℝ) cut).indicator
      (comparisonSelectedMassDensity hc hk hkc hm hM q α as J)=ᵐ[volume]
      (Iic cut).indicator (fun r=>deriv α.val.val r*w r) := by
    filter_upwards [volume.ae_ne (1:ℝ)] with r hr1
    by_cases hr:r≤cut
    · by_cases hr0:0< r
      · have hr01 : r∈Ioo (0:ℝ) 1 := ⟨hr0,lt_of_le_of_ne (hr.trans hcut.2) hr1⟩
        simp only [indicator_of_mem (show r∈Ioc (0:ℝ) cut from ⟨hr0,hr⟩),
          indicator_of_mem (show r∈Iic cut from hr),comparisonSelectedMassDensity,indicator_of_mem hr01]
        rfl
      · have hnot:r∉Ioc (0:ℝ) cut := fun hh=>hr0 hh.1
        have hw0:w r=0 := by
          apply radiusCellEnergyDensity_eq_zero_of_le R
            (comparisonSweepQuantile_monotone hc hk hkc hm hM α) as ho
          rw [hR0]
          exact le_of_not_gt hr0
        simp only [indicator_of_notMem hnot,indicator_of_mem (show r∈Iic cut from hr),hw0,mul_zero]
    · have hnot:r∉Ioc (0:ℝ) cut := fun hh=>hr hh.2
      simp only [indicator_of_notMem hnot,indicator_of_notMem (show r∉Iic cut from hr)]
  calc
    _=(∫r in Iic cut,deriv α.val.val r*w r) := by
      rw [cumulativeCellMass,intervalIntegral.integral_of_le hcut.1,
        ←integral_indicator measurableSet_Ioc,←integral_indicator measurableSet_Iic]
      exact integral_congr_ae heq
    _=_ := comparison_selected_prefix_integral hc hk hkc hm hM q α as ho he J m

theorem comparison_selected_contact_coordinate_eq_cumulative {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1)→Fin K) (x : ℕ→ℝ)
    (h0:x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass (sampleClockSteps q 0 as) J unit u=
      x (u.val+1)-x u.val)
    (horder : MonotoneOn unit (J:Set (Fin ((sampleClockSteps q 0 as).length+1))))
    (i : Fin ((sampleClockSteps q 0 as).length+1)) (hi:i∈J)
    (hsingle : ∀j∈J,unit j=unit i→j=i) :
    x (unit i).val=cumulativeCellMass
      (comparisonSelectedMassDensity hc hk hkc hm hM q α as J)
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val)) := by
  rw [comparison_selected_cumulative_at_cut hc hk hkc hm hM q α as ho he J]
  simpa only [Fin.lt_def] using
    WholeUnitSideKernel.selected_effective_contact_coordinate_eq_mass_before_row
      (sampleClockSteps q 0 as) J unit x h0 hmass horder i hi hsingle

theorem cumulativeCellMass_monotoneOn (g : ℝ→ℝ)
    (hi : IntegrableOn g (Icc (0:ℝ) 1)) (h0 : ∀r∈Icc (0:ℝ) 1,0≤g r) :
    MonotoneOn (cumulativeCellMass g) (Icc (0:ℝ) 1) := by
  intro r hr s hs hrs
  have hir : IntervalIntegrable g volume 0 r :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hr.1).mpr
      (hi.mono_set (Icc_subset_Icc le_rfl hr.2))
  have his : IntervalIntegrable g volume 0 s :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hs.1).mpr
      (hi.mono_set (Icc_subset_Icc le_rfl hs.2))
  rw [←sub_nonneg,cumulativeCellMass,cumulativeCellMass,
    intervalIntegral.integral_interval_sub_left his hir]
  exact intervalIntegral.integral_nonneg hrs
    (fun t ht=>h0 t ⟨hr.1.trans ht.1,ht.2.trans hs.2⟩)

theorem selected_unit_prefix_bracket {ι : Type} {K : ℕ}
    (steps : List (GaussianStep ι)) (ha : OrderedSteps 0 steps)
    (J : Finset (Fin (steps.length+1))) (unit : Fin (steps.length+1)→Fin K)
    (x : ℕ→ℝ) (h0:x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass steps J unit u=x (u.val+1)-x u.val)
    (horder : MonotoneOn unit (J:Set (Fin (steps.length+1))))
    (i : Fin (steps.length+1)) (hi:i∈J) :
    x (unit i).val≤∑j : Fin (steps.length+1),pathMassDifferences steps 0 j*
      (if j∈J ∧ j.val< i.val then 1 else 0) ∧
    (∑j : Fin (steps.length+1),pathMassDifferences steps 0 j*
      (if j∈J ∧ j.val< i.val+1 then 1 else 0))≤x ((unit i).val+1) := by
  have hx0 := WholeUnitSideKernel.selected_effective_coordinate_eq_mass_before_unit
    steps J unit x h0 hmass (unit i)
  have hm0 := pathMassDifferences_nonneg steps ha
  constructor
  · rw [hx0]
    apply Finset.sum_le_sum
    intro j _
    by_cases hJ:j∈J
    · by_cases hu:unit j< unit i
      · have hji:j< i := by
          by_contra hh
          exact (not_le_of_gt hu) (horder hi hJ (le_of_not_gt hh))
        simp only [hJ,hu,Fin.lt_def.mp hji,and_self,ite_true]
        exact le_rfl
      · simp only [hJ,hu,and_false,ite_false,mul_zero]
        split_ifs <;> simp [hm0 j]
    · simp [hJ]
  · have hx1 : x ((unit i).val+1)=x (unit i).val+
        physicalSelectedUnitMass steps J unit (unit i) := by linarith [hmass (unit i)]
    rw [hx1,hx0,physicalSelectedUnitMass,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases hJ:j∈J
    · by_cases hji:j.val< i.val+1
      · have hu:unit j≤unit i := horder hJ hi (Fin.le_def.mpr (by omega))
        rcases lt_or_eq_of_le hu with hu|hu
        · have hne:unit j≠unit i := ne_of_lt hu
          simp [hJ,hji,hu,hne]
        · simp [hJ,hji,hu]
      · simp only [hJ,hji,and_false,ite_false,mul_zero]
        apply add_nonneg
        · split_ifs <;> simp [hm0 j]
        · split_ifs <;> first | exact hm0 j | exact le_rfl
    · simp [hJ]

theorem comparison_selected_cumulative_mem_unit_interval {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1)→Fin K) (x : ℕ→ℝ)
    (h0:x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass (sampleClockSteps q 0 as) J unit u=
      x (u.val+1)-x u.val)
    (horder : MonotoneOn unit (J:Set (Fin ((sampleClockSteps q 0 as).length+1))))
    (i : Fin ((sampleClockSteps q 0 as).length+1)) (hi:i∈J) {r : ℝ}
    (hr : r∈Ioc
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as i.val))
      (comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 as (i.val+1)))) :
    cumulativeCellMass (comparisonSelectedMassDensity hc hk hkc hm hM q α as J) r∈
      Icc (x (unit i).val) (x ((unit i).val+1)) := by
  have hprefix := selected_unit_prefix_bracket (sampleClockSteps q 0 as)
    (sampleClockSteps_ordered q as ho) J unit x h0 hmass horder i hi
  rw [←comparison_selected_cumulative_at_cut hc hk hkc hm hM q α as ho he J i.val,
    ←comparison_selected_cumulative_at_cut hc hk hkc hm hM q α as ho he J (i.val+1)] at hprefix
  have hlo := comparisonSweepQuantile_bounds hc hk hkc hm hM α (partitionPoint 0 as i.val)
  have hhi := comparisonSweepQuantile_bounds hc hk hkc hm hM α (partitionPoint 0 as (i.val+1))
  have hr01 : r∈Icc (0:ℝ) 1 := ⟨(hlo.1.trans_lt hr.1).le,hr.2.trans hhi.2⟩
  have hmono := cumulativeCellMass_monotoneOn _
    (comparisonSelectedMassDensity_integrable hc hk hkc hm hM q α as ho J)
    (fun t _=>(comparisonSelectedMassDensity_mem_Icc hc hk hkc hm hM q α as ho J t).1)
  exact ⟨hprefix.1.trans (hmono hlo hr01 hr.1.le),
    (hmono hr01 hhi hr.2).trans hprefix.2⟩

end
end OAI.SKFluctuations.LaplaceWindowFormalization
