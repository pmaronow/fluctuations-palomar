module

public import ComparisonShiftedNativeBandCarrier
public import ComparisonNativeCovarianceTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000
attribute [local instance] Classical.propDecidable

namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem original_coefficients_mass_radius_eq {u : ℝ}
    (as : List PositiveMass) (ho : MassOrdered u as) (C : ℕ→ℝ)
    (hhigh : ∀i,C i≠0 → m.u0≤partitionPoint u as i) :
    Integrable (fun r=>deriv m.alpha.val.val r*radiusCellEnergyDensity m.R u as C r) ∧
    (∫r,deriv m.alpha.val.val r*radiusCellEnergyDensity m.R u as C r)=massCellSum as u C := by
  induction as generalizing u C with
  | nil => simp [radiusCellEnergyDensity,massCellSum]
  | cons a as ih =>
    have hRua := m.R_monotone ho.2.1
    have hsub : uIcc (m.R u) (m.R a.val)⊆Icc m.rmin 1 := by
      rw [uIcc_of_le hRua]
      exact Icc_subset_Icc (m.R_bounds u).1 (m.R_bounds a.val).2
    have hac : AbsolutelyContinuousOnInterval m.alpha.val.val (m.R u) (m.R a.val) :=
      ((inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property).mono hsub).absolutelyContinuousOnInterval
    have hI : IntegrableOn (deriv m.alpha.val.val) (Ioc (m.R u) (m.R a.val)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hRua).mp hac.intervalIntegrable_deriv
    have heq : (fun r=>deriv m.alpha.val.val r*(Ioc (m.R u) (m.R a.val)).indicator (fun _=>C 0) r)=
        (Ioc (m.R u) (m.R a.val)).indicator (fun r=>deriv m.alpha.val.val r*C 0) := by
      funext r
      by_cases hr:r∈Ioc (m.R u) (m.R a.val) <;> simp [hr]
    have hhead : Integrable (fun r=>deriv m.alpha.val.val r*
        (Ioc (m.R u) (m.R a.val)).indicator (fun _=>C 0) r) := by
      rw [heq]
      exact (integrable_indicator_iff measurableSet_Ioc).mpr (hI.mul_const (C 0))
    have hheadEq : (∫r,deriv m.alpha.val.val r*
        (Ioc (m.R u) (m.R a.val)).indicator (fun _=>C 0) r)=(a.val-u)*C 0 := by
      by_cases hC : C 0=0
      · simp [hC]
      have hu0 : m.u0≤u := by simpa only [partitionPoint,partitionValues_zero,id_eq] using hhigh 0 hC
      have hu1 : u≤1 := (massOrdered_bounds ho).2
      have ha1 : a.val≤1 := (massOrdered_bounds ho.2.2).2
      rw [heq,integral_indicator measurableSet_Ioc,←intervalIntegral.integral_of_le hRua,
        intervalIntegral.integral_mul_const,hac.integral_deriv_eq_sub,
        m.R_spec ⟨hu0.trans ho.2.1,ha1⟩,m.R_spec ⟨hu0,hu1⟩]
    have htail := ih ho.2.2 (fun j=>C (j+1)) (fun j hj=>by
      simpa only [partitionPoint,partitionValues] using hhigh (j+1) hj)
    have he (r : ℝ) : deriv m.alpha.val.val r*radiusCellEnergyDensity m.R u (a::as) C r=
        deriv m.alpha.val.val r*(Ioc (m.R u) (m.R a.val)).indicator (fun _=>C 0) r+
          deriv m.alpha.val.val r*radiusCellEnergyDensity m.R a.val as (fun j=>C (j+1)) r := by
      simp only [radiusCellEnergyDensity,mul_add]
    refine ⟨by simp_rw [he];exact hhead.add htail.1,?_⟩
    simp_rw [he]
    rw [integral_add hhead htail.1,hheadEq,htail.2]
    rfl

theorem nativeColumn_high_support (as : List PositiveMass) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ)
    (hhigh : ∀i∈J,m.u0≤partitionPoint 0 as i.val) :
    ∀i,nativeSelectedColumn J unit col i≠0 → m.u0≤partitionPoint 0 as i := by
  intro i hi
  unfold nativeSelectedColumn at hi
  split_ifs at hi with hib hij
  · exact hhigh ⟨i,hib⟩ hij
  all_goals exact False.elim (hi rfl)

theorem unitColumn_mass (as : List PositiveMass) (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ)
    (hhigh : ∀i∈J,m.u0≤partitionPoint 0 as i.val) :
    (∫r,deriv m.alpha.val.val r*m.unitColumn as J unit col r)=
      ∑u : Fin K,physicalSelectedUnitMass (sampleClockSteps m.q 0 as) J unit u*col u := by
  rw [unitColumn,(m.original_coefficients_mass_radius_eq as ho _
    (m.nativeColumn_high_support as J unit col hhigh)).2]
  have hs := sampled_mass_weight_sum m.q as 0 (nativeSelectedColumn J unit col)
  simp only [he,sub_self,zero_mul,add_zero] at hs
  rw [←hs]
  simp_rw [nativeSelectedColumn_atIndex]
  exact selected_mass_grouping _ _ _ _

theorem unitColumn_filled_integral (dphys : ℕ)
    (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ)
    (hcol : ∀u,0≤col u) (hhigh : ∀i∈J,m.u0≤partitionPoint 0 as i.val) :
    nativeWeightedFilledTrace m.n dphys e m.q as ho J unit col=
      ∫r,deriv m.alpha.val.val r*m.unitColumn as J unit col r
        ∂m.radiusMeasure dphys e as ho := by
  let steps := sampleClockSteps m.q 0 as
  let ha : OrderedSteps 0 (steps++[]) := by simpa using sampleClockSteps_ordered m.q _ ho
  let C := fun j=>physicalRootedCapCellTrace m.n dphys e (m.q 0) steps [] ha j
  let D := nativeSelectedColumn J unit col
  have hC r : 0≤radiusCellEnergyDensity m.R 0 as C r :=
    (radiusCellEnergyDensity_mem_Icc m.R m.R_monotone as ho C
      (fun j=>physicalRootedCapCellTrace_mem_Icc _ _ _ _ _ _ _ j) r).1
  have hmeasure :
      (∫r,deriv m.alpha.val.val r*radiusCellEnergyDensity m.R 0 as D r
        ∂volume.withDensity (fun r=>ENNReal.ofReal (radiusCellEnergyDensity m.R 0 as C r)))=
      ∫r,deriv m.alpha.val.val r*radiusCellEnergyDensity m.R 0 as (fun j=>D j*C j) r := by
    rw [integral_withDensity_eq_integral_toReal_smul
      (radiusCellEnergyDensity_measurable m.R 0 as C).ennreal_ofReal
      (ae_of_all _ (fun _=>ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    exact ae_of_all _ (fun r=>by
      change (ENNReal.ofReal (radiusCellEnergyDensity m.R 0 as C r)).toReal*
        (deriv m.alpha.val.val r*radiusCellEnergyDensity m.R 0 as D r)=
        deriv m.alpha.val.val r*radiusCellEnergyDensity m.R 0 as (fun j=>D j*C j) r
      rw [ENNReal.toReal_ofReal (hC r),←radiusCellEnergyDensity_mul m.R m.R_monotone as ho D C r]
      ring)
  have hmass := (m.original_coefficients_mass_radius_eq as ho (fun j=>D j*C j)
    (fun j hj=>(m.nativeColumn_high_support as J unit col hhigh) j (mul_ne_zero_iff.mp hj).1)).2
  have hs := sampled_mass_weight_sum m.q as 0 (fun j=>D j*C j)
  simp only [he,sub_self,zero_mul,add_zero] at hs
  have htrace := physicalRootedCapIndexedTrace_eq_weightedCellSum m.n dphys e (m.q 0)
    (nativeWeightedCutDurations steps J unit col) steps [] ha (by
      simp only [nativeWeightedCutDurations,List.length_ofFn,le_refl])
  change nativeWeightedFilledTrace m.n dphys e m.q as ho J unit col=
    physicalWeightedCutSum (nativeWeightedCutDurations steps J unit col) C at htrace
  rw [htrace,nativeWeightedCutDurations,contactWeightedCutSum_ofFn]
  have hmassEq :
      (∑i : Fin steps.length,pathMassDifferences steps 0 i.castSucc*D i.val*C i.val)=
      massCellSum as 0 (fun j=>D j*C j) := by
    rw [←hs,Fin.sum_univ_castSucc,sampled_terminal_mass_zero m.q as he]
    simp only [zero_mul,add_zero]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_castSucc]
    ring
  have hl : (∑i : Fin steps.length,
      ((pathMassDifferences steps 0 i.castSucc*D i.val).toNNReal:ℝ)*C i.val)=
      massCellSum as 0 (fun j=>D j*C j) := by
    calc
      _ = ∑i : Fin steps.length,pathMassDifferences steps 0 i.castSucc*D i.val*C i.val := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Real.coe_toNNReal _ (mul_nonneg
          (pathMassDifferences_nonneg steps (sampleClockSteps_ordered m.q _ ho) i.castSucc)
          (nativeSelectedColumn_nonneg J unit col hcol i.val))]
      _ = _ := hmassEq
  rw [hl]
  have hr := hmeasure.trans hmass
  simpa only [unitColumn,radiusMeasure,radiusDensity,physicalRadiusCellEnergyDensity,
    Nat.zero_add,steps,ha,C,D] using hr.symm

theorem cutMass_lowerRadius (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0≤partitionPoint 0 as i.val) {a : ℝ}
    (hleft : ∀i∈J,a≤ m.R (partitionPoint 0 as i.val)) :
    ∀i∈J,m.alpha.val.val a≤physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val := by
  intro i hi
  have hp := partitionPoint_mem as ho i.val
  have h := m.alpha.val.property.2 (hleft i hi)
  rw [m.R_spec ⟨hhigh i hi,hp.2⟩] at h
  rw [physicalCutMass_sampleClockSteps m.q 0 as i.val (by
    simpa only [sampleClockSteps_length] using Nat.le_of_lt_succ i.isLt)]
  exact h

theorem weightedSquareEnergy_le_integral (dphys : ℕ)
    (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh : ℝ} (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0≤ mesh)
    {K : ℕ} (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (col : Fin K→ℝ)
    (hcol : ∀u,0≤col u) {B : ℝ} (hB : 0≤B) (hbound : ∀u,col u≤B)
    (hhigh : ∀i∈J,m.u0≤partitionPoint 0 as i.val) :
    nativeWeightedSquareEnergy (m.n+1) (sampleClockSteps m.q 0 as) (m.q 0) J unit col≤
      2*(∫r,deriv m.alpha.val.val r*m.unitColumn as J unit col r∂m.radiusMeasure dphys e as ho)+
        2*(mesh*B) := by
  let steps := sampleClockSteps m.q 0 as
  have ha := sampleClockSteps_ordered m.q _ ho
  have hmass (i : Fin steps.length) : pathMassDifferences steps 0 i.castSucc≤ mesh := by
    have hi : i.val<as.length := by simpa only [steps,sampleClockSteps_length] using i.isLt
    have heq := pathMassDifferences_eq_cutMass steps 0 i.castSucc
    simp only [Fin.val_castSucc,steps,
      physicalCutMass_sampleClockSteps m.q 0 as i.val hi.le,
      physicalCutMass_sampleClockSteps m.q 0 as (i.val+1) (by omega)] at heq
    rw [heq]
    exact massPartition_point_next_mesh as hmesh hi
  have ht := nativeWeightedSquareEnergy_le_filled_and_mesh m.n dphys e steps ha (m.q 0)
    J unit col hcol (sampled_terminal_mass_zero m.q as he) hmesh0 hB hmass hbound
  change _≤2*nativeWeightedFilledTrace m.n dphys e m.q as ho J unit col+2*(mesh*B) at ht
  rwa [m.unitColumn_filled_integral dphys e as ho he J unit col hcol hhigh] at ht

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
