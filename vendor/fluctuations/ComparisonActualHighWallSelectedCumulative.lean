module

public import ComparisonShiftedNativeColumns
public import ComparisonSelectedCumulativeFiniteCompactness
public import ComparisonSelectedUnitEndpointCoordinates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
set_option maxHeartbeats 16000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

def selectedMassDensity (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) : ℝ→ℝ :=
  (Ioo m.rmin 1).indicator (fun r=>deriv m.alpha.val.val r*
    m.unitColumn as J (fun _=>(0:Fin 1)) (fun _=>1) r)

theorem selectedMassDensity_mem_Icc (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) (r : ℝ) :
    m.selectedMassDensity as J r∈Icc (0:ℝ) (m.M 1) := by
  unfold selectedMassDensity
  by_cases hr:r∈Ioo m.rmin 1
  · rw [indicator_of_mem hr]
    have hd := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr.1 hr.2)
      (inverseIntegralConstraints_lipschitz m.hm m.hM m.alpha.property)
    have hd0 := m.alpha.val.property.2.deriv_nonneg (x:=r)
    have hw : m.unitColumn as J (fun _=>(0:Fin 1)) (fun _=>1) r∈Icc (0:ℝ) 1 := by
      apply radiusCellEnergyDensity_mem_Icc_bound _ m.R_monotone as ho _ (by norm_num)
      intro i
      unfold nativeSelectedColumn
      split_ifs <;> norm_num
    refine ⟨mul_nonneg hd0 hw.1,?_⟩
    rw [Real.norm_eq_abs,abs_of_nonneg hd0] at hd
    exact (mul_le_mul hd hw.2 hw.1 m.hM).trans_eq (mul_one _)
  · rw [indicator_of_notMem hr]
    exact ⟨le_rfl,m.hM⟩

theorem selectedMassDensity_stronglyMeasurable (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) :
    StronglyMeasurable (m.selectedMassDensity as J) := by
  apply StronglyMeasurable.indicator _ measurableSet_Ioo
  exact (stronglyMeasurable_deriv m.alpha.val.val).mul
    (m.unitColumn_measurable as J (fun _=>(0:Fin 1)) (fun _=>1)).stronglyMeasurable

theorem selectedMassDensity_integrable (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) :
    IntegrableOn (m.selectedMassDensity as J) (Icc (0:ℝ) 1) := by
  have h1 : IntegrableOn (fun _ : ℝ=>(1:ℝ)) (Icc (0:ℝ) 1) := integrableOn_const (by simp)
  have hbound : ∀ᵐ r∂volume.restrict (Icc (0:ℝ) 1),‖m.selectedMassDensity as J r‖  ≤  m.M 1 := by
    apply ae_of_all
    intro r
    have hh := m.selectedMassDensity_mem_Icc as ho J r
    rw [Real.norm_eq_abs,abs_of_nonneg hh.1]
    exact hh.2
  simpa only [IntegrableOn,mul_one] using h1.bdd_mul
    (m.selectedMassDensity_stronglyMeasurable as J).aestronglyMeasurable.restrict hbound

def selectedCDF (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) : Icc (0:ℝ) 1→ᵇℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨
    fun r=>cumulativeCellMass (m.selectedMassDensity as J) r.val,
    (cumulativeCellMass_lipschitz m.hM _ (m.selectedMassDensity_integrable as ho J)
      (fun r _=>by
        have hh:=m.selectedMassDensity_mem_Icc as ho J r
        rw [Real.norm_eq_abs,abs_of_nonneg hh.1]
        exact hh.2)).continuous⟩

theorem selectedCDF_apply (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) (r : Icc (0:ℝ) 1) :
    m.selectedCDF as ho J r=cumulativeCellMass (m.selectedMassDensity as J) r.val := rfl

theorem selectedCDF_lipschitz (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) :
    LipschitzWith (m.M 1).toNNReal (m.selectedCDF as ho J) :=
  cumulativeCellMass_lipschitz m.hM _ (m.selectedMassDensity_integrable as ho J)
    (fun r _=>by
      have hh:=m.selectedMassDensity_mem_Icc as ho J r
      rw [Real.norm_eq_abs,abs_of_nonneg hh.1]
      exact hh.2)

theorem selectedCDF_mem_Icc (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) (r : Icc (0:ℝ) 1) :
    m.selectedCDF as ho J r∈Icc (0:ℝ) (m.M 1) :=
  cumulativeCellMass_mem_Icc m.hM _ (m.selectedMassDensity_integrable as ho J)
    (fun t _=>m.selectedMassDensity_mem_Icc as ho J t) r

theorem selectedCDF_finite_exists_uniform_subseq {β : Type*} [Fintype β]
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (J : ∀j,β→Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1))) :
    ∃f : β→(Icc (0:ℝ) 1→ᵇℝ),∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀b,Tendsto (fun j=>m.selectedCDF (as (φ j)) (ho (φ j)) (J (φ j) b)) atTop (𝓝 (f b)) := by
  apply boundedLipschitzCumulative_finite_exists_uniform_subseq m.hM
    (fun j b=>m.selectedCDF (as j) (ho j) (J j b))
  · exact fun j b=>m.selectedCDF_lipschitz (as j) (ho j) (J j b)
  · exact fun j b r=>m.selectedCDF_mem_Icc (as j) (ho j) (J j b) r

theorem selectedCDF_exists_uniform_subseq
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (J : ∀j,Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1))) :
    ∃f : Icc (0:ℝ) 1→ᵇℝ,∃φ : ℕ→ℕ,StrictMono φ ∧
      Tendsto (fun j=>m.selectedCDF (as (φ j)) (ho (φ j)) (J (φ j))) atTop (𝓝 f) := by
  obtain ⟨f,φ,hφ,hlim⟩:=m.selectedCDF_finite_exists_uniform_subseq as ho (fun (j : ℕ) (_ : Fin 1)=>J j)
  exact ⟨f 0,φ,hφ,hlim 0⟩

theorem selectedMassDensity_zero_before (as : List PositiveMass)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) {r : ℝ} (hr : r  ≤  m.rmin) :
    m.selectedMassDensity as J r=0 := by
  exact indicator_of_notMem (fun h : r∈Ioo m.rmin 1=>not_lt_of_ge hr h.1) _

theorem selected_prefix_integral (as : List PositiveMass) (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0 ≤ partitionPoint 0 as i.val) (kcut : ℕ) :
    (∫r in Iic (m.R (partitionPoint 0 as kcut)),
      deriv m.alpha.val.val r*m.unitColumn as J (fun _=>(0:Fin 1)) (fun _=>1) r)=
    ∑i : Fin ((sampleClockSteps m.q 0 as).length+1),
      pathMassDifferences (sampleClockSteps m.q 0 as) 0 i*
        (if i∈J ∧ i.val<kcut then 1 else 0) := by
  let C:=nativeSelectedColumn J (fun _=>(0:Fin 1)) (fun _=>1)
  have hfun : (fun r=>deriv m.alpha.val.val r*
      radiusCellEnergyDensity m.R 0 as (fun i=>if i<kcut then C i else 0) r)=
      (Iic (m.R (partitionPoint 0 as kcut))).indicator
        (fun r=>deriv m.alpha.val.val r*radiusCellEnergyDensity m.R 0 as C r) := by
    funext r
    rw [radiusCellEnergyDensity_prefix m.R m.R_monotone as ho C kcut]
    by_cases hr:r∈Iic (m.R (partitionPoint 0 as kcut)) <;> simp [hr]
  have hi:=(m.original_coefficients_mass_radius_eq as ho (fun i=>if i<kcut then C i else 0)
    (fun i hi=>by
      split_ifs at hi with hik
      · exact m.nativeColumn_high_support as J (fun _=>(0:Fin 1)) (fun _=>1) hhigh i hi
      · exact (hi rfl).elim)).2
  rw [hfun,integral_indicator measurableSet_Iic] at hi
  change (∫r in Iic (m.R (partitionPoint 0 as kcut)),
    deriv m.alpha.val.val r*radiusCellEnergyDensity m.R 0 as C r)=_
  rw [hi]
  have hs:=sampled_mass_weight_sum m.q as 0 (fun i=>if i<kcut then C i else 0)
  simp only [he,sub_self,zero_mul,add_zero] at hs
  rw [←hs]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [C]
  rw [nativeSelectedColumn_atIndex]
  by_cases hJ:i∈J <;> by_cases hk:i.val<kcut <;> simp [hJ,hk]

theorem selected_cumulative_at_cut (hr0 : 0  ≤  m.rmin)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0 ≤ partitionPoint 0 as i.val) (kcut : ℕ) :
    cumulativeCellMass (m.selectedMassDensity as J) (m.R (partitionPoint 0 as kcut))=
    ∑i : Fin ((sampleClockSteps m.q 0 as).length+1),
      pathMassDifferences (sampleClockSteps m.q 0 as) 0 i*
        (if i∈J ∧ i.val<kcut then 1 else 0) := by
  let cut:=m.R (partitionPoint 0 as kcut)
  let w:=m.unitColumn as J (fun _=>(0:Fin 1)) (fun _=>1)
  have hcut : cut∈Icc (0:ℝ) 1:=⟨hr0.trans (m.R_bounds _).1,(m.R_bounds _).2⟩
  have heq : (Ioc (0:ℝ) cut).indicator (m.selectedMassDensity as J)=ᵐ[volume]
      (Iic cut).indicator (fun r=>deriv m.alpha.val.val r*w r) := by
    filter_upwards [volume.ae_ne (1:ℝ)] with r hr1
    by_cases hr:r ≤ cut
    · by_cases hrmin:m.rmin<r
      · have hr0r : 0<r:=hr0.trans_lt hrmin
        have hr01 : r∈Ioo m.rmin 1:=⟨hrmin,lt_of_le_of_ne (hr.trans hcut.2) hr1⟩
        simp only [indicator_of_mem (show r∈Ioc (0:ℝ) cut from ⟨hr0r,hr⟩),
          indicator_of_mem (show r∈Iic cut from hr),selectedMassDensity,indicator_of_mem hr01]
        rfl
      · have hw0 : w r=0:=radiusCellEnergyDensity_eq_zero_of_le m.R m.R_monotone as ho _
          ((le_of_not_gt hrmin).trans (m.R_bounds 0).1)
        have hnot : r∉Ioo m.rmin 1:=fun hh=>hrmin hh.1
        rw [indicator_of_mem (show r∈Iic cut from hr),hw0,mul_zero]
        by_cases hri:r∈Ioc (0:ℝ) cut
        · rw [indicator_of_mem hri,selectedMassDensity,indicator_of_notMem hnot]
        · rw [indicator_of_notMem hri]
    · have hnot:r∉Ioc (0:ℝ) cut:=fun hh=>hr hh.2
      simp only [indicator_of_notMem hnot,indicator_of_notMem (show r∉Iic cut from hr)]
  calc
    _=(∫r in Iic cut,deriv m.alpha.val.val r*w r) := by
      rw [cumulativeCellMass,intervalIntegral.integral_of_le hcut.1,
        ←integral_indicator measurableSet_Ioc,←integral_indicator measurableSet_Iic]
      exact integral_congr_ae heq
    _=_:=m.selected_prefix_integral as ho he J hhigh kcut

theorem selected_cumulative_monotoneOn (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1))) :
    MonotoneOn (cumulativeCellMass (m.selectedMassDensity as J)) (Icc (0:ℝ) 1) :=
  cumulativeCellMass_monotoneOn _ (m.selectedMassDensity_integrable as ho J)
    (fun r _=>(m.selectedMassDensity_mem_Icc as ho J r).1)

private theorem partitionPoint_length_succ (u : ℝ) (as : List PositiveMass) :
    partitionPoint u as (as.length+1)=partitionEnd u as := by
  induction as generalizing u with
  | nil=>rfl
  | cons b bs ih=>exact ih b.val

theorem selected_cumulative_one (hr0 : 0  ≤  m.rmin)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0 ≤ partitionPoint 0 as i.val) :
    cumulativeCellMass (m.selectedMassDensity as J) 1=
      physicalWindowMass (sampleClockSteps m.q 0 as) 0 J := by
  have HH:=m.selected_cumulative_at_cut hr0 as ho he J hhigh (as.length+1)
  rw [partitionPoint_length_succ,he,m.R_one] at HH
  rw [HH]
  have hi (i : Fin ((sampleClockSteps m.q 0 as).length+1)) : i.val<as.length+1 := by
    simpa only [sampleClockSteps_length] using i.isLt
  simp only [hi,and_true,mul_ite,mul_one,mul_zero,physicalWindowMass,Finset.sum_ite_mem,
    Finset.univ_inter]

theorem selectedCDF_one (hr0 : 0  ≤  m.rmin)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0 ≤ partitionPoint 0 as i.val) :
    m.selectedCDF as ho J ⟨1,by simp⟩=physicalWindowMass (sampleClockSteps m.q 0 as) 0 J :=
  m.selected_cumulative_one hr0 as ho he J hhigh

theorem selectedCDF_at_cut (hr0 : 0 ≤ m.rmin)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0 ≤ partitionPoint 0 as i.val) (kcut : ℕ) :
    m.selectedCDF as ho J
      ⟨m.R (partitionPoint 0 as kcut),hr0.trans (m.R_bounds _).1,(m.R_bounds _).2⟩=
    ∑i : Fin ((sampleClockSteps m.q 0 as).length+1),
      pathMassDifferences (sampleClockSteps m.q 0 as) 0 i*
        (if i∈J ∧ i.val<kcut then 1 else 0) :=
  m.selected_cumulative_at_cut hr0 as ho he J hhigh kcut

theorem selectedCDF_width_tendsto (hr0 : 0 ≤ m.rmin)
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1)
    (J : ∀j,Finset (Fin ((sampleClockSteps m.q 0 (as j)).length+1)))
    (hhigh : ∀j,∀i∈J j,m.u0 ≤ partitionPoint 0 (as j) i.val)
    (U : Set ℝ)
    (C : ∀j,NativeConstructedCoordinates (sampleClockSteps m.q 0 (as j)) (J j)
      (m.rowRadius (as j)) U)
    (f : Icc (0:ℝ) 1→ᵇℝ)
    (hf : Tendsto (fun j=>m.selectedCDF (as j) (ho j) (J j)) atTop (𝓝 f)) :
    Tendsto (fun j=>(C j).x (C j).K) atTop (𝓝 (f ⟨1,by simp⟩)) := by
  have hh:=selectedCumulative_uniform_moving_eval_tendsto _ f hf
    (fun _=>(⟨1,by simp⟩ : Icc (0:ℝ) 1)) ⟨1,by simp⟩ tendsto_const_nhds
  have heq j : m.selectedCDF (as j) (ho j) (J j) ⟨1,by simp⟩=(C j).x (C j).K := by
    rw [m.selectedCDF_one hr0 (as j) (ho j) (he j) (J j) (hhigh j),(C j).width]
  simpa only [heq] using hh

theorem selected_first_coordinate_eq_cumulative (hr0 : 0  ≤  m.rmin)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0 ≤ partitionPoint 0 as i.val)
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (x : ℕ→ℝ) (h0:x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass (sampleClockSteps m.q 0 as) J unit u=
      x (u.val+1)-x u.val)
    (horder : MonotoneOn unit (J:Set (Fin ((sampleClockSteps m.q 0 as).length+1))))
    (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi:i∈J)
    (hfirst : ∀j∈J,unit j=unit i→i ≤ j) :
    x (unit i).val=cumulativeCellMass (m.selectedMassDensity as J)
      (m.R (partitionPoint 0 as i.val)) := by
  rw [m.selected_cumulative_at_cut hr0 as ho he J hhigh i.val]
  exact selected_first_coordinate_eq_mass_before_row (sampleClockSteps m.q 0 as)
    J unit x h0 hmass horder i hi hfirst

theorem selected_last_coordinate_eq_cumulative (hr0 : 0  ≤  m.rmin)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0 ≤ partitionPoint 0 as i.val)
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (x : ℕ→ℝ) (h0:x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass (sampleClockSteps m.q 0 as) J unit u=
      x (u.val+1)-x u.val)
    (horder : MonotoneOn unit (J:Set (Fin ((sampleClockSteps m.q 0 as).length+1))))
    (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi:i∈J)
    (hlast : ∀j∈J,unit j=unit i→j ≤ i) :
    x ((unit i).val+1)=cumulativeCellMass (m.selectedMassDensity as J)
      (m.R (partitionPoint 0 as (i.val+1))) := by
  rw [m.selected_cumulative_at_cut hr0 as ho he J hhigh (i.val+1)]
  exact selected_last_coordinate_eq_mass_through_row (sampleClockSteps m.q 0 as)
    J unit x h0 hmass horder i hi hlast

theorem selected_cumulative_mem_unit_interval (hr0 : 0  ≤  m.rmin)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps m.q 0 as).length+1)))
    (hhigh : ∀i∈J,m.u0 ≤ partitionPoint 0 as i.val)
    (unit : Fin ((sampleClockSteps m.q 0 as).length+1)→Fin K) (x : ℕ→ℝ)
    (h0:x 0=0)
    (hmass : ∀u : Fin K,physicalSelectedUnitMass (sampleClockSteps m.q 0 as) J unit u=
      x (u.val+1)-x u.val)
    (horder : MonotoneOn unit (J:Set (Fin ((sampleClockSteps m.q 0 as).length+1))))
    (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi:i∈J) {r : ℝ}
    (hr : r∈Ioc (m.R (partitionPoint 0 as i.val)) (m.R (partitionPoint 0 as (i.val+1)))) :
    cumulativeCellMass (m.selectedMassDensity as J) r∈Icc (x (unit i).val) (x ((unit i).val+1)) := by
  have hprefix:=selected_unit_prefix_bracket (sampleClockSteps m.q 0 as)
    (sampleClockSteps_ordered m.q _ ho) J unit x h0 hmass horder i hi
  rw [←m.selected_cumulative_at_cut hr0 as ho he J hhigh i.val,
    ←m.selected_cumulative_at_cut hr0 as ho he J hhigh (i.val+1)] at hprefix
  have hlo : m.R (partitionPoint 0 as i.val)∈Icc (0:ℝ) 1:=
    ⟨hr0.trans (m.R_bounds _).1,(m.R_bounds _).2⟩
  have hhi : m.R (partitionPoint 0 as (i.val+1))∈Icc (0:ℝ) 1:=
    ⟨hr0.trans (m.R_bounds _).1,(m.R_bounds _).2⟩
  have hr01 : r∈Icc (0:ℝ) 1:=⟨(hlo.1.trans_lt hr.1).le,hr.2.trans hhi.2⟩
  have hmono:=m.selected_cumulative_monotoneOn as ho J
  exact ⟨hprefix.1.trans (hmono hlo hr01 hr.1.le),
    (hmono hr01 hhi hr.2).trans hprefix.2⟩

end ShiftedNativeBandModel

namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable (a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)

abbrev actualCDF (as : List PositiveMass) (ho : MassOrdered 0 as)
    (J : Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 as).length+1))) :
    Icc (0:ℝ) 1→ᵇℝ := a.shiftedNativeModel.selectedCDF as ho J

theorem actualCDF_finite_exists_uniform_subseq {β : Type*} [Fintype β]
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (J : ∀j,β→Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 (as j)).length+1))) :
    ∃f : β→(Icc (0:ℝ) 1→ᵇℝ),∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀b,Tendsto (fun j=>a.actualCDF (as (φ j)) (ho (φ j)) (J (φ j) b)) atTop (𝓝 (f b)) :=
  a.shiftedNativeModel.selectedCDF_finite_exists_uniform_subseq as ho J

theorem actualCDF_one (as : List PositiveMass) (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1)
    (J : Finset (Fin ((sampleClockSteps a.shiftedNativeModel.q 0 as).length+1)))
    (hhigh : ∀i∈J,a.data.s ≤ partitionPoint 0 as i.val) :
    a.actualCDF as ho J ⟨1,by simp⟩=
      physicalWindowMass (sampleClockSteps a.shiftedNativeModel.q 0 as) 0 J :=
  a.shiftedNativeModel.selectedCDF_one a.data.hrbounds.1.le as ho he J hhigh

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
