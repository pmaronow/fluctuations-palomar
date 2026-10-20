module

public import ComparisonNativeSelectedMaskWitnesses
public import ComparisonNativeMaskMassTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000
attribute [local instance] Classical.propDecidable

def nativeKeptRows {β : Type*} [Fintype β] {N : ℕ}
    (J : β→Finset (Fin N)) (keep : β→Bool) : Finset (Fin N) :=
  Finset.univ.biUnion (fun b=>if keep b then J b else ∅)

def nativeKeptSupport {β : Type*} (F : β→Set ℝ) (keep : β→Bool) : Set ℝ :=
  {r | ∃b,keep b=true ∧ r∈F b}

theorem nativeKeptRows_mem {β : Type*} [Fintype β] {N : ℕ}
    (J : β→Finset (Fin N)) (keep : β→Bool) (i : Fin N) :
    i∈nativeKeptRows J keep ↔ ∃b,keep b=true ∧ i∈J b := by
  simp only [nativeKeptRows,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨b,hb⟩
    split_ifs at hb with h
    · exact ⟨b,h,hb⟩
    · exact False.elim (Finset.notMem_empty _ hb)
  · rintro ⟨b,hb,hi⟩
    exact ⟨b,by simpa only [hb,ite_true] using hi⟩

theorem nativeKeptRows_support {β : Type*} [Fintype β] {N : ℕ}
    (p : ℕ→ℝ) (J : β→Finset (Fin N)) (keep : β→Bool) {r : ℝ} :
    r∈NativeSelectedMask.finiteSupport p (nativeKeptRows J keep) ↔
      ∃b,keep b=true ∧ r∈NativeSelectedMask.finiteSupport p (J b) := by
  constructor
  · rintro ⟨i,hi,hri⟩
    obtain ⟨b,hb,hib⟩ := (nativeKeptRows_mem J keep i).mp hi
    exact ⟨b,hb,i,hib,hri⟩
  · rintro ⟨b,hb,i,hi,hri⟩
    exact ⟨i,(nativeKeptRows_mem J keep i).mpr ⟨b,hb,hi⟩,hri⟩

theorem nativeKeptSupport_measurable {β : Type*} [Fintype β]
    (F : β→Set ℝ) (keep : β→Bool) (hF : ∀b,MeasurableSet (F b)) :
    MeasurableSet (nativeKeptSupport F keep) := by
  have he : nativeKeptSupport F keep=⋃b,if keep b then F b else ∅ := by
    ext r
    simp only [nativeKeptSupport,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · rintro ⟨b,hb,hr⟩
      exact ⟨b,by simpa only [hb,ite_true] using hr⟩
    · rintro ⟨b,hr⟩
      split_ifs at hr with hb
      · exact ⟨b,hb,hr⟩
      · exact False.elim hr
  rw [he]
  apply MeasurableSet.iUnion
  intro b
  split_ifs <;> first | exact hF b | exact MeasurableSet.empty

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonNativeKeptUnion_support_eventually {β : Type*} [Fintype β] {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M) (as : ℕ→List PositiveMass)
    (J : ∀j,β→Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (keep : β→Bool) (F : β→Set ℝ)
    (hmem : ∀b,∀ᵐ r∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)) (J j b) ↔ r∈F b)) :
    ∀ᵐ r∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i))
        (nativeKeptRows (J j) keep) ↔ r∈nativeKeptSupport F keep) := by
  filter_upwards [ae_all_iff.mpr hmem] with r hr
  filter_upwards [Filter.eventually_all.mpr hr] with j hj
  rw [nativeKeptRows_support]
  exact exists_congr (fun b=>and_congr_right (fun _=>hj b))

theorem comparisonNativeKeptUnion_mass_L1 {β : Type*} [Fintype β] {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1)
    (J : ∀j,β→Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (hJ : ∀j b,∀i∈J j b,i.val<(as j).length)
    (K : ℕ→ℕ) (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1)→Fin (K j))
    (keep : β→Bool) (F : β→Set ℝ)
    (hmem : ∀b,∀ᵐ r∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)) (J j b) ↔ r∈F b)) :
    Tendsto (fun j=>∫u in Icc (0:ℝ) 1,
      |massStepFunction (as j) (nativeSelectedColumn (nativeKeptRows (J j) keep) (unit j) (fun _=>1)) u-
        (nativeKeptSupport F keep).indicator (fun _=>1)
          (comparisonSweepQuantile hc hk hkc hm hM α u)|) atTop (𝓝 0) := by
  have hU : ∀j,∀i∈nativeKeptRows (J j) keep,i.val<(as j).length := by
    intro j i hi
    obtain ⟨b,_,hib⟩ := (nativeKeptRows_mem (J j) keep i).mp hi
    exact hJ j b i hib
  have hs := comparisonNativeMask_tendsto_of_support_eventually hc hk hkc hm hM q α as ho he K
    (fun j=>nativeKeptRows (J j) keep) unit hU (nativeKeptSupport F keep)
    (comparisonNativeKeptUnion_support_eventually hc hk hkc hm hM q α as J keep F hmem)
  apply comparisonNativeMask_mass_L1_tendsto_of_radius_ae hc hk hkc hm hM q α as ho he K
    (fun j=>nativeKeptRows (J j) keep) unit ((nativeKeptSupport F keep).indicator (fun _=>1))
  simpa only [restrict_Ioo_eq_restrict_Icc] using hs.1

theorem comparisonNativeMask_massStep_integral {ι : Type}
    (q : ℝ→ι→ℝ≥0) (as : List PositiveMass) (ho : MassOrdered 0 as)
    (he : partitionEnd 0 as=1) {K : ℕ}
    (J : Finset (Fin ((sampleClockSteps q 0 as).length+1)))
    (unit : Fin ((sampleClockSteps q 0 as).length+1)→Fin K) :
    (∫u in Icc (0:ℝ) 1,massStepFunction as (nativeSelectedColumn J unit (fun _=>1)) u)=
      physicalWindowMass (sampleClockSteps q 0 as) 0 J := by
  have hs := sampled_mass_weight_sum q as 0 (nativeSelectedColumn J unit (fun _=>1))
  simp only [he,sub_self,zero_mul,add_zero] at hs
  have hmass : massCellSum as 0 (nativeSelectedColumn J unit (fun _=>1))=
      ∫u in (0:ℝ)..1,massStepFunction as (nativeSelectedColumn J unit (fun _=>1)) u := by
    simpa only [he] using massCellSum_eq_integral as ho (nativeSelectedColumn J unit (fun _=>1))
  rw [integral_Icc_eq_integral_Ioc,←intervalIntegral.integral_of_le zero_le_one,
    ←hmass,←hs]
  simp_rw [nativeSelectedColumn_atIndex]
  simp [physicalWindowMass,mul_ite]

theorem comparisonNativeKeptUnion_mass_tendsto {β : Type*} [Fintype β] {ι : Type}
    (q : ℝ→ι→ℝ≥0) (α : inverseIntegralConstraints 0 0 k M)
    (as : ℕ→List PositiveMass) (ho : ∀j,MassOrdered 0 (as j))
    (he : ∀j,partitionEnd 0 (as j)=1)
    (J : ∀j,β→Finset (Fin ((sampleClockSteps q 0 (as j)).length+1)))
    (hJ : ∀j b,∀i∈J j b,i.val<(as j).length)
    (K : ℕ→ℕ) (unit : ∀j,Fin ((sampleClockSteps q 0 (as j)).length+1)→Fin (K j))
    (keep : β→Bool) (F : β→Set ℝ) (hF : ∀b,MeasurableSet (F b))
    (hmem : ∀b,∀ᵐ r∂volume.restrict (Ioo (0:ℝ) 1),∀ᶠ j in atTop,
      (r∈NativeSelectedMask.finiteSupport
        (fun i=>comparisonSweepQuantile hc hk hkc hm hM α (partitionPoint 0 (as j) i)) (J j b) ↔ r∈F b)) :
    Tendsto (fun j=>physicalWindowMass (sampleClockSteps q 0 (as j)) 0 (nativeKeptRows (J j) keep))
      atTop (𝓝 (∫u in Icc (0:ℝ) 1,(nativeKeptSupport F keep).indicator (fun _=>1)
        (comparisonSweepQuantile hc hk hkc hm hM α u))) := by
  let moving := fun j u=>massStepFunction (as j)
    (nativeSelectedColumn (nativeKeptRows (J j) keep) (unit j) (fun _=>1)) u
  let fixed : ℝ→ℝ := fun u=>(nativeKeptSupport F keep).indicator (fun _=>1)
    (comparisonSweepQuantile hc hk hkc hm hM α u)
  have hlimit := comparisonNativeKeptUnion_mass_L1 hc hk hkc hm hM q α as ho he J hJ K unit keep F hmem
  have hfixed : IntegrableOn fixed (Icc (0:ℝ) 1) := by
    apply (memLp_of_bounded (p:=1) (a:=0) (b:=1) ?_ ?_).integrable le_rfl
    · apply ae_of_all
      intro u
      simp only [fixed,Set.indicator_apply]
      split_ifs <;> norm_num
    · exact ((measurable_const.indicator (nativeKeptSupport_measurable F keep hF)).comp
        (comparisonSweepQuantile_monotone hc hk hkc hm hM α).measurable).aestronglyMeasurable.restrict
  have hmoving j : IntegrableOn (moving j) (Icc (0:ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp
      (massStepFunction_intervalIntegrable (as j) _ 0 1)
  have hint : Tendsto (fun j=>∫u in Icc (0:ℝ) 1,moving j u) atTop
      (𝓝 (∫u in Icc (0:ℝ) 1,fixed u)) := by
    apply Metric.tendsto_nhds.mpr
    intro epsilon hepsilon
    filter_upwards [(tendsto_order.mp hlimit).2 epsilon hepsilon] with j hj
    rw [Real.dist_eq,←integral_sub (hmoving j) hfixed]
    have habs := abs_integral_le_integral_abs (f:=fun u=>moving j u-fixed u)
      (μ:=volume.restrict (Icc (0:ℝ) 1))
    exact habs.trans_lt hj
  convert hint using 1
  funext j
  exact (comparisonNativeMask_massStep_integral q (as j) (ho j) (he j) _ (unit j)).symm

end
end OAI.SKFluctuations.LaplaceWindowFormalization
