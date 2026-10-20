module

public import PhysicalFilledCapCellLaw
public import PhysicalComparisonRadiusSampling
public import BoundaryCapMassCellSum

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory ProbabilityTheory Filter Set Hierarchy
open scoped Topology NNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

def radiusCellEnergyDensity (R : ℝ→ℝ) : ℝ→List PositiveMass→(ℕ→ℝ)→ℝ→ℝ
  | _,[],_,_=>0
  | u,a::as,C,r=>(Ioc (R u) (R a.val)).indicator (fun _=>C 0) r+
      radiusCellEnergyDensity R a.val as (fun j=>C (j+1)) r

theorem radiusCellEnergyDensity_measurable (R : ℝ→ℝ) (u : ℝ)
    (as : List PositiveMass) (C : ℕ→ℝ) :
    Measurable (radiusCellEnergyDensity R u as C) := by
  induction as generalizing u C with
  | nil=>exact measurable_const
  | cons a as ih=>exact (measurable_const.indicator measurableSet_Ioc).add (ih a.val _)

theorem radiusCellEnergyDensity_eq_zero_of_le (R : ℝ→ℝ) (hR : Monotone R)
    {u r : ℝ} (as : List PositiveMass) (ho : MassOrdered u as) (C : ℕ→ℝ)
    (hr : r ≤ R u) : radiusCellEnergyDensity R u as C r=0 := by
  induction as generalizing u C with
  | nil=>rfl
  | cons a as ih=>
    have hra : r ≤ R a.val := hr.trans (hR ho.2.1)
    have hnot : r∉Ioc (R u) (R a.val) := fun hh=>not_lt.mpr hr hh.1
    simp only [radiusCellEnergyDensity,indicator_of_notMem hnot,
      ih ho.2.2 _ hra,zero_add]

theorem radiusCellEnergyDensity_mem_Icc (R : ℝ→ℝ) (hR : Monotone R)
    {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as) (C : ℕ→ℝ)
    (hC : ∀j,C j∈Icc (0:ℝ) 1) (r : ℝ) :
    radiusCellEnergyDensity R u as C r∈Icc (0:ℝ) 1 := by
  induction as generalizing u C with
  | nil=>norm_num [radiusCellEnergyDensity]
  | cons a as ih=>
    by_cases hr : r∈Ioc (R u) (R a.val)
    · rw [radiusCellEnergyDensity,indicator_of_mem hr,
        radiusCellEnergyDensity_eq_zero_of_le R hR as ho.2.2 _ hr.2,add_zero]
      exact hC 0
    · rw [radiusCellEnergyDensity,indicator_of_notMem hr,zero_add]
      exact ih ho.2.2 _ (fun j=>hC (j+1))

theorem radiusCellEnergyDensity_integrable (R : ℝ→ℝ) (u : ℝ)
    (as : List PositiveMass) (C : ℕ→ℝ) :
    Integrable (radiusCellEnergyDensity R u as C) := by
  induction as generalizing u C with
  | nil=>exact (integrable_zero ℝ ℝ volume : Integrable (fun _ : ℝ=>(0:ℝ)))
  | cons a as ih=>
    have hi : Integrable ((Ioc (R u) (R a.val)).indicator (fun _ : ℝ=>C 0)) :=
      (integrableOn_const (by simp : volume (Ioc (R u) (R a.val))≠⊤)).integrable_indicator measurableSet_Ioc
    exact hi.add (ih a.val _)

theorem radiusCellEnergyDensity_integral (R : ℝ→ℝ) (hR : Monotone R)
    {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as) (C : ℕ→ℝ) :
    (∫r,radiusCellEnergyDensity R u as C r)=
      physicalWeightedCutSum (sampleParameterDurations R u as) C := by
  induction as generalizing u C with
  | nil=>simp [radiusCellEnergyDensity,sampleParameterDurations,physicalWeightedCutSum]
  | cons a as ih=>
    have hi : Integrable ((Ioc (R u) (R a.val)).indicator (fun _ : ℝ=>C 0)) :=
      (integrableOn_const (by simp : volume (Ioc (R u) (R a.val))≠⊤)).integrable_indicator measurableSet_Ioc
    change (∫r,(Ioc (R u) (R a.val)).indicator (fun _=>C 0) r+
      radiusCellEnergyDensity R a.val as (fun j=>C (j+1)) r)=_
    rw [integral_add hi (radiusCellEnergyDensity_integrable R a.val as _),
      integral_indicator_const _ measurableSet_Ioc,Real.volume_real_Ioc_of_le (hR ho.2.1),
      ih ho.2.2]
    simp only [sampleParameterDurations,physicalWeightedCutSum,
      Real.coe_toNNReal _ (sub_nonneg.mpr (hR ho.2.1)),smul_eq_mul]

def radiusCellEnergyMeasure (R : ℝ→ℝ) (u : ℝ)
    (as : List PositiveMass) (C : ℕ→ℝ) : Measure ℝ :=
    volume.withDensity (fun r=>ENNReal.ofReal (radiusCellEnergyDensity R u as C r))

theorem radiusCellEnergyMeasure_le_volume (R : ℝ→ℝ) (hR : Monotone R)
    {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as) (C : ℕ→ℝ)
    (hC : ∀j,C j∈Icc (0:ℝ) 1) : radiusCellEnergyMeasure R u as C ≤ volume := by
  unfold radiusCellEnergyMeasure
  have hh : (fun r=>ENNReal.ofReal (radiusCellEnergyDensity R u as C r)) ≤ᵐ[volume] (fun _=>1) :=
    Eventually.of_forall fun r=>by
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (radiusCellEnergyDensity_mem_Icc R hR as ho C hC r).2
  have hh' := withDensity_mono hh
  change volume.withDensity _ ≤ volume.withDensity (1 : ℝ→ENNReal) at hh'
  rwa [withDensity_one] at hh'

def physicalRadiusCellEnergyDensity (n d : ℕ) (e : Fin (d+1) ≃ FeatureIndex (n+1))
    (q₀ : FeatureIndex (n+1)→ℝ≥0) (pre tail : List (GaussianStep (FeatureIndex (n+1))))
    {a : ℝ} (ha : OrderedSteps a (pre++tail)) (offset : ℕ)
    (R : ℝ→ℝ) (u : ℝ) (as : List PositiveMass) : ℝ→ℝ :=
    radiusCellEnergyDensity R u as (fun j=>physicalRootedCapCellTrace n d e q₀ pre tail ha (offset+j))

theorem physicalRadiusCellEnergyDensity_mem_Icc (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q₀ : FeatureIndex (n+1)→ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n+1)))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (offset : ℕ) (R : ℝ→ℝ) (hR : Monotone R)
    {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as) (r : ℝ) :
    physicalRadiusCellEnergyDensity n d e q₀ pre tail ha offset R u as r∈Icc (0:ℝ) 1 :=
  radiusCellEnergyDensity_mem_Icc R hR as ho _
    (fun j=>physicalRootedCapCellTrace_mem_Icc n d e q₀ pre tail ha (offset+j)) r

theorem physicalRadiusCellEnergyDensity_integral_eq_cap (n d : ℕ)
    (e : Fin (d+1) ≃ FeatureIndex (n+1)) (q₀ : FeatureIndex (n+1)→ℝ≥0)
    (pre tail : List (GaussianStep (FeatureIndex (n+1)))) {a : ℝ}
    (ha : OrderedSteps a (pre++tail)) (offset : ℕ) (R : ℝ→ℝ) (hR : Monotone R)
    {u : ℝ} (as : List PositiveMass) (ho : MassOrdered u as)
    (hlen : offset+as.length ≤ pre.length) :
    (∫r,physicalRadiusCellEnergyDensity n d e q₀ pre tail ha offset R u as r)=
      zeroContinuation (Measure.pi fun k=>gaussianReal 0 (q₀ k))
        (physicalFiniteCapIndexedTrace n d e
          (List.replicate offset 0++sampleParameterDurations R u as) pre tail ha) 0 := by
  unfold physicalRadiusCellEnergyDensity
  rw [radiusCellEnergyDensity_integral R hR as ho,
    physicalRootedCapIndexedTrace_eq_weightedCellSum n d e q₀ _ pre tail ha (by
      have hlenR : (sampleParameterDurations R u as).length=as.length := by
        clear hlen
        induction as generalizing u with
        | nil=>rfl
        | cons b bs ih=>simpa only [sampleParameterDurations,List.length_cons] using congrArg (fun l=>l+1) (ih ho.2.2)
      simpa only [List.length_append,List.length_replicate,hlenR] using hlen),
    physicalWeightedCutSum_zero_prefix]

end OAI.SKFluctuations.LaplaceWindowFormalization
