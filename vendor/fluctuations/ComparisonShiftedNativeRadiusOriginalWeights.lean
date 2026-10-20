module

public import ComparisonShiftedNativeRadiusFiniteAssembly
public import ComparisonShiftedNativeRadiusWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 16000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem original_radius_weights_bounds
    {A : Set ℝ} (hA : MeasurableSet A) {x kmin : ℝ} (hx : 0<x) (hkmin : 0<kmin)
    (as : List PositiveMass) (ho : MassOrdered 0 as)
    (i : Fin ((sampleClockSteps m.q 0 as).length+1)) :
    comparisonOriginalRadiusWeights m.q as
      (comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin) i∈Icc (0:ℝ) (1/(x*kmin)) := by
  have hLp:=comparisonRadiusMassWeight_memLp_two m.R m.alpha.val.val
    m.R_monotone.measurable hA hx hkmin
  have hi : IntervalIntegrable (comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin) volume 0 1:=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr (hLp.integrable (by norm_num))
  exact MassCellAveraging.originalCoefficient_mem_Icc _ as ho (by positivity) hi
    (fun u _=>comparisonRadiusMassWeight_bounds m.R m.alpha.val.val A hx hkmin u) i.val

theorem original_radius_variance_le_filled_of_mesh
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh a z x kmin : ℝ} (hm : PartitionMesh mesh 0 as) (hm0 : 0  ≤  mesh)
    (ha : m.rmin<a) (haz : a ≤ z) (hz : z ≤ 1) (hx : 0<x) (hkmin : 0<kmin)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo a z)
    (hcutMesh : mesh ≤ m.alpha.val.val a/2) (hwallMesh : mesh ≤ m.alpha.val.val a-m.u0) :
    let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
    let w:=comparisonOriginalRadiusWeights m.q as f
    variance (fun p=>(physicalPinnedPair (uniformWeight (m.n+1)) (finiteFeature (m.n+1))
      (spinSource (m.n+1)) (sampleClockSteps m.q 0 as) 0 w p.1 p.2).1)
      (rootedHierarchyPathLaw (uniformWeight (m.n+1)) (finiteFeature (m.n+1))
        (m.q 0) (sampleClockSteps m.q 0 as)) ≤ 
      (2*(∫r,deriv m.alpha.val.val r*m.unitColumn as Finset.univ id (fun i=>(w i)^2) r
        ∂m.radiusMeasure dphys e as ho)+2*(mesh*(1/(x*kmin))^2))/(m.alpha.val.val a/2) := by
  let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
  let w:=comparisonOriginalRadiusWeights m.q as f
  have ha1 : a ≤ 1:=haz.trans hz
  have haI : a∈Icc m.rmin 1:=⟨ha.le,ha1⟩
  have hapos:=m.profile_pos ha ha1
  have Hcut (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi : w i≠0) :
      m.alpha.val.val a-mesh ≤ physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val:=
    m.originalWeights_native_cut_floor haI hAD x kmin as ho hm i hi
  have Hhigh (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi : w i≠0) :
      m.u0 ≤ partitionPoint 0 as i.val:=by
    have HC:=Hcut i hi
    have hit : i.val ≤ as.length:=by have H:=i.isLt;simp only [sampleClockSteps_length] at H;omega
    rw [physicalCutMass_sampleClockSteps m.q 0 as i.val hit] at HC
    linarith
  exact m.original_weight_variance_le_filled dphys e as ho he hm hm0 w
    (by positivity) (sq_nonneg _) (fun i=>pow_le_pow_left₀
      (m.original_radius_weights_bounds hA hx hkmin as ho i).1
      (m.original_radius_weights_bounds hA hx hkmin as ho i).2 2)
    Hhigh (fun i hi=>by have H:=Hcut i hi;linarith)

theorem original_radius_covariance_le_filled_of_mesh
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh a z kmin : ℝ} (hm : PartitionMesh mesh 0 as) (hm0 : 0  ≤  mesh)
    (ha : m.rmin<a) (haz : a ≤ z) (hz : z ≤ 1) (hkmin : 0<kmin)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo a z)
    (hcutMesh : mesh ≤ m.alpha.val.val a/2) (hwallMesh : mesh ≤ m.alpha.val.val a-m.u0) :
    let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A 1 kmin
    let w:=comparisonOriginalRadiusWeights m.q as f
    (∑i,pathMassDifferences (sampleClockSteps m.q 0 as) 0 i*w i*
      actualCutCovarianceEnergy (m.n+1) (sampleClockSteps m.q 0 as) (m.q 0) i.val) ≤ 
      (2*(∫r,deriv m.alpha.val.val r*m.unitColumn as Finset.univ id w r
        ∂m.radiusMeasure dphys e as ho)+2*(mesh*(1/kmin)))/(m.alpha.val.val a/2)^2 := by
  let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A 1 kmin
  let w:=comparisonOriginalRadiusWeights m.q as f
  have ha1 : a ≤ 1:=haz.trans hz
  have haI : a∈Icc m.rmin 1:=⟨ha.le,ha1⟩
  have hapos:=m.profile_pos ha ha1
  have hw i : w i∈Icc (0:ℝ) (1/kmin):=by
    simpa only [one_mul] using m.original_radius_weights_bounds hA (by norm_num : (0:ℝ)<1) hkmin as ho i
  have Hcut (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi : w i≠0) :
      m.alpha.val.val a-mesh ≤ physicalCutMass 0 (sampleClockSteps m.q 0 as) i.val:=
    m.originalWeights_native_cut_floor haI hAD 1 kmin as ho hm i hi
  have Hhigh (i : Fin ((sampleClockSteps m.q 0 as).length+1)) (hi : w i≠0) :
      m.u0 ≤ partitionPoint 0 as i.val:=by
    have HC:=Hcut i hi
    have hit : i.val ≤ as.length:=by have H:=i.isLt;simp only [sampleClockSteps_length] at H;omega
    rw [physicalCutMass_sampleClockSteps m.q 0 as i.val hit] at HC
    linarith
  exact m.original_weight_covariance_le_filled dphys e as ho he hm hm0 w (fun i=>(hw i).1)
    (by positivity) (by positivity) (fun i=>(hw i).2) Hhigh
    (fun i hi=>by have H:=Hcut i hi;linarith)

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
