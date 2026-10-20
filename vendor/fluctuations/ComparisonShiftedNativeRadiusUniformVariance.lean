module

public import ComparisonShiftedNativeRadiusOriginalWeights
public import ComparisonNativeRadiusUniformIntervals

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000
attribute [local instance] Classical.propDecidable
namespace ShiftedNativeBandModel
variable (m : ShiftedNativeBandModel)

theorem dominated_radius_variance_le_filled_of_mesh
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (m.n+1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (he : partitionEnd 0 as=1)
    {mesh a z x kmin : ℝ} (hm : PartitionMesh mesh 0 as) (hm0 : 0 ≤ mesh)
    (ha : m.rmin < a) (haz : a ≤ z) (hz : z ≤ 1) (hx : 0 < x) (hkmin : 0 < kmin)
    {A : Set ℝ} (hA : MeasurableSet A) (hAD : A⊆Ioo a z)
    (hcutMesh : mesh ≤ m.alpha.val.val a/2) (hwallMesh : mesh ≤ m.alpha.val.val a-m.u0) :
    let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
    let orig:=comparisonOriginalRadiusWeights m.q as f
    comparisonDominatedRadiusVarianceBound (m.n+1) m.q as f
      ((2*(∫r,deriv m.alpha.val.val r*m.unitColumn as Finset.univ id (fun i=>(orig i)^2) r
        ∂m.radiusMeasure dphys e as ho)+2*(mesh*(1/(x*kmin))^2))/(m.alpha.val.val a/2)) := by
  dsimp only
  let f:=comparisonRadiusMassWeight m.R m.alpha.val.val A x kmin
  let orig:=comparisonOriginalRadiusWeights m.q as f
  let steps:=sampleClockSteps m.q 0 as
  have hs:=sampleClockSteps_ordered m.q as ho
  have hapos:=m.profile_pos ha (haz.trans hz)
  have Hcut (i : Fin (steps.length+1)) (hi : orig i≠0) :
      m.alpha.val.val a-mesh ≤ physicalCutMass 0 steps i.val:=
    m.originalWeights_native_cut_floor ⟨ha.le,haz.trans hz⟩ hAD x kmin as ho hm i hi
  have Hhigh (i : Fin (steps.length+1)) (hi : orig i≠0) :
      m.u0 ≤ partitionPoint 0 as i.val:=by
    have HC:=Hcut i hi
    have hit : i.val ≤ as.length:=by have H:=i.isLt;simp only [steps,sampleClockSteps_length] at H;omega
    rw [physicalCutMass_sampleClockSteps m.q 0 as i.val hit] at HC
    linarith
  have Hfilled:=m.weightedSquareEnergy_le_integral dphys e as ho he hm hm0
    (m.coefficientRows as orig) id (fun i=>(orig i)^2) (fun i=>sq_nonneg _)
    (sq_nonneg _) (fun i=>pow_le_pow_left₀
      (m.original_radius_weights_bounds hA hx hkmin as ho i).1
      (m.original_radius_weights_bounds hA hx hkmin as ho i).2 2)
    (fun i hi=>Hhigh i (Finset.mem_filter.mp hi).2)
  have HC:=m.coefficientRows_column_eq as orig 2 (by norm_num)
  unfold nativeWeightedSquareEnergy at Hfilled
  rw [HC,m.coefficientRows_unitColumn_eq as orig 2 (by norm_num)] at Hfilled
  intro coeff hcoeff
  have HCcut (i : Fin (steps.length+1)) (hi : coeff i≠0) :
      m.alpha.val.val a/2 ≤ physicalCutMass 0 steps i.val:=by
    have HO : orig i≠0:=by intro HH;have HA:=hcoeff i;change coeff i∈Icc (0:ℝ) (orig i) at HA;rw [HH] at HA;exact hi (le_antisymm HA.2 HA.1)
    have HH:=Hcut i HO
    linarith
  have Hvar:=physical_radius_weight_variance_le_source_square (m.n+1) steps hs (m.q 0)
    coeff (by positivity : 0 < m.alpha.val.val a/2) HCcut
  have Hmono:=nativeWeightedSquareEnergy_square_mono (m.n+1) steps hs (m.q 0) coeff orig hcoeff
  unfold nativeWeightedSquareEnergy at Hmono
  simp only [nativeSelectedColumn_atIndex,Finset.mem_univ,ite_true,id_eq] at Hvar Hmono Hfilled
  exact Hvar.trans (div_le_div_of_nonneg_right (Hmono.trans Hfilled) (by positivity))

end ShiftedNativeBandModel
end OAI.SKFluctuations.LaplaceWindowFormalization
