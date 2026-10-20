module

public import RadiusCellEnergySupport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

def comparisonPhysicalRadiusFiniteMeasure (n dphys : ℕ)
    (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (d lam : ℝ) (b h : ℝ→ℝ)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) : FiniteMeasure ℝ :=
  ⟨comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α as ho,inferInstance⟩

theorem comparisonPhysicalRadiusMeasure_interval_le_fixedStrength
    {N d lam p q z mesh : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N)
    (hd : 0 < d) (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M) (as : List PositiveMass)
    (ho : MassOrdered 0 as) (hend : partitionEnd 0 as=1)
    (hmesh : PartitionMesh mesh 0 as) (hmesh0 : 0 ≤ mesh)
    (hp : 0 < p) (hpq : p ≤ q) (hqz : q ≤ z) (hz : z ≤ 1) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let clock := completedPathClock (n+1) bf hf
    let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
      clockVariationBound (physicalFeatureCoordinateBound n) clock
    comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α as ho (Ioo p q) ≤
      ENNReal.ofReal ((S q-S p)/F)+ENNReal.ofReal (2*(mesh*Cnode)/F+2*(mesh/c)) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let clock := completedPathClock (n+1) bf hf
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let Fq := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam q)
  let Cnode := 2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) clock
  have hκ : 0 < (1/3)/Real.log N := div_pos (by norm_num) (by linarith)
  have hF : 0 < F := mul_pos (by positivity) (mul_pos hκ (laplaceComparisonStrength_pos d hlam z))
  have hFF : F ≤ Fq := by
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (n+1:ℝ))
    apply mul_le_mul_of_nonneg_left _ hκ.le
    exact (laplaceComparisonStrength_monotonicities hd.ne' hlam (r₀:=0) (by norm_num)).1
      ⟨hp.le.trans hpq,hqz.trans hz⟩ ⟨hp.le.trans (hpq.trans hqz),hz⟩ hqz
  have hSm := (comparisonVariableEndpoint_radius_moments hc hk hkc hm hM (n+1)
    (by omega) b h hd.ne' hlam.le hlb hb hh hh0 α).1
  have hSp : 0 ≤ S q-S p := sub_nonneg.mpr (hSm ⟨hp.le,hpq.trans (hqz.trans hz)⟩
    ⟨hp.le.trans hpq,hqz.trans hz⟩ hpq)
  have had := comparisonVariableEndpoint_clocks_admissible hc hk hkc hm hM b h
    hd.ne' hlam.le hlb hb hh hh0 α
  have hCn : 0 ≤ Cnode := mul_nonneg
    (mul_nonneg (by norm_num) (ClockTree.errorJetVariation_nonneg _ _ _))
    (clockVariationBound_nonneg (physicalFeatureCoordinateBound n) clock
      (completedPathClock_monotone (n+1) (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)))
  have ht := comparisonPhysicalRadiusMeasure_interval_le hc hk hkc hm hM hN hlog hd hnd
    hlam hld n dphys e b h hb hh hh0 hlb α as ho hend hmesh hmesh0 hp hpq (hqz.trans hz)
  dsimp only at ht
  apply ht.trans
  apply add_le_add
  · apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_left hSp hF hFF
  · apply ENNReal.ofReal_le_ofReal
    have ht := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*(mesh*Cnode)) hF hFF
    dsimp only [F,Fq,Cnode,clock,bf,hf,R] at ht
    linarith
end
end OAI.SKFluctuations.LaplaceWindowFormalization
