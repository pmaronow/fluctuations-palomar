module

public import ComparisonCapSideTraceLocalizedBroad

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonPhysicalLocalizedBroadCapTraceAggregate_eventually
    {ι : Type*} [Fintype ι]
    {N δcap U L E d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N)
    (hU : 0<U) (hL : 0<L) (hE : 0<E) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (hMdef : M=comparisonCap N δcap U L E d)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ→ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    (hbang : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r<0→deriv α.val.val r=M (α.val.val r))
    {ag zg vmax K : ℝ} (hag : 0<ag) (hzg : zg≤1)
    (hK : 1≤K) (hcal : d^3*L*U≤E)
    (a z v V weight : ι→ℝ) (ha : ∀i,0≤a i) (haz : ∀i,a i<z i) (hz : ∀i,z i≤1)
    (hoverlap : ∀i,max (a i) ag < min (z i) zg)
    (hboundary : ∀i,(H (a i)=0 ∧ H (z i)=0) ∨
      (a i=0 ∧ H (z i)=0) ∨ (H (a i)=0 ∧ z i=1))
    (hneg : ∀i,∀r∈Ioo (a i) (z i),H r<0)
    (hUv : ∀i,U≤v i) (hvmax : ∀i,v i≤vmax)
    (hV : ∀i,V i∈Icc (0:ℝ) 1) (hVv : ∀i,V i≤K*v i)
    (A : ι→Set ℝ) (hA : ∀i,MeasurableSet (A i))
    (hAcap : ∀i,A i⊆Ioo (a i) (z i)) (hAgroup : ∀i,A i⊆Ioo ag zg)
    (hAV : ∀i,∀r∈A i,α.val.val r≤V i)
    (hslice : ∀i,v i≤∫r in A i,deriv α.val.val r)
    (hweight : ∀i,0≤weight i)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ε : ℝ} (hε : 0<ε) :
    let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam zg)
    let Q := (K+1)^2*(1+vmax/U)*Real.log ((1+U)/U)
    ∀ᶠ j in atTop,
      (∑i,weight i*(∫r in A i,deriv α.val.val r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α
          (as j) (ho j))) ≤
      C*Q*(∑i,weight i*(∫r in A i,deriv α.val.val r))+ε := by
  dsimp only
  let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam zg)
  let Q := (K+1)^2*(1+vmax/U)*Real.log ((1+U)/U)
  let totalWeight := ∑i,weight i
  have htw : 0≤totalWeight := Finset.sum_nonneg (fun i _=>hweight i)
  let err := ε/(totalWeight+1)
  have herr : 0<err := div_pos hε (by linarith)
  have hC : 0≤C := by
    have hgpos := laplaceComparisonStrength_pos d hlam zg
    dsimp [C]
    positivity
  have hT : 0≤Real.log ((1+U)/U) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hU).mpr
    linarith
  have hcaps : ∀i,∀ᶠ j in atTop,
      (∫r in A i,deriv α.val.val r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α
          (as j) (ho j)) ≤ C*Q*(∫r in A i,deriv α.val.val r)+err := by
    intro i
    have ht := comparisonPhysicalLocalizedBroadCapUnitTrace_eventually hc hk hkc hm hM
      hN hlog hU hL hE hd hnd hlam hld hMdef n dphys e b h hb hlb hh hh0 α H J
      hH hJ hD hbang (ha i) (haz i) (hz i) hag hzg (hoverlap i) (hboundary i)
      (hneg i) hK (hUv i) (hV i) (hVv i) hcal (A i) (hA i) (hAcap i) (hAgroup i)
      (hAV i) (hslice i) as mesh ho hend hmesh hmesh0 hlim herr
    have hmass : 0≤∫r in A i,deriv α.val.val r :=
      integral_nonneg (fun r=>α.val.property.2.deriv_nonneg)
    have hprofile : (K+1)^2*(1+v i/U)*Real.log ((1+U)/U)≤Q := by
      apply mul_le_mul_of_nonneg_right _ hT
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact add_le_add le_rfl (div_le_div_of_nonneg_right (hvmax i) hU.le)
    have hcoef := mul_le_mul_of_nonneg_left hprofile hC
    filter_upwards [ht] with j hj
    have hscaled := mul_le_mul_of_nonneg_right hcoef hmass
    dsimp only [C,Q] at hscaled ⊢
    nlinarith
  have hsumcaps := Filter.eventually_all.mpr hcaps
  filter_upwards [hsumcaps] with j hj
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>
    mul_le_mul_of_nonneg_left (hj i) (hweight i))
  have hs' : (∑i,weight i*(∫r in A i,deriv α.val.val r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α
          (as j) (ho j))) ≤
      C*Q*(∑i,weight i*(∫r in A i,deriv α.val.val r))+err*totalWeight := by
    convert hs using 1
    dsimp only [totalWeight]
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have herrbound : err*totalWeight≤ε := by
    dsimp only [err]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by linarith : 0<totalWeight+1)).mpr
    nlinarith
  dsimp only [C,Q] at hs' ⊢
  exact hs'.trans (add_le_add le_rfl herrbound)

end
end OAI.SKFluctuations.LaplaceWindowFormalization
