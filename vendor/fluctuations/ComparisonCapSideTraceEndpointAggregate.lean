module

public import ComparisonCapSideTraceEndpointNormalized
public import ComparisonCapSideTraceAggregate

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 1800000

section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonPhysicalLeftContactCapContactTrace_eventually
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
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r=0→
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    {ag zg lo hi K : ℝ} (hag : 0<ag) (hagz : ag≤zg) (hzg : zg≤1)
    (hlo : 0≤lo) (hK : 1≤K) (hband : hi+U≤K*(lo+U))
    (a z weight : ι→ℝ) (hga : ∀i,ag≤a i) (haz : ∀i,a i<z i)
    (hgz : ∀i,z i≤zg) (haH : ∀i,H (a i)=0) (hzH : ∀i,H (z i)=0 ∨ z i=1)
    (hneg : ∀i,∀r∈Ioo (a i) (z i),H r<0)
    (hamass : ∀i,lo≤α.val.val (a i)) (hzmass : ∀i,α.val.val (z i)≤hi)
    (hweight : ∀i,0≤weight i)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc ag zg))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc ag zg))
    (w : ℝ→ℝ) (hw : Measurable w) (W : ℝ)
    (hwb : ∀r∈Ioo ag zg,H r=0→‖w r‖≤W)
    (hw0 : ∀r∈Ioo ag zg,H r=0→0≤w r)
    {ε : ℝ} (hε : 0<ε) :
    let A := {r | r∈Ioo ag zg ∧ H r=0}
    let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam zg)
    ∀ᶠ j in atTop,
      (∑i,weight i*(∫r in Ioo (a i) (z i),deriv α.val.val r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α (as j) (ho j))) +
      (∫r in A,deriv α.val.val r*w r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α (as j) (ho j)) ≤
      C*(K^2*(∑i,weight i*(α.val.val (z i)-α.val.val (a i)))+
        (∫r in A,deriv α.val.val r*w r))+ε := by
  dsimp only
  let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam zg)
  let A := {r | r∈Ioo ag zg ∧ H r=0}
  let totalWeight := ∑i,weight i
  have htw : 0≤totalWeight := Finset.sum_nonneg (fun i _=>hweight i)
  let err := ε/(2*(totalWeight+1))
  have herr : 0<err := div_pos hε (by positivity)
  have hlogpos : 0<Real.log N := by linarith
  have hcommon (r : ℝ) :
      (9*Real.log N)/((n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam r)) =
      27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam r) := by
    field_simp [hlogpos.ne',(laplaceComparisonStrength_pos d hlam r).ne']
    <;> ring
  have hC : 0≤C := by
    have hgpos := laplaceComparisonStrength_pos d hlam zg
    dsimp [C]
    positivity
  have hcaps : ∀i,∀ᶠ j in atTop,
      (∫r in Ioo (a i) (z i),deriv α.val.val r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α (as j) (ho j)) ≤
      K^2*C*(α.val.val (z i)-α.val.val (a i))+err := by
    intro i
    have ha0 : 0≤a i := (hag.trans_le (hga i)).le
    have hz1 : z i≤1 := (hgz i).trans hzg
    have hMa : 0<M (α.val.val (a i)) := by
      rw [congrFun hMdef (α.val.val (a i))]
      exact (comparisonCap_first_term (δ:=δcap) (by linarith) hU hL hE hd.le
        (α.val.property.1 (a i)).1).1
    have hr := comparisonPhysicalLeftContactCapUnitTrace_eventually hc hk hkc hm hM
      hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD hbang
      ha0 (haz i) hz1 (haH i) (hzH i) (hneg i)
      as mesh ho hend hmesh hmesh0 hlim hMa herr
    have hratio : M (α.val.val (z i))/M (α.val.val (a i))≤K^2 := by
      rw [congrFun hMdef (α.val.val (z i)),congrFun hMdef (α.val.val (a i))]
      exact comparisonCap_common_mass_band_ratio (by linarith) hU hL hE hd.le hlo
        hK hband (hamass i) (hzmass i) (α.val.property.1 (z i)).1
    have hg := (laplaceComparisonStrength_monotonicities hd.ne' hlam
      (r₀:=0) le_rfl).1
      ⟨ha0.trans (haz i).le,hz1⟩ ⟨hag.le.trans hagz,hzg⟩ (hgz i)
    have hcoef : (9*Real.log N)/
        ((n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam (z i)))≤C := by
      rw [hcommon]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by positivity) (laplaceComparisonStrength_pos d hlam zg))
        (mul_le_mul_of_nonneg_left hg (by positivity))
    have hmass : 0≤α.val.val (z i)-α.val.val (a i) :=
      sub_nonneg.mpr (α.val.property.2 (haz i).le)
    have hr0 : 0≤M (α.val.val (z i))/M (α.val.val (a i)) :=
      div_nonneg (hMa.le.trans (hm (α.val.property.1 (a i))
        (α.val.property.1 (z i)) (α.val.property.2 (haz i).le))) hMa.le
    have hc0 : 0≤(9*Real.log N)/
        ((n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam (z i))) := by
      have hgpos := laplaceComparisonStrength_pos d hlam (z i)
      positivity
    have hprod := mul_le_mul hratio hcoef hc0 (sq_nonneg K)
    filter_upwards [hr] with j hj
    exact hj.trans (add_le_add
      (mul_le_mul_of_nonneg_right hprod hmass) le_rfl)
  have hcontact := comparisonPhysicalWeightedContactTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero
    as mesh ho hend hmesh hmesh0 hlim hag hagz hzg Kb Kh hparent hfield
    w hw W hwb hw0 (show 0<ε/2 by positivity)
  have hsumcaps := Filter.eventually_all.mpr hcaps
  filter_upwards [hsumcaps,hcontact] with j hj hcont
  rw [hcommon] at hcont
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>
    mul_le_mul_of_nonneg_left (hj i) (hweight i))
  have hs' : (∑i,weight i*(∫r in Ioo (a i) (z i),deriv α.val.val r
      ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j))) ≤
      K^2*C*(∑i,weight i*(α.val.val (z i)-α.val.val (a i)))+err*totalWeight := by
    convert hs using 1
    dsimp only [totalWeight]
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have herrbound : err*totalWeight≤ε/2 := by
    dsimp only [err]
    rw [div_mul_eq_mul_div]
    have hp : 0<2*(totalWeight+1) := by positivity
    apply (div_le_iff₀ hp).mpr
    nlinarith
  dsimp only [C,A] at hs' hcont ⊢
  nlinarith [hs',hcont,herrbound]

end
end OAI.SKFluctuations.LaplaceWindowFormalization
