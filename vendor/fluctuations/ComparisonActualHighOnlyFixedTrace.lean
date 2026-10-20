module

public import ComparisonActualHighOnlyCapTraceNormalized
public import ComparisonActualHighOnlyRegularContactTrace
public import ComparisonShiftedNativeMovingWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.cap_contact_weight_trace_eventually (P : a.Potential)
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval a P)
    {ag zg lo hi K : ℝ} (hag : (0:ℝ)< ag) (hagz : ag≤ zg) (hzg : zg≤1)
    (hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h ag zg)
    (hlo : 0≤ lo) (hK : 1≤ K)
    (hband : hi+comparisonSmallMass a.data.N a.data.E≤ K*(lo+comparisonSmallMass a.data.N a.data.E))
    (hga : ∀i,ag≤(c i).left) (hgz : ∀i,(c i).right≤ zg)
    (haH : ∀i,P.H (c i).left=0) (hzH : ∀i,P.H (c i).right=0 ∨ (c i).right=1)
    (hamass : ∀i,lo≤ a.alpha.val.val (c i).left) (hzmass : ∀i,a.alpha.val.val (c i).right≤ hi)
    (weight : ι→ℝ) (hweight : ∀i,0≤ weight i)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (w : ℝ→ℝ) (hw : Measurable w) {W : ℝ} (hwb : ∀r,‖w r‖≤ W) (hw0 : ∀r,0≤ w r)
    {epsilon : ℝ} (hepsilon : 0< epsilon) :
    let A:=Ioo ag zg∩P.contactSet
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) zg)
    ∀ᶠj : ℕ in atTop,
      (∑i,weight i*(∫r in Ioo (c i).left (c i).right,deriv a.alpha.val.val r
        ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j)))+
      (∫r in A,deriv a.alpha.val.val r*w r∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      C*(K^2*(∑i,weight i*(a.alpha.val.val (c i).right-a.alpha.val.val (c i).left))+
        (∫r in A,deriv a.alpha.val.val r*w r))+epsilon := by
  dsimp only
  let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) zg)
  let totalWeight:=∑i,weight i
  have htw : 0≤ totalWeight:=Finset.sum_nonneg (fun i _=>hweight i)
  let err:=epsilon/(2*(totalWeight+1))
  have herr : 0< err:=div_pos hepsilon (by positivity)
  have hcommon (r : ℝ) : (9*Real.log a.data.N)/
      ((n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) r))=
      27*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) r):=by
    field_simp [(show 0< Real.log a.data.N from by linarith).ne',
      (laplaceComparisonStrength_pos a.data.d a.hlam r).ne']
    ring
  have hC : 0≤ C:=div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (by positivity) (laplaceComparisonStrength_pos a.data.d a.hlam zg).le)
  have hcaps : ∀i,∀ᶠj : ℕ in atTop,
      (∫r in Ioo (c i).left (c i).right,deriv a.alpha.val.val r
        ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      K^2*C*(a.alpha.val.val (c i).right-a.alpha.val.val (c i).left)+err:=by
    intro i
    have hr:=(c i).unit_trace_eventually hN hlog hnd dphys e (hag.trans_le (hga i))
      (haH i) (hzH i) as mesh ho hend hmesh hmesh0 hlim herr
    have hratio : a.data.M (a.alpha.val.val (c i).right)/a.data.M (a.alpha.val.val (c i).left)≤ K^2:=
      comparisonCap_common_mass_band_ratio a.data.hN a.data.hU a.data.hL a.data.hE a.data.hd.le
        hlo hK hband (hamass i) (hzmass i) (a.alpha.val.property.1 (c i).right).1
    have hg:=(laplaceComparisonStrength_monotonicities a.data.hd.ne' a.hlam
      (le_refl (0:ℝ))).1
      ⟨(c i).hleft.trans (c i).hlt.le,(c i).hright⟩ ⟨hag.le.trans hagz,hzg⟩ (hgz i)
    have hcoef : (9*Real.log a.data.N)/
        ((n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) (c i).right))≤ C:=by
      rw [hcommon]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by positivity) (laplaceComparisonStrength_pos a.data.d a.hlam zg))
        (mul_le_mul_of_nonneg_left hg (by positivity))
    have hmass : 0≤ a.alpha.val.val (c i).right-a.alpha.val.val (c i).left:=
      sub_nonneg.mpr (a.alpha.val.property.2 (c i).hlt.le)
    have hcoef0 : 0≤(9*Real.log a.data.N)/
        ((n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) (c i).right)):=
      div_nonneg (by linarith) (mul_nonneg (by positivity) (mul_nonneg (by positivity)
        (laplaceComparisonStrength_pos a.data.d a.hlam _).le))
    have hprod:=mul_le_mul hratio hcoef hcoef0 (sq_nonneg K)
    filter_upwards [hr] with j hj
    exact hj.trans (add_le_add (mul_le_mul_of_nonneg_right hprod hmass) le_rfl)
  have hcontact:=P.contact_weight_trace_eventually hN hlog hnd dphys e as mesh ho hend
    hmesh hmesh0 hlim hag hagz hzg hclock w hw hwb hw0 (show 0< epsilon/2 by positivity)
  filter_upwards [Filter.eventually_all.mpr hcaps,hcontact] with j hj hcont
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>mul_le_mul_of_nonneg_left (hj i) (hweight i))
  have hs' : (∑i,weight i*(∫r in Ioo (c i).left (c i).right,deriv a.alpha.val.val r
      ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j)))≤
      K^2*C*(∑i,weight i*(a.alpha.val.val (c i).right-a.alpha.val.val (c i).left))+err*totalWeight:=by
    convert hs using 1
    dsimp only [totalWeight]
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have herrbound : err*totalWeight≤ epsilon/2:=by
    dsimp only [err]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0<2*(totalWeight+1))).mpr
    nlinarith
  dsimp only [C] at hs' hcont ⊢
  nlinarith

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
