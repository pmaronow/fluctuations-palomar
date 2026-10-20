module

public import ComparisonActualHighWallThetaZeroInitialCapUnitTrace
public import ComparisonActualHighWallThetaZeroContactWeightTracePositiveOrigin

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {W : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.cap_contact_weight_trace_eventually_positive_origin (P : W.Potential)
    (hN : 1≤ W.data.N) (hlog : 1≤ Real.log W.data.N) (hnd : 1/W.data.N≤ W.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval W P)
    {ag zg lo hi K : ℝ} (hag : W.data.rmin≤ ag) (hagz : ag≤ zg) (hzg : zg≤1)
    (hlo : 0≤ lo) (hK : 1≤ K)
    (hband : hi+comparisonSmallMass W.data.N W.data.E≤ K*(lo+comparisonSmallMass W.data.N W.data.E))
    (hga : ∀i,ag≤(c i).left) (hgz : ∀i,(c i).right≤ zg)
    (haH : ∀i,P.H (c i).left=0 ∨ (c i).left=W.data.rmin) (hzH : ∀i,P.H (c i).right=0 ∨ (c i).right=1)
    (hinitialU : ∀i,(c i).left=W.data.rmin → comparisonSmallMass W.data.N W.data.E≤
      W.alpha.val.val (c i).right-W.alpha.val.val (c i).left)
    (hamass : ∀i,lo≤ W.alpha.val.val (c i).left) (hzmass : ∀i,W.alpha.val.val (c i).right≤ hi)
    (weight : ι→ℝ) (hweight : ∀i,0≤ weight i)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (w : ℝ→ℝ) (hw : Measurable w) {Wbound : ℝ} (hwb : ∀r,‖w r‖≤ Wbound) (hw0 : ∀r,0≤ w r)
    {epsilon : ℝ} (hepsilon : 0< epsilon) :
    let A:=Ioo ag zg∩P.contactSet
    let C:=27*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg)
    ∀ᶠj : ℕ in atTop,
      (∑i,weight i*(∫r in Ioo (c i).left (c i).right,deriv W.alpha.val.val r
        ∂W.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j)))+
      (∫r in A,deriv W.alpha.val.val r*w r∂W.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      C*(2*K^2*(∑i,weight i*(W.alpha.val.val (c i).right-W.alpha.val.val (c i).left))+
        (∫r in A,deriv W.alpha.val.val r*w r))+epsilon := by
  dsimp only
  let C:=27*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg)
  let totalWeight:=∑i,weight i
  have htw : 0≤ totalWeight:=Finset.sum_nonneg (fun i _=>hweight i)
  let err:=epsilon/(2*(totalWeight+1))
  have herr : 0< err:=div_pos hepsilon (by positivity)
  have hcommon (r : ℝ) : (9*Real.log W.data.N)/
      ((n+1:ℝ)*(((1/3)/Real.log W.data.N)*laplaceComparisonStrength W.data.d W.lam r))=
      27*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam r):=by
    field_simp [(show 0< Real.log W.data.N from by linarith).ne',
      (laplaceComparisonStrength_pos W.data.d W.hlam r).ne']
    ring
  have hC : 0≤ C:=div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (by positivity) (laplaceComparisonStrength_pos W.data.d W.hlam zg).le)
  have hcaps : ∀i,∀ᶠj : ℕ in atTop,
      (∫r in Ioo (c i).left (c i).right,deriv W.alpha.val.val r
        ∂W.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      2*K^2*C*(W.alpha.val.val (c i).right-W.alpha.val.val (c i).left)+err:=by
    intro i
    have hratio : W.data.M (W.alpha.val.val (c i).right)/W.data.M (W.alpha.val.val (c i).left)≤ K^2:=
      comparisonCap_common_mass_band_ratio W.data.hN W.data.hU W.data.hL W.data.hE W.data.hd.le
        hlo hK hband (hamass i) (hzmass i) (W.alpha.val.property.1 (c i).right).1
    have hg:=(laplaceComparisonStrength_monotonicities W.data.hd.ne' W.hlam
      W.data.hrbounds.1.le).1
      ⟨(c i).hleft.trans (c i).hlt.le,(c i).hright⟩ ⟨hag.trans hagz,hzg⟩ (hgz i)
    have hcoef : (9*Real.log W.data.N)/
        ((n+1:ℝ)*(((1/3)/Real.log W.data.N)*laplaceComparisonStrength W.data.d W.lam (c i).right))≤ C:=by
      rw [hcommon]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by positivity) (laplaceComparisonStrength_pos W.data.d W.hlam zg))
        (mul_le_mul_of_nonneg_left hg (by positivity))
    have hmass : 0≤ W.alpha.val.val (c i).right-W.alpha.val.val (c i).left:=
      sub_nonneg.mpr (W.alpha.val.property.2 (c i).hlt.le)
    have hcoef0 : 0≤(9*Real.log W.data.N)/
        ((n+1:ℝ)*(((1/3)/Real.log W.data.N)*laplaceComparisonStrength W.data.d W.lam (c i).right)):=
      div_nonneg (by linarith) (mul_nonneg (by positivity) (mul_nonneg (by positivity)
        (laplaceComparisonStrength_pos W.data.d W.hlam _).le))
    let Ci:=(9*Real.log W.data.N)/
      ((n+1:ℝ)*(((1/3)/Real.log W.data.N)*laplaceComparisonStrength W.data.d W.lam (c i).right))
    let mass:=W.alpha.val.val (c i).right-W.alpha.val.val (c i).left
    have hprod:=mul_le_mul hratio hcoef hcoef0 (sq_nonneg K)
    have hmain : (W.data.M (W.alpha.val.val (c i).right)/W.data.M (W.alpha.val.val (c i).left))*
        Ci*mass≤K^2*C*mass:=mul_le_mul_of_nonneg_right hprod hmass
    by_cases hinitial : (c i).left=W.data.rmin
    · have hleft : W.alpha.val.val (c i).left=W.data.s:=by
        rw [hinitial]
        exact W.alpha.property.1
      have hMa : 0<W.data.M W.data.s:=(comparisonCap_first_term (δ:=delta) W.data.hN
        W.data.hU W.data.hL W.data.hE W.data.hd.le W.data.hs.1.le).1
      have heq : W.data.M (W.alpha.val.val (c i).right)*W.data.rmin=
          (comparisonSmallMass W.data.N W.data.E/2)*
            (W.data.M (W.alpha.val.val (c i).right)/W.data.M W.data.s):=by
        change W.data.M (W.alpha.val.val (c i).right)*
          (comparisonSmallMass W.data.N W.data.E/(2*W.data.M W.data.s))=_
        field_simp
      have horigin : W.data.M (W.alpha.val.val (c i).right)*W.data.rmin≤(K^2/2)*mass:=by
        rw [heq]
        have Hratio:=hratio
        rw [hleft] at Hratio
        have H1:=mul_le_mul_of_nonneg_left Hratio
          (show 0≤comparisonSmallMass W.data.N W.data.E/2 from
            (div_pos W.data.hU (by norm_num : (0:ℝ)<2)).le)
        have H2 : (K^2/2)*comparisonSmallMass W.data.N W.data.E≤(K^2/2)*mass:=
          mul_le_mul_of_nonneg_left (hinitialU i hinitial) (show 0≤K^2/2 by positivity)
        nlinarith only [H1,H2]
      have hMz : 0≤W.data.M (W.alpha.val.val (c i).right):=(comparisonCap_first_term
        (δ:=delta) W.data.hN W.data.hU W.data.hL W.data.hE W.data.hd.le
        (W.alpha.val.property.1 (c i).right).1).1.le
      have hcharge0 : 0≤W.data.M (W.alpha.val.val (c i).right)*W.data.rmin:=
        mul_nonneg hMz W.data.hrbounds.1.le
      have H1:=mul_le_mul_of_nonneg_left horigin hcoef0
      have H2:=mul_le_mul_of_nonneg_right hcoef
        (show 0≤(K^2/2)*mass from
          mul_nonneg (div_nonneg (sq_nonneg K) (by norm_num : (0:ℝ)≤2)) hmass)
      have hr:=(c i).unit_trace_eventually_with_origin hN hlog hnd dphys e
        ⟨Or.inr hinitial,hzH i⟩ as mesh ho hend hmesh hmesh0 hlim herr
      filter_upwards [hr] with j hj
      dsimp only [Ci,mass] at hmain H1 H2 ⊢
      nlinarith only [hj,hmain,H1,H2,mul_nonneg (mul_nonneg (sq_nonneg K) hC) hmass]
    · have hleft : W.data.rmin<(c i).left:=lt_of_le_of_ne (c i).hleft (Ne.symm hinitial)
      have hr:=(c i).unit_trace_eventually_strict hN hlog hnd dphys e hleft
        ((haH i).resolve_right hinitial) (hzH i) as mesh ho hend hmesh hmesh0 hlim herr
      filter_upwards [hr] with j hj
      dsimp only [Ci,mass] at hmain ⊢
      nlinarith only [hj,hmain,mul_nonneg (mul_nonneg (sq_nonneg K) hC) hmass]
  have hcontact:=P.contact_weight_trace_eventually_positive_origin hN hlog hnd dphys e as mesh ho hend
    hmesh hmesh0 hlim hag hagz hzg w hw hwb hw0 (show 0< epsilon/2 by positivity)
  filter_upwards [Filter.eventually_all.mpr hcaps,hcontact] with j hj hcont
  have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>mul_le_mul_of_nonneg_left (hj i) (hweight i))
  have hs' : (∑i,weight i*(∫r in Ioo (c i).left (c i).right,deriv W.alpha.val.val r
      ∂W.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j)))≤
      2*K^2*C*(∑i,weight i*(W.alpha.val.val (c i).right-W.alpha.val.val (c i).left))+err*totalWeight:=by
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

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
