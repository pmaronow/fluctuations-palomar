module

public import ComparisonActualHighWallCapTrace
public import ComparisonShiftedNativeMovingWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace ActualHighWallOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.contact_weight_trace_eventually (P : a.Potential)
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {ag zg : ℝ} (hag : a.data.rmin< ag) (hagz : ag≤ zg) (hzg : zg≤1)
    (w : ℝ→ℝ) (hw : Measurable w) {W : ℝ} (hwb : ∀r,‖w r‖≤ W) (hw0 : ∀r,0≤ w r)
    {epsilon : ℝ} (hepsilon : 0< epsilon) :
    let A:=Ioo ag zg∩P.contactSet
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g zg)
    ∀ᶠj : ℕ in atTop,
      (∫r in A,deriv a.alpha.val.val r*w r∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
        C*(∫r in A,deriv a.alpha.val.val r*w r)+epsilon := by
  dsimp only
  let m:=a.shiftedNativeModel
  let A:=Ioo ag zg∩P.contactSet
  let weight:=fun r=>deriv a.alpha.val.val r*w r
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*a.data.g zg)
  have hA : MeasurableSet A:=measurableSet_Ioo.inter P.contactSet_measurable
  have hAD : A⊆Ioo ag zg:=inter_subset_left
  have hweight : Measurable weight:=(stronglyMeasurable_deriv a.alpha.val.val).measurable.mul hw
  have hb r (hr : r∈A) : ‖weight r‖≤ a.data.M 1*W:=by
    have hri : r∈Ioo a.data.rmin 1:=⟨hag.trans hr.1.1,hr.1.2.trans_le hzg⟩
    have hd : ‖deriv a.alpha.val.val r‖≤ a.data.M 1:=
      norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hri.1 hri.2)
        (inverseIntegralConstraints_lipschitz a.data.hm a.data.hM a.alpha.property)
    exact (norm_mul _ _).le.trans (mul_le_mul hd (hwb r) (norm_nonneg _) a.data.hM)
  have hweight0 r : 0≤ weight r:=mul_nonneg a.alpha.val.property.2.deriv_nonneg (hw0 r)
  have hiW : IntegrableOn weight A:=m.radiusWeight_integrableOn hag hzg A hA hAD w hw hwb
  have hAC:=a.radiusS_absolutelyContinuous dphys e hag hagz hzg
  have hiD : IntegrableOn (deriv a.radiusS) A:=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hagz).mp hAC.intervalIntegrable_deriv).mono_set
      (hAD.trans Ioo_subset_Icc_self)
  have hiProd : IntegrableOn (fun r=>weight r*deriv a.radiusS r) A:=
    hiD.bdd_mul hweight.aestronglyMeasurable.restrict (by
      filter_upwards [ae_restrict_mem hA] with r hr
      exact hb r hr)
  have Hnumeric : (∫r in A,weight r*deriv a.radiusS r)≤
      (9*Real.log a.data.N)*(∫r in A,weight r):=by
    rw [←integral_const_mul]
    apply integral_mono_ae hiProd (hiW.const_mul _)
    filter_upwards [ae_restrict_mem hA,ae_restrict_of_ae (P.contact_ae_deriv_le hN hlog hnd)]
      with r hr hd
    have H:=hd hr.2.1 hr.2.2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left H (hweight0 r)
  have ht:=a.radius_trace_boundedWeight hN hlog hnd dphys e as ho hend mesh hmesh hmesh0 hlim
    hag hagz hzg hA hAD weight hweight.aestronglyMeasurable (a.data.M 1*W) hb
    (fun r _=>hweight0 r) hepsilon
  have hF : 0< F:=mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos a.data.d (sq_pos_of_pos a.data.hd) zg))
  have hcommon : (9*Real.log a.data.N)/F=
      27*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g zg):=by
    dsimp only [F]
    field_simp [(show 0< Real.log a.data.N from by linarith).ne',
      (laplaceComparisonStrength_pos a.data.d (sq_pos_of_pos a.data.hd) zg).ne']
    ring
  filter_upwards [ht] with j hj
  apply hj.trans
  have HH:=div_le_div_of_nonneg_right Hnumeric hF.le
  have HE : ((9*Real.log a.data.N)*(∫r in A,weight r))/F=
      ((9*Real.log a.data.N)/F)*(∫r in A,weight r):=by ring
  rw [HE,hcommon] at HH
  exact add_le_add HH le_rfl

theorem Potential.cap_contact_weight_trace_eventually (P : a.Potential)
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    {ι : Type*} [Fintype ι] (c : ι→ShiftedCapInterval a P)
    {ag zg lo hi K : ℝ} (hag : a.data.rmin< ag) (hagz : ag≤ zg) (hzg : zg≤1)
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
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g zg)
    ∀ᶠj : ℕ in atTop,
      (∑i,weight i*(∫r in Ioo (c i).left (c i).right,deriv a.alpha.val.val r
        ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j)))+
      (∫r in A,deriv a.alpha.val.val r*w r∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
      C*(K^2*(∑i,weight i*(a.alpha.val.val (c i).right-a.alpha.val.val (c i).left))+
        (∫r in A,deriv a.alpha.val.val r*w r))+epsilon := by
  dsimp only
  let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g zg)
  let totalWeight:=∑i,weight i
  have htw : 0≤ totalWeight:=Finset.sum_nonneg (fun i _=>hweight i)
  let err:=epsilon/(2*(totalWeight+1))
  have herr : 0< err:=div_pos hepsilon (by positivity)
  have hcommon (r : ℝ) : (9*Real.log a.data.N)/
      ((n+1:ℝ)*(((1/3)/Real.log a.data.N)*a.data.g r))=
      27*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g r):=by
    field_simp [(show 0< Real.log a.data.N from by linarith).ne',
      (laplaceComparisonStrength_pos a.data.d (sq_pos_of_pos a.data.hd) r).ne']
    ring
  have hC : 0≤ C:=div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (by positivity) (laplaceComparisonStrength_pos a.data.d (sq_pos_of_pos a.data.hd) zg).le)
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
    have hg:=(laplaceComparisonStrength_monotonicities a.data.hd.ne' (sq_pos_of_pos a.data.hd)
      a.data.hrbounds.1.le).1
      ⟨(c i).hleft.trans (c i).hlt.le,(c i).hright⟩ ⟨hag.le.trans hagz,hzg⟩ (hgz i)
    have hcoef : (9*Real.log a.data.N)/
        ((n+1:ℝ)*(((1/3)/Real.log a.data.N)*a.data.g (c i).right))≤ C:=by
      rw [hcommon]
      exact div_le_div_of_nonneg_left (by positivity)
        (mul_pos (by positivity) (laplaceComparisonStrength_pos a.data.d (sq_pos_of_pos a.data.hd) zg))
        (mul_le_mul_of_nonneg_left hg (by positivity))
    have hmass : 0≤ a.alpha.val.val (c i).right-a.alpha.val.val (c i).left:=
      sub_nonneg.mpr (a.alpha.val.property.2 (c i).hlt.le)
    have hcoef0 : 0≤(9*Real.log a.data.N)/
        ((n+1:ℝ)*(((1/3)/Real.log a.data.N)*a.data.g (c i).right)):=
      div_nonneg (by linarith) (mul_nonneg (by positivity) (mul_nonneg (by positivity)
        (laplaceComparisonStrength_pos a.data.d (sq_pos_of_pos a.data.hd) _).le))
    have hprod:=mul_le_mul hratio hcoef hcoef0 (sq_nonneg K)
    filter_upwards [hr] with j hj
    exact hj.trans (add_le_add (mul_le_mul_of_nonneg_right hprod hmass) le_rfl)
  have hcontact:=P.contact_weight_trace_eventually hN hlog hnd dphys e as mesh ho hend
    hmesh hmesh0 hlim hag hagz hzg w hw hwb hw0 (show 0< epsilon/2 by positivity)
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

end ActualHighWallOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
