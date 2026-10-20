module

public import ComparisonActualHighWallThetaZeroContactTrace
public import ComparisonActualHighWallThetaZeroCapComponents
public import ComparisonActualHighWallThetaZeroTraceLimitPositiveOrigin
public import ComparisonShiftedNativePositiveOriginMovingWeights

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 12000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {W : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

theorem Potential.contact_weight_trace_eventually_positive_origin (P : W.Potential)
    (hN : 1≤ W.data.N) (hlog : 1≤ Real.log W.data.N) (hnd : 1/W.data.N≤ W.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {ag zg : ℝ} (hag : W.data.rmin≤ ag) (hagz : ag≤ zg) (hzg : zg≤1)
    (w : ℝ→ℝ) (hw : Measurable w) {Wbound : ℝ} (hwb : ∀r,‖w r‖≤ Wbound) (hw0 : ∀r,0≤ w r)
    {epsilon : ℝ} (hepsilon : 0< epsilon) :
    let A:=Ioo ag zg∩P.contactSet
    let C:=27*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg)
    ∀ᶠj : ℕ in atTop,
      (∫r in A,deriv W.alpha.val.val r*w r∂W.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
        C*(∫r in A,deriv W.alpha.val.val r*w r)+epsilon := by
  dsimp only
  let m:=W.shiftedNativeModel
  let A:=Ioo ag zg∩P.contactSet
  let weight:=fun r=>deriv W.alpha.val.val r*w r
  let F:=(n+1:ℝ)*(((1/3)/Real.log W.data.N)*laplaceComparisonStrength W.data.d W.lam zg)
  have hA : MeasurableSet A:=measurableSet_Ioo.inter P.contactSet_measurable
  have hAD : A⊆Ioo ag zg:=inter_subset_left
  have hweight : Measurable weight:=(stronglyMeasurable_deriv W.alpha.val.val).measurable.mul hw
  have hb r (hr : r∈A) : ‖weight r‖≤ W.data.M 1*Wbound:=by
    have hri : r∈Ioo W.data.rmin 1:=⟨hag.trans_lt hr.1.1,hr.1.2.trans_le hzg⟩
    have hd : ‖deriv W.alpha.val.val r‖≤ W.data.M 1:=
      norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hri.1 hri.2)
        (inverseIntegralConstraints_lipschitz W.data.hm W.data.hM W.alpha.property)
    exact (norm_mul _ _).le.trans (mul_le_mul hd (hwb r) (norm_nonneg _) W.data.hM)
  have hweight0 r : 0≤ weight r:=mul_nonneg W.alpha.val.property.2.deriv_nonneg (hw0 r)
  have hiW : IntegrableOn weight A:=m.radiusWeight_integrableOn_positive_origin hag hzg A hA hAD w hw hwb
  have hAC:=W.radiusS_absolutelyContinuous_positive_origin dphys e hag hagz hzg
  have hiD : IntegrableOn (deriv W.radiusS) A:=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hagz).mp hAC.intervalIntegrable_deriv).mono_set
      (hAD.trans Ioo_subset_Icc_self)
  have hiProd : IntegrableOn (fun r=>weight r*deriv W.radiusS r) A:=
    hiD.bdd_mul hweight.aestronglyMeasurable.restrict (by
      filter_upwards [ae_restrict_mem hA] with r hr
      exact hb r hr)
  have Hnumeric : (∫r in A,weight r*deriv W.radiusS r)≤
      (9*Real.log W.data.N)*(∫r in A,weight r):=by
    rw [←integral_const_mul]
    apply integral_mono_ae hiProd (hiW.const_mul _)
    filter_upwards [ae_restrict_mem hA,ae_restrict_of_ae (P.contact_ae_deriv_le hN hlog hnd)]
      with r hr hd
    have H:=hd hr.2.1 hr.2.2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left H (hweight0 r)
  have ht:=W.radius_trace_boundedWeight_positive_origin hN hlog hnd dphys e as ho hend mesh hmesh hmesh0 hlim
    hag hagz hzg hA hAD weight hweight.aestronglyMeasurable (W.data.M 1*Wbound) hb
    (fun r _=>hweight0 r) hepsilon
  have hF : 0< F:=mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos W.data.d W.hlam zg))
  have hcommon : (9*Real.log W.data.N)/F=
      27*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg):=by
    dsimp only [F]
    field_simp [(show 0< Real.log W.data.N from by linarith).ne',
      (laplaceComparisonStrength_pos W.data.d W.hlam zg).ne']
    ring
  filter_upwards [ht] with j hj
  apply hj.trans
  have HH:=div_le_div_of_nonneg_right Hnumeric hF.le
  have HE : ((9*Real.log W.data.N)*(∫r in A,weight r))/F=
      ((9*Real.log W.data.N)/F)*(∫r in A,weight r):=by ring
  rw [HE,hcommon] at HH
  exact add_le_add HH le_rfl

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
