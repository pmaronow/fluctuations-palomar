module

public import ComparisonActualHighOnlyTraceLimit
public import ComparisonActualHighOnlyCapComponents
public import ComparisonNativeRegularContactTrace
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

theorem Potential.contact_weight_trace_smooth_eventually (P : a.Potential)
    (hN : 1≤ a.data.N) (hlog : 1≤ Real.log a.data.N) (hnd : 1/a.data.N≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {ag zg : ℝ} (hag : (0:ℝ)< ag) (hagz : ag≤ zg) (hzg : zg≤1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc ag zg))
    (hfield : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc ag zg))
    (w : ℝ→ℝ) (hw : Measurable w) {W : ℝ} (hwb : ∀r,‖w r‖≤ W) (hw0 : ∀r,0≤ w r)
    {epsilon : ℝ} (hepsilon : 0< epsilon) :
    let A:=Ioo ag zg∩P.contactSet
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) zg)
    ∀ᶠj : ℕ in atTop,
      (∫r in A,deriv a.alpha.val.val r*w r∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j))≤
        C*(∫r in A,deriv a.alpha.val.val r*w r)+epsilon := by
  dsimp only
  let m:=a.shiftedNativeModel
  let A:=Ioo ag zg∩P.contactSet
  let weight:=fun r=>deriv a.alpha.val.val r*w r
  let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*(laplaceComparisonStrength a.data.d a.lam) zg)
  have hA : MeasurableSet A:=measurableSet_Ioo.inter P.contactSet_measurable
  have hAD : A⊆Ioo ag zg:=inter_subset_left
  have hweight : Measurable weight:=(stronglyMeasurable_deriv a.alpha.val.val).measurable.mul hw
  have hb r (hr : r∈A) : ‖weight r‖≤ a.data.M 1*W:=by
    have hri : r∈Ioo (0:ℝ) 1:=⟨hag.trans hr.1.1,hr.1.2.trans_le hzg⟩
    have hd : ‖deriv a.alpha.val.val r‖≤ a.data.M 1:=
      norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hri.1 hri.2)
        (inverseIntegralConstraints_lipschitz a.data.hm a.data.hM a.alpha.property)
    exact (norm_mul _ _).le.trans (mul_le_mul hd (hwb r) (norm_nonneg _) a.data.hM)
  have hweight0 r : 0≤ weight r:=mul_nonneg a.alpha.val.property.2.deriv_nonneg (hw0 r)
  have hiW : IntegrableOn weight A:=m.radiusWeight_integrableOn hag hzg A hA hAD w hw hwb
  have hAC:=a.radiusS_absolutelyContinuous dphys e hag hagz hzg Kb Kh hparent hfield
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
    hag hagz hzg Kb Kh hparent hfield hA hAD weight hweight.aestronglyMeasurable (a.data.M 1*W) hb
    (fun r _=>hweight0 r) hepsilon
  have hF : 0< F:=mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith))
    (laplaceComparisonStrength_pos a.data.d a.hlam zg))
  have hcommon : (9*Real.log a.data.N)/F=
      27*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) zg):=by
    dsimp only [F]
    field_simp [(show 0< Real.log a.data.N from by linarith).ne',
      (laplaceComparisonStrength_pos a.data.d a.hlam zg).ne']
    ring
  filter_upwards [ht] with j hj
  apply hj.trans
  have HH:=div_le_div_of_nonneg_right Hnumeric hF.le
  have HE : ((9*Real.log a.data.N)*(∫r in A,weight r))/F=
      ((9*Real.log a.data.N)/F)*(∫r in A,weight r):=by ring
  rw [HE,hcommon] at HH
  exact add_le_add HH le_rfl

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
