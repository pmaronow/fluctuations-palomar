module

public import ComparisonSelectedContactSideTrace

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 1800000

def contactMeetingCells (H x : ℝ → ℝ) (nodes : ℕ → ℝ) (K : ℕ) : Set ℝ :=
  {r | ∃i<K, (∃t∈Icc (x (nodes i)) (x (nodes (i+1))), H t=0) ∧
    r∈Ioc (x (nodes i)) (x (nodes (i+1)))}

theorem contactMeetingCells_measurable (H x : ℝ → ℝ) (nodes : ℕ → ℝ) (K : ℕ) :
    MeasurableSet (contactMeetingCells H x nodes K) := by
  classical
  let S := fun i : ℕ => if i<K ∧
    (∃t∈Icc (x (nodes i)) (x (nodes (i+1))), H t=0) then
    Ioc (x (nodes i)) (x (nodes (i+1))) else ∅
  have he : contactMeetingCells H x nodes K=⋃i : ℕ, S i := by
    ext r
    simp only [contactMeetingCells, mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨i,hi,hzero,hr⟩
      exact ⟨i,by simp only [S,hi,hzero,and_self,ite_true]; exact hr⟩
    · rintro ⟨i,hr⟩
      by_cases hh : i<K ∧ (∃t∈Icc (x (nodes i)) (x (nodes (i+1))), H t=0)
      · refine ⟨i,hh.1,hh.2,?_⟩
        dsimp only [S] at hr
        rw [ite_eq_left hh] at hr
        exact hr
      · simp only [S,hh,ite_false,mem_empty_iff_false] at hr
  rw [he]
  apply MeasurableSet.iUnion
  intro i
  dsimp only [S]
  split_ifs
  · exact measurableSet_Ioc
  · exact MeasurableSet.empty

theorem contactMeetingCells_cover (H x : ℝ → ℝ) (nodes : ℕ → ℝ) (K : ℕ)
    {r : ℝ} (hstart : x (nodes 0)<r) (hend : r≤x (nodes K)) (hzero : H r=0) :
    r∈contactMeetingCells H x nodes K := by
  induction K with
  | zero => exact False.elim (not_le_of_gt hstart hend)
  | succ K ih =>
    by_cases hrK : r≤x (nodes K)
    · obtain ⟨i,hi,hcontact,hr⟩ := ih hrK
      exact ⟨i,Nat.lt_trans hi (Nat.lt_succ_self K),hcontact,hr⟩
    · have hrp : x (nodes K)<r := lt_of_not_ge hrK
      exact ⟨K,Nat.lt_succ_self K,⟨r,⟨hrp.le,hend⟩,hzero⟩,hrp,hend⟩

theorem contactMeetingCells_small_potential (H : ℝ → ℝ)
    (hH : ContinuousOn H (Icc (0:ℝ) 1)) {κ : ℝ} (hκ : 0<κ) :
    ∃δ : ℝ, 0<δ ∧ ∀p q t r : ℝ,
      p∈Icc (0:ℝ) 1 → q∈Icc (0:ℝ) 1 → q-p<δ →
      t∈Icc p q → H t=0 → r∈Ioc p q → |H r|<κ := by
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hH) κ hκ
  refine ⟨δ,hδ,?_⟩
  intro p q t r hp hq hwidth ht hzero hr
  have hrr : r∈Icc (0:ℝ) 1 := ⟨hp.1.trans hr.1.le,hr.2.trans hq.2⟩
  have htt : t∈Icc (0:ℝ) 1 := ⟨hp.1.trans ht.1,ht.2.trans hq.2⟩
  have hab : |r-t|≤q-p := abs_le.mpr ⟨by linarith [hr.1,ht.2],by linarith [hr.2,ht.1]⟩
  have hdist : dist r t<δ := by rw [Real.dist_eq]; exact hab.trans_lt hwidth
  simpa only [Real.dist_eq,hzero,sub_zero] using hclose r hrr t htt hdist

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparison_contactMeetingCells_cover
    (α : inverseIntegralConstraints 0 0 k M) (H : ℝ → ℝ)
    (as : List PositiveMass) (he : partitionEnd 0 as=1)
    {r : ℝ} (hr : r∈Ioc (0:ℝ) 1) (hzero : H r=0) :
    r∈contactMeetingCells H (comparisonSweepQuantile hc hk hkc hm hM α)
      (partitionPoint 0 as) as.length := by
  have h0 : comparisonSweepQuantile hc hk hkc hm hM α 0=0 := by
    simpa only [α.property.1] using comparisonSweepQuantile_inverse hc hk hkc hm hM α
      (show (0:ℝ)∈Icc (0:ℝ) 1 by simp)
  have h1 : comparisonSweepQuantile hc hk hkc hm hM α 1=1 := by
    simpa only [α.property.2.1] using comparisonSweepQuantile_inverse hc hk hkc hm hM α
      (show (1:ℝ)∈Icc (0:ℝ) 1 by simp)
  apply contactMeetingCells_cover H _ _ _ _ _ hzero
  · simpa only [partitionPoint,partitionValues_zero,id_eq,h0] using hr.1
  · simpa only [partitionPoint_length,he,h1] using hr.2

theorem comparison_contactMeetingCells_potential_eventually
    (α : inverseIntegralConstraints 0 0 k M) (H : ℝ → ℝ)
    (hH : AbsolutelyContinuousOnInterval H 0 1)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j))
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j))
    (hlim : Tendsto mesh atTop (𝓝 0)) {κ : ℝ} (hκ : 0<κ) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    ∀ᶠ j in atTop, ∀r∈contactMeetingCells H R (partitionPoint 0 (as j)) (as j).length,
      |H r|<κ := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  have hHC : ContinuousOn H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hH.continuousOn
  obtain ⟨δ,hδ,hclose⟩ := contactMeetingCells_small_potential H hHC hκ
  have ht : Tendsto (fun j=>mesh j/c) atTop (𝓝 0) := by
    simpa only [zero_div] using hlim.div_const c
  filter_upwards [(tendsto_order.mp ht).2 δ hδ] with j hj
  intro r hr
  obtain ⟨i,hi,⟨t,ht,hzero⟩,hr⟩ := hr
  apply hclose (R (partitionPoint 0 (as j) i))
    (R (partitionPoint 0 (as j) (i+1))) t r
    (comparisonSweepQuantile_bounds hc hk hkc hm hM α _)
    (comparisonSweepQuantile_bounds hc hk hkc hm hM α _)
    ((comparisonSampledRadius_point_mesh hc hk hkc hm hM α (as j) (ho j)
      (hmesh j) i hi).trans_lt hj) ht hzero hr

theorem comparisonPhysicalContactCoverSideSquareTrace_eventually
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d)
    (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H : ℝ→ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r=0→
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hpartEnd : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z))

    (v0 : ℝ) (x : ℕ → ℝ) (K : ℕ) {δ width : ℝ}
    (hv0 : 0 ≤ v0) (hv1 : v0+width ≤ 1)
    (hstart : x 0=0) (hxend : x K=width) (hδ : 0 < δ) (hwidth : 2*δ ≤ width)
    (hx : ∀i : Fin K, x i.val < x (i.val+1))
    (hxb : ∀i≤K, x i∈Icc (0:ℝ) width)
    {ε : ℝ} (hε : 0 < ε) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    ∀ᶠ j in atTop,
      (∫r in Ioo a z∩contactMeetingCells H R (partitionPoint 0 (as j)) (as j).length,
        deriv α.val.val r*sideSquareRadiusWeight R v0 x K δ width r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
          n dphys e d lam b h α (as j) (ho j)) ≤
      (54*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam z))*
        Real.log (width/δ)+ε := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let w := sideSquareRadiusWeight R v0 x K δ width
  let f := fun r => deriv α.val.val r*w r
  let col := fun i : Fin K => sideSquareColumn x δ width i.val
  have hcol i : 0 ≤ col i := sideSquareColumn_nonneg x hwidth i.val
  have hw : Measurable w := finiteRadiusWeight_measurable _ _ _
  have hw0 r : 0 ≤ w r := finiteRadiusWeight_nonneg _ _ _ hcol r
  have hwb r : ‖w r‖ ≤ ∑i : Fin K, col i := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hw0 r)]
    exact finiteRadiusWeight_le_sum _ _ _ hcol r
  have hαLip := inverseIntegralConstraints_lipschitz hm hM α.property
  have hfMeas : AEStronglyMeasurable f volume :=
    (stronglyMeasurable_deriv α.val.val).aestronglyMeasurable.mul
      hw.stronglyMeasurable.aestronglyMeasurable
  have hfBound r (hr : r∈Ioo a z) : ‖f r‖ ≤ (M 1)*(∑i : Fin K, col i) := by
    have hr01 : r∈Ioo (0:ℝ) 1 := ⟨ha.trans hr.1, hr.2.trans_le hz⟩
    have hderiv : ‖deriv α.val.val r‖ ≤ M 1 :=
      norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hr01.1 hr01.2) hαLip
    dsimp only [f]
    rw [norm_mul]
    exact mul_le_mul hderiv (hwb r) (norm_nonneg _) hM
  have hKf : volume (Ioo a z)≠⊤ := ne_top_of_le_ne_top
    (by simp : volume (Icc a z)≠⊤) (measure_mono Ioo_subset_Icc_self)
  have hiOne : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo a z) := integrableOn_const hKf
  have hi : IntegrableOn f (Ioo a z) := by
    simpa only [IntegrableOn, mul_one] using hiOne.bdd_mul hfMeas.restrict
      ((ae_restrict_mem measurableSet_Ioo).mono (fun r hr => hfBound r hr))
  have hf0 r (_ : r∈Ioo a z) : 0 ≤ f r :=
    mul_nonneg α.val.property.2.deriv_nonneg (hw0 r)
  let He := fun r => H (projIcc (0:ℝ) 1 zero_le_one r)
  have hHC : ContinuousOn H (Icc (0:ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using hH.continuousOn
  have hHe : Continuous He :=
    (continuousOn_iff_continuous_domRestrict.mp hHC).comp continuous_projIcc
  have heq r (hr : r∈Icc (0:ℝ) 1) : He r=H r := by
    simp only [He, projIcc_of_mem zero_le_one hr]
  have hr01 r (hr : r∈Ioo a z) : r∈Icc (0:ℝ) 1 :=
    ⟨ha.le.trans hr.1.le, hr.2.le.trans hz⟩
  let mu := fun j => comparisonPhysicalRadiusMeasure hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)
  have hdom j : mu j ≤ volume :=
    (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM
      n dphys e d lam b h α (as j) (ho j)).trans Measure.restrict_le_self
  let selected := fun j => contactMeetingCells H R (partitionPoint 0 (as j)) (as j).length
  have hcontain : ∀κ>0, ∀ᶠ j in atTop, ∀r∈selected j, r∈Ioo a z → |He r| ≤ κ := by
    intro κ hκ
    filter_upwards [comparison_contactMeetingCells_potential_eventually hc hk hkc hm hM
      α H hH as mesh ho hmesh hlim hκ] with j hj
    intro r hr hrr
    rw [heq r (hr01 r hrr)]
    exact (hj r hr).le
  let budget := (54*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam z))*
    Real.log (width/δ)
  have hcontacts : {r | r∈Ioo a z ∧ He r=0}={r | r∈Ioo a z ∧ H r=0} := by
    ext r
    constructor <;> intro hr <;> exact ⟨hr.1, by simpa only [heq r (hr01 r hr.1)] using hr.2⟩
  have hcontact : ∀ε'>0, ∀ᶠ j in atTop,
      (∫r in {r | r∈Ioo a z ∧ He r=0}, f r∂mu j) ≤ budget+ε' := by
    intro ε' hε'
    have ht := comparisonPhysicalContactSideSquareTrace_eventually hc hk hkc hm hM
      hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero
      as mesh ho hpartEnd hmesh hmesh0 hlim ha haz hz Kb Kh hparent hfield
      v0 x K hv0 hv1 hstart hxend hδ hwidth hx hxb hε'
    simpa only [hcontacts, f, w, mu, budget, R] using ht
  exact fixed_contact_neighborhood_trace_transfer He hHe.measurable (Ioo a z)
    measurableSet_Ioo f hi hf0 mu hdom selected hcontain budget hcontact hε

end

theorem exists_constantComparison_contactCoverSideSquareTrace
    {N δcap U L E d lam T : ℝ} (hN : 0 < N) (hU : 0 < U) (hL : 0 < L)
    (hLU : L ≤ U) (hE : 0 < E) (hd : 0 < d) (hq : 2 ≤ N^δcap)
    (hNlarge : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hnd : 1/N ≤ d)
    (hlam : 0 < lam) (hld : lam ≤ d^2) (hlT : lam ≤ T)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j, MassOrdered 0 (as j)) (hpartEnd : ∀j, partitionEnd 0 (as j)=1)
    (hmesh : ∀j, PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j, 0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (v0 : ℝ) (x : ℕ → ℝ) (K : ℕ) {δ width : ℝ}
    (hv0 : 0 ≤ v0) (hv1 : v0+width ≤ 1)
    (hstart : x 0=0) (hxend : x K=width) (hδ : 0 < δ) (hwidth : 2*δ ≤ width)
    (hx : ∀i : Fin K, x i.val < x (i.val+1))
    (hxb : ∀i≤K, x i∈Icc (0:ℝ) width) {ε : ℝ} (hε : 0 < ε) :
    let k := comparisonFloor N δcap U
    let M := comparisonCap N δcap U L E d
    let c := k 1
    let hc : 0 < c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δcap) hN hU (r₀:=0) le_rfl
    let hkc := fun r (hr : r∈Icc (0:ℝ) 1) =>
      comparisonFloor_lower_on (δ:=δcap) hN hU le_rfl hr
    let hm := comparisonCap_monotoneOn (δ:=δcap) hN hU.le hL hE hd.le
    let hM := comparisonCap_nonneg (δ:=δcap) hN hU.le hL hE hd.le zero_le_one
    ∃ (α : inverseIntegralConstraints 0 0 k M) (H : ℝ → ℝ),
      (∀γ : inverseIntegralConstraints 0 0 k M,
        comparisonVariableEndpointObjective hc hk hkc hm hM (n+1)
          (fun _=>T) (fun _=>0) d lam α ≤
        comparisonVariableEndpointObjective hc hk hkc hm hM (n+1)
          (fun _=>T) (fun _=>0) d lam γ) ∧
      let R := comparisonSweepQuantile hc hk hkc hm hM α
      let g := laplaceComparisonStrength d lam
      let bf := fun u=>(T-g (R u)).toNNReal
      let hf := fun u=>((0:ℝ)+g (R u)*R u).toNNReal
      let S := orderedPathS (n+1) bf hf
      let B := orderedPathB (n+1) bf hf
      let J := inverseControlFactor 0 (fun r=>inverseControlWeight α.val.val k M r*
        comparisonCapSlope N δcap U L E d (α.val.val r))
      AbsolutelyContinuousOnInterval H 0 1 ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
        (J r*radiusComparisonGradient g α.val.val S B r) r) ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→
        (H r<0→deriv α.val.val r=M (α.val.val r)) ∧
        (0<H r→deriv α.val.val r=k r)) ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→H r=0→
        radiusComparisonGradient g α.val.val S B r=0 ∧
        S (α.val.val r)≤r ∧
        (S (α.val.val r)-r)^2≤B (α.val.val r)-(S (α.val.val r))^2) ∧
      let A := fun j => Ioo a z∩contactMeetingCells H R (partitionPoint 0 (as j)) (as j).length
      (∀j, {r | r∈Ioc (0:ℝ) 1 ∧ H r=0}⊆
        contactMeetingCells H R (partitionPoint 0 (as j)) (as j).length) ∧
      ∀ᶠ j in atTop,
        (∫r in A j, deriv α.val.val r*sideSquareRadiusWeight R v0 x K δ width r
          ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
            n dphys e d lam (fun _=>T) (fun _=>0) α (as j) (ho j)) ≤
        (54*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam z))*
          Real.log (width/δ)+ε := by
  dsimp only
  let k := comparisonFloor N δcap U
  let M := comparisonCap N δcap U L E d
  have hc : 0 < k 1 := comparisonFloor_pos hN hU (by norm_num)
  have hk : ContinuousOn k (Icc (0:ℝ) 1) :=
    comparisonFloor_continuousOn (δ:=δcap) hN hU le_rfl
  have hkc : ∀r∈Icc (0:ℝ) 1, k 1 ≤ k r :=
    fun r hr => comparisonFloor_lower_on (δ:=δcap) hN hU le_rfl hr
  have hm : MonotoneOn M (Icc (0:ℝ) 1) :=
    comparisonCap_monotoneOn (δ:=δcap) hN hU.le hL hE hd.le
  have hM : 0 ≤ M 1 :=
    comparisonCap_nonneg (δ:=δcap) hN hU.le hL hE hd.le zero_le_one
  have hb : MonotoneOn (fun _ : ℝ => T) (Icc (0:ℝ) 1) := fun _ _ _ _ _ => le_rfl
  have hh : MonotoneOn (fun _ : ℝ => (0:ℝ)) (Icc (0:ℝ) 1) := fun _ _ _ _ _ => le_rfl
  obtain ⟨α,H,hmin,hH,hD,hbang,hzero⟩ := exists_concrete_variableEndpoint_optimizer_potential
    hN hU hL hLU hE hd hq hlam (fun _=>T) (fun _=>0) hb hlT hh (by norm_num)
    (n+1) (by omega)
  refine ⟨α,H,hmin,hH,hD,hbang,hzero,?_,?_⟩
  · intro j r hr
    exact comparison_contactMeetingCells_cover hc hk hkc hm hM α H (as j)
      (hpartEnd j) hr.1 hr.2
  apply comparisonPhysicalContactCoverSideSquareTrace_eventually hc hk hkc hm hM
    hNlarge hlog hd hnd hlam hld n dphys e (fun _=>T) (fun _=>0) hb hh
    (by norm_num) hlT α H hH ?_ as mesh ho hpartEnd hmesh hmesh0 hlim
    ha haz hz 0 0 (LipschitzWith.const T).lipschitzOnWith
    (LipschitzWith.const (0:ℝ)).lipschitzOnWith v0 x K hv0 hv1 hstart hxend
    hδ hwidth hx hxb hε
  filter_upwards [hzero] with r hr h01 hHr
  exact (hr h01 hHr).1

end OAI.SKFluctuations.LaplaceWindowFormalization
