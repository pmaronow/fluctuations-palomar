module

public import ComparisonActualHighOnlyContactTrace
public import ComparisonActualHighOnlyRadiusSingleCutIntegral

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 4000000
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}

private theorem Potential.contact_trace_single_cut
    (P : a.Potential) (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0  ≤  mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {lo z : ℝ} (ha : 0<lo) (haz : lo ≤ z) (hz : z ≤ 1)
    (s : ℝ) (has : lo ≤ s) (hsz : s ≤ z)
    (hlocal : ∀ l r, lo ≤ l → l ≤ r → r ≤ z → (r < s ∨ s ≤ l) → ∃ Kb Kh : ℝ≥0,
      LipschitzOnWith Kb (fun t=>a.b (a.alpha.val.val t)) (Icc l r) ∧
      LipschitzOnWith Kh (fun t=>a.h (a.alpha.val.val t)) (Icc l r))
    (w : ℝ → ℝ) (hw : Measurable w) (K : ℝ) (hK : 0 ≤ K)
    (hwb : ∀r,‖w r‖ ≤ K) (hw0 : ∀r,0 ≤ w r) {ε : ℝ} (hε : 0<ε) :
    let F:=(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam z)
    ∀ᶠj in atTop,(∫r in {r | r∈Ioo lo z ∧ P.H r=0},deriv a.alpha.val.val r*w r
      ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j)) ≤ 
      ((9*Real.log a.data.N)/F)*(∫r in {r | r∈Ioo lo z ∧ P.H r=0},deriv a.alpha.val.val r*w r)+ε := by
  dsimp only
  let A := {r | r∈Ioo lo z ∧ P.H r=0}
  let weight := fun r=>deriv a.alpha.val.val r*w r
  let f := A.indicator weight
  let m:=a.shiftedNativeModel
  let mu:=fun j=>m.radiusMeasure dphys e (as j) (ho j)
  let F := fun t=>(n+1:ℝ)*(((1/3)/Real.log a.data.N)*laplaceComparisonStrength a.data.d a.lam t)
  let C := (9*Real.log a.data.N)/F z
  have hC : 0  ≤  C := by
    exact div_nonneg (by linarith) (mul_nonneg (by positivity)
      (mul_nonneg (div_nonneg (by norm_num) (by linarith))
        (laplaceComparisonStrength_pos a.data.d a.hlam z).le))
  have hdom j : mu j ≤ volume:=m.radiusMeasure_le_volume dphys e (as j) (ho j)
  have hHC : ContinuousOn P.H (Icc lo z) := P.hH.continuousOn.mono (by
    simpa only [uIcc_of_le zero_le_one] using Icc_subset_Icc ha.le hz)
  have hclosed : MeasurableSet {r | r∈Icc lo z ∧ P.H r=0} :=
    (hHC.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton).measurableSet
  have hA : MeasurableSet A := by
    have heq : A={r | r∈Icc lo z ∧ P.H r=0}∩Ioo lo z := by
      ext r
      exact ⟨fun hr=>⟨⟨Ioo_subset_Icc_self hr.1,hr.2⟩,hr.1⟩,
        fun hr=>⟨hr.2,hr.1.2⟩⟩
    rw [heq]
    exact hclosed.inter measurableSet_Ioo
  have hiw : IntegrableOn weight (Ioo lo z) :=
    m.radiusWeight_integrableOn ha hz
      (Ioo lo z) measurableSet_Ioo (Subset.refl _) w hw hwb
  have hi : IntervalIntegrable f volume lo z :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le haz).mpr (hiw.indicator hA)
  have hf : ∀r∈Icc lo z,0  ≤  f r ∧ f r  ≤  a.data.M 1*K := by
    intro r _
    by_cases hr : r∈A
    · have hr01 : r∈Ioo (0:ℝ) 1 := ⟨ha.trans hr.1.1,hr.1.2.trans_le hz⟩
      have hdα : ‖deriv a.alpha.val.val r‖  ≤  a.data.M 1 := norm_deriv_le_of_lipschitzOn
        (Icc_mem_nhds hr01.1 hr01.2) (inverseIntegralConstraints_lipschitz a.data.hm a.data.hM a.alpha.property)
      have hp : 0  ≤  weight r := mul_nonneg a.alpha.val.property.2.deriv_nonneg (hw0 r)
      have hbnd : ‖weight r‖  ≤  a.data.M 1*K := by
        dsimp only [weight]
        rw [norm_mul]
        exact mul_le_mul hdα (hwb r) (norm_nonneg _) a.data.hM
      simp only [f,indicator_of_mem hr]
      exact ⟨hp,(le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbnd)⟩
    · simp only [f,indicator_of_notMem hr]
      exact ⟨le_rfl,mul_nonneg a.data.hM hK⟩
  have heq (nu : Measure ℝ) (hnu : nu  ≤  volume) {l r : ℝ}
      (hal : lo  ≤  l) (hlr : l  ≤  r) (hrz : r  ≤  z) :
      (∫t in l..r,f t∂nu)=∫t in {t | t∈Ioo l r ∧ P.H t=0},weight t∂nu :=
    interval_integral_contact_indicator nu hnu P.H weight hal hlr hrz hA
  have hbranch {l r : ℝ} (hal : lo  ≤  l) (hlr : l  ≤  r) (hrz : r  ≤  z)
      (hside : r < s ∨ s  ≤  l) (eps : ℝ) (heps : 0 < eps) :
      ∀ᶠj in atTop,(∫t in l..r,f t∂mu j)  ≤  C*(∫t in l..r,f t)+eps := by
    obtain ⟨Kb,Kh,hbLip,hhLip⟩:=hlocal l r hal hlr hrz hside
    have ht:=P.contact_weight_trace_smooth_eventually hN hlog hnd dphys e as mesh ho hend
      hmesh hmesh0 hlim (ha.trans_le hal) hlr (hrz.trans hz) Kb Kh hbLip hhLip w hw hwb hw0 heps
    have hseteq : Ioo l r∩P.contactSet={t | t∈Ioo l r ∧ P.H t=0} := by
      ext t
      constructor
      · exact fun ht=>⟨ht.1,ht.2.2⟩
      · intro ht
        exact ⟨ht.1,⟨⟨(ha.le.trans hal).trans ht.1.1.le,ht.1.2.le.trans (hrz.trans hz)⟩,ht.2⟩⟩
    dsimp only at ht
    rw [hseteq] at ht
    have hcommon t : 27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam t)=
        (9*Real.log a.data.N)/F t := by
      dsimp only [F]
      field_simp [(show 0<Real.log a.data.N by linarith).ne',
        (laplaceComparisonStrength_pos a.data.d a.hlam t).ne']
      ring
    rw [hcommon] at ht
    have hepos t : 0 < F t := mul_pos (by positivity)
      (mul_pos (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos a.data.d a.hlam t))
    have hemono : F z  ≤  F r := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (by linarith))
      exact (laplaceComparisonStrength_monotonicities a.data.hd.ne' a.hlam (by norm_num : (0:ℝ)  ≤  0)).1
        ⟨(ha.le.trans hal).trans hlr,hrz.trans hz⟩ ⟨ha.le.trans haz,hz⟩ hrz
    have hcmono : (9*Real.log a.data.N)/F r  ≤  C :=
      div_le_div_of_nonneg_left (by linarith) (hepos z) hemono
    have hnonneg : 0  ≤  ∫t in l..r,f t := intervalIntegral.integral_nonneg hlr
      (fun t ht=>(hf t ⟨hal.trans ht.1,ht.2.trans hrz⟩).1)
    filter_upwards [ht] with j hj
    rw [heq (mu j) (hdom j) hal hlr hrz,heq volume le_rfl hal hlr hrz]
    have hscale := mul_le_mul_of_nonneg_right hcmono hnonneg
    rw [heq volume le_rfl hal hlr hrz] at hscale
    change (∫t in {t | t∈Ioo l r ∧ P.H t=0},weight t∂mu j)  ≤ 
      ((9*Real.log a.data.N)/F r)*(∫t in {t | t∈Ioo l r ∧ P.H t=0},weight t)+eps at hj
    linarith
  have ht:=interval_trace_single_cut_eventually mu hdom f has hsz hi hf hC (mul_nonneg a.data.hM hK)
    (fun p hp hps eps heps=>hbranch le_rfl hp.1 (hp.2.trans hsz) (Or.inl hps) eps heps)
    (fun eps heps=>hbranch has hsz le_rfl (Or.inr le_rfl) eps heps) hε
  filter_upwards [ht] with j hj
  simpa only [heq (mu j) (hdom j) le_rfl haz le_rfl,
    heq volume le_rfl le_rfl haz le_rfl,weight,mu,C,F] using hj

theorem Potential.contact_weight_trace_eventually
    (P : a.Potential) (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    (dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0)) {ag zg : ℝ} (hag : 0<ag) (hagz : ag ≤ zg) (hzg : zg ≤ 1)
    (hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h ag zg)
    (w : ℝ → ℝ) (hw : Measurable w) {W : ℝ} (hwb : ∀r,‖w r‖ ≤ W) (hw0 : ∀r,0 ≤ w r)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    let A:=Ioo ag zg∩P.contactSet
    let C:=27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg)
    ∀ᶠj in atTop,(∫r in A,deriv a.alpha.val.val r*w r
      ∂a.shiftedNativeModel.radiusMeasure dphys e (as j) (ho j)) ≤
      C*(∫r in A,deriv a.alpha.val.val r*w r)+epsilon := by
  have hglobal (Kb Kh : ℝ≥0)
      (hbLip : LipschitzOnWith Kb (fun r=>a.b (a.alpha.val.val r)) (Icc ag zg))
      (hhLip : LipschitzOnWith Kh (fun r=>a.h (a.alpha.val.val r)) (Icc ag zg)) :=
    P.contact_weight_trace_smooth_eventually hN hlog hnd dphys e as mesh ho hend hmesh hmesh0 hlim
      hag hagz hzg Kb Kh hbLip hhLip w hw hwb hw0 hepsilon
  rcases hclock with ⟨Kb,Kh,hbLip,hhLip⟩|⟨s,hs⟩
  · exact hglobal Kb Kh hbLip hhLip
  by_cases hleft : zg<s
  · obtain ⟨Kb,Kh,hbLip,hhLip⟩:=hs ag zg le_rfl hagz le_rfl (Or.inl hleft)
    exact hglobal Kb Kh hbLip hhLip
  by_cases hright : s ≤ ag
  · obtain ⟨Kb,Kh,hbLip,hhLip⟩:=hs ag zg le_rfl hagz le_rfl (Or.inr hright)
    exact hglobal Kb Kh hbLip hhLip
  have hW : 0 ≤ W := (norm_nonneg (w 0)).trans (hwb 0)
  have HT:=P.contact_trace_single_cut hN hlog hnd dphys e as mesh ho hend hmesh hmesh0 hlim
    hag hagz hzg s (le_of_not_ge hright) (le_of_not_gt hleft) hs w hw W hW hwb hw0 hepsilon
  have hset : {r | r∈Ioo ag zg ∧ P.H r=0}=Ioo ag zg∩P.contactSet := by
    ext r
    constructor
    · intro hr
      exact ⟨hr.1,⟨⟨hag.le.trans hr.1.1.le,hr.1.2.le.trans hzg⟩,hr.2⟩⟩
    · exact fun hr=>⟨hr.1,hr.2.2⟩
  dsimp only at HT ⊢
  rw [hset] at HT
  have hcommon : (9*Real.log a.data.N)/((n+1:ℝ)*(((1/3)/Real.log a.data.N)*
      laplaceComparisonStrength a.data.d a.lam zg))=
      27*(Real.log a.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength a.data.d a.lam zg) := by
    field_simp [(show 0<Real.log a.data.N by linarith).ne',
      (laplaceComparisonStrength_pos a.data.d a.hlam zg).ne']
    ring
  simpa only [hcommon] using HT

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
