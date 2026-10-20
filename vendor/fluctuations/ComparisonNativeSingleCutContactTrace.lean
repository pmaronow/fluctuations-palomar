module

public import ComparisonSingleCutTraceExtension

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 7000000
section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonPhysicalSingleCutContactTrace_eventually
    {N d lam : ℝ} (hN : 1 ≤ N) (hlog : 1 ≤ Real.log N) (hd : 0 < d)
    (hnd : 1/N ≤ d) (hlam : 0 < lam) (hld : lam ≤ d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0 ≤ h 0) (hlb : lam ≤ b 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hzero : ∀ᵐ r,r∈Icc (0:ℝ) 1 → H r=0 →
      radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r=0)
    (as : ℕ → List PositiveMass) (mesh : ℕ → ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (s : ℝ) (has : a ≤ s) (hsz : s ≤ z)
    (hlocal : ∀l r,a ≤ l → l ≤ r → r ≤ z → (r < s ∨ s ≤ l) →
      ∃Kb Kh : ℝ≥0,
        LipschitzOnWith Kb (fun t=>b (α.val.val t)) (Icc l r) ∧
        LipschitzOnWith Kh (fun t=>h (α.val.val t)) (Icc l r))
    (w : ℝ → ℝ) (hw : Measurable w) (K : ℝ) (hK : 0 ≤ K)
    (hwb : ∀r,‖w r‖ ≤ K) (hw0 : ∀r,0 ≤ w r)
    {ε : ℝ} (hε : 0 < ε) :
    let A := {r | r∈Ioo a z ∧ H r=0}
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in A,deriv α.val.val r*w r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      ((9*Real.log N)/F)*(∫r in A,deriv α.val.val r*w r)+ε := by
  dsimp only
  let A := {r | r∈Ioo a z ∧ H r=0}
  let weight := fun r=>deriv α.val.val r*w r
  let f := A.indicator weight
  let mu := fun j=>comparisonPhysicalRadiusMeasure hc hk hkc hm hM
    n dphys e d lam b h α (as j) (ho j)
  let F := fun t=>(n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam t)
  let C := (9*Real.log N)/F z
  have hC : 0 ≤ C := by
    exact div_nonneg (by linarith) (mul_nonneg (by positivity)
      (mul_nonneg (div_nonneg (by norm_num) (by linarith))
        (laplaceComparisonStrength_pos d hlam z).le))
  have hdom j : mu j ≤ volume :=
    (comparisonPhysicalRadiusMeasure_le_compact_volume hc hk hkc hm hM
      n dphys e d lam b h α (as j) (ho j)).trans Measure.restrict_le_self
  have hHC : ContinuousOn H (Icc a z) := hH.continuousOn.mono (by
    simpa only [uIcc_of_le zero_le_one] using Icc_subset_Icc ha.le hz)
  have hclosed : MeasurableSet {r | r∈Icc a z ∧ H r=0} :=
    (hHC.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton).measurableSet
  have hA : MeasurableSet A := by
    have heq : A={r | r∈Icc a z ∧ H r=0}∩Ioo a z := by
      ext r
      exact ⟨fun hr=>⟨⟨Ioo_subset_Icc_self hr.1,hr.2⟩,hr.1⟩,
        fun hr=>⟨hr.2,hr.1.2⟩⟩
    rw [heq]
    exact hclosed.inter measurableSet_Ioo
  have hiw : IntegrableOn weight (Ioo a z) :=
    comparison_radiusWeight_integrableOn hm hM α ha hz
      (Ioo a z) measurableSet_Ioo (Subset.refl _) w hw hwb
  have hi : IntervalIntegrable f volume a z :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le haz).mpr (hiw.indicator hA)
  have hf : ∀r∈Icc a z,0 ≤ f r ∧ f r ≤ M 1*K := by
    intro r _
    by_cases hr : r∈A
    · have hr01 : r∈Ioo (0:ℝ) 1 := ⟨ha.trans hr.1.1,hr.1.2.trans_le hz⟩
      have hdα : ‖deriv α.val.val r‖ ≤ M 1 := norm_deriv_le_of_lipschitzOn
        (Icc_mem_nhds hr01.1 hr01.2) (inverseIntegralConstraints_lipschitz hm hM α.property)
      have hp : 0 ≤ weight r := mul_nonneg α.val.property.2.deriv_nonneg (hw0 r)
      have hbnd : ‖weight r‖ ≤ M 1*K := by
        dsimp only [weight]
        rw [norm_mul]
        exact mul_le_mul hdα (hwb r) (norm_nonneg _) hM
      simp only [f,indicator_of_mem hr]
      exact ⟨hp,(le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using hbnd)⟩
    · simp only [f,indicator_of_notMem hr]
      exact ⟨le_rfl,mul_nonneg hM hK⟩
  have heq (nu : Measure ℝ) (hnu : nu ≤ volume) {l r : ℝ}
      (hal : a ≤ l) (hlr : l ≤ r) (hrz : r ≤ z) :
      (∫t in l..r,f t∂nu)=∫t in {t | t∈Ioo l r ∧ H t=0},weight t∂nu :=
    interval_integral_contact_indicator nu hnu H weight hal hlr hrz hA
  have hbranch {l r : ℝ} (hal : a ≤ l) (hlr : l ≤ r) (hrz : r ≤ z)
      (hside : r < s ∨ s ≤ l) (eps : ℝ) (heps : 0 < eps) :
      ∀ᶠj in atTop,(∫t in l..r,f t∂mu j) ≤ C*(∫t in l..r,f t)+eps := by
    obtain ⟨Kb,Kh,hbLip,hhLip⟩:=hlocal l r hal hlr hrz hside
    have ht:=comparisonPhysicalWeightedContactTrace_eventually hc hk hkc hm hM
      hN hlog hd hnd hlam hld n dphys e b h hb hh hh0 hlb α H hH hzero
      as mesh ho hend hmesh hmesh0 hlim (ha.trans_le hal) hlr (hrz.trans hz)
      Kb Kh hbLip hhLip w hw K (fun t _ _=>hwb t) (fun t _ _=>hw0 t) heps
    have hepos t : 0 < F t := mul_pos (by positivity)
      (mul_pos (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam t))
    have hemono : F z ≤ F r := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (by linarith))
      exact (laplaceComparisonStrength_monotonicities hd.ne' hlam (by norm_num : (0:ℝ) ≤ 0)).1
        ⟨(ha.le.trans hal).trans hlr,hrz.trans hz⟩ ⟨ha.le.trans haz,hz⟩ hrz
    have hcmono : (9*Real.log N)/F r ≤ C :=
      div_le_div_of_nonneg_left (by linarith) (hepos z) hemono
    have hnonneg : 0 ≤ ∫t in l..r,f t := intervalIntegral.integral_nonneg hlr
      (fun t ht=>(hf t ⟨hal.trans ht.1,ht.2.trans hrz⟩).1)
    filter_upwards [ht] with j hj
    rw [heq (mu j) (hdom j) hal hlr hrz,heq volume le_rfl hal hlr hrz]
    have hm := mul_le_mul_of_nonneg_right hcmono hnonneg
    rw [heq volume le_rfl hal hlr hrz] at hm
    change (∫t in {t | t∈Ioo l r ∧ H t=0},weight t∂mu j) ≤
      ((9*Real.log N)/F r)*(∫t in {t | t∈Ioo l r ∧ H t=0},weight t)+eps at hj
    linarith
  have ht:=interval_trace_single_cut_eventually mu hdom f has hsz hi hf hC (mul_nonneg hM hK)
    (fun p hp hps eps heps=>hbranch le_rfl hp.1 (hp.2.trans hsz) (Or.inl hps) eps heps)
    (fun eps heps=>hbranch has hsz le_rfl (Or.inr le_rfl) eps heps) hε
  filter_upwards [ht] with j hj
  simpa only [heq (mu j) (hdom j) le_rfl haz le_rfl,
    heq volume le_rfl le_rfl haz le_rfl,weight,mu,C,F] using hj
end
end OAI.SKFluctuations.LaplaceWindowFormalization
