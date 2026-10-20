module

public import PhysicalFiniteWeightedTrace
public import ActualVariableEndpointContactIntegration

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 1000000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonPhysicalWeightedContactTrace_eventually
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
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z))
    (w : ℝ→ℝ) (hw : Measurable w) (K : ℝ)
    (hwb : ∀r∈Ioo a z,H r=0→‖w r‖ ≤ K)
    (hw0 : ∀r∈Ioo a z,H r=0→0 ≤ w r)
    {ε : ℝ} (hε : 0 < ε) :
    let A := {r | r∈Ioo a z ∧ H r=0}
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in A,deriv α.val.val r*w r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      ((9*Real.log N)/F)*(∫r in A,deriv α.val.val r*w r)+ε := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
  let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
  let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let A := {r | r∈Ioo a z ∧ H r=0}
  let Aclosed := {r | r∈Icc a z ∧ H r=0}
  have hsub : Icc a z⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha.le hz
  have hHC : ContinuousOn H (Icc a z) := hH.continuousOn.mono (by
    simpa only [uIcc_of_le zero_le_one] using hsub)
  have hclosedMeas : MeasurableSet Aclosed := by
    change MeasurableSet (Icc a z∩H ⁻¹' {0})
    exact (hHC.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton).measurableSet
  have hAm : MeasurableSet A := by
    have heq : A=Aclosed∩Ioo a z := by
      ext r
      simp only [A,Aclosed,mem_setOf_eq,mem_inter_iff,mem_Ioo,mem_Icc]
      constructor
      · intro hr
        exact ⟨⟨⟨hr.1.1.le,hr.1.2.le⟩,hr.2⟩,hr.1⟩
      · intro hr
        exact ⟨hr.2,hr.1.2⟩
    rw [heq]
    exact hclosedMeas.inter measurableSet_Ioo
  let weight := fun r=>deriv α.val.val r*w r
  have hweightMeas : AEStronglyMeasurable weight volume :=
    (stronglyMeasurable_deriv α.val.val).aestronglyMeasurable.mul hw.stronglyMeasurable.aestronglyMeasurable
  have hαLip := inverseIntegralConstraints_lipschitz hm hM α.property
  have hweightBound r (hr : r∈A) : ‖weight r‖ ≤ (M 1)*K := by
    have hr01 : r∈Ioo (0:ℝ) 1 := ⟨ha.trans hr.1.1,hr.1.2.trans_le hz⟩
    have hdα : ‖deriv α.val.val r‖ ≤ M 1 := norm_deriv_le_of_lipschitzOn
      (Icc_mem_nhds hr01.1 hr01.2) hαLip
    dsimp only [weight]
    rw [norm_mul]
    exact mul_le_mul hdα (hwb r hr.1 hr.2) (norm_nonneg _) hM
  have hweightPos r (hr : r∈A) : 0 ≤ weight r :=
    mul_nonneg α.val.property.2.deriv_nonneg (hw0 r hr.1 hr.2)
  let g := laplaceComparisonStrength d lam
  let p := comparisonLogSlope g
  let κ := (1/3)/Real.log N
  let B := fun r=>orderedPathB (n+1) bf hf (α.val.val r)
  have hκ : 0 < κ := div_pos (by norm_num) (by linarith)
  have hpm : MonotoneOn p (Ioc (0:ℝ) 1) := by
    intro r hr t ht hrt
    dsimp only [p,g]
    rw [laplaceComparisonStrength_logSlope hd.ne' hlam.ne',laplaceComparisonStrength_logSlope hd.ne' hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt hlam.le) (pow_nonneg hd.le _))
  have hpb (r : ℝ) (hr : r∈Ioc (0:ℝ) 1) : p r∈Icc (0:ℝ) (1-κ) :=
    ⟨(laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).1,by
      have hh := laplaceComparisonStrength_uniform_slope hN hlog hd hnd hlam hld ⟨hr.1.le,hr.2⟩
      dsimp only [κ,p,g]
      linarith⟩
  have hmom := comparisonVariableEndpoint_radius_moments hc hk hkc hm hM
    (n+1) (by omega) b h hd.ne' hlam.le hlb hb hh hh0 α
  have hderiv := comparison_contact_ae_deriv_le hκ hpm hpb hmom.1
    (hmom.2.1.mono Ioc_subset_Icc_self)
    (fun r hr=>((hmom.2.2 r ⟨hr.1.le,hr.2⟩).1).1)
    (fun r hr=>((hmom.2.2 r ⟨hr.1.le,hr.2⟩).2).1)
  have hconst : 3/κ=9*Real.log N := by dsimp [κ];field_simp;ring
  have hcontactDeriv : ∀ᵐ r,r∈A→deriv S r ≤ 9*Real.log N := by
    filter_upwards [hderiv,hzero] with r hdr hzr hr
    have hr01 : r∈Ioc (0:ℝ) 1 := ⟨ha.trans hr.1.1,hr.1.2.le.trans hz⟩
    have hz0 := hzr ⟨hr01.1.le,hr01.2⟩ hr.2
    rw [comparison_gradient_slope hr01.1.ne' (laplaceComparisonStrength_pos d hlam r).ne'] at hz0
    have heq : g r*comparisonBracket (p r) r (S r) (B r)=0 := by
      simpa only [g,p,S,B,bf,hf,R,comparisonBracket] using hz0
    have hbr := (mul_eq_zero.mp heq).resolve_left (laplaceComparisonStrength_pos d hlam r).ne'
    simpa only [hconst] using hdr hr01 hbr
  have hAC := actual_variableEndpoint_radius_overlap_absolutelyContinuous hc hk hkc hm hM
    n dphys e b h hb hh hh0 hd.ne' hlam.le hlb α ha haz hz Kb hparent Kh hfield
  have hiS : IntegrableOn (deriv S) A :=
    ((intervalIntegrable_iff_integrableOn_Icc_of_le haz).mp hAC.intervalIntegrable_deriv).mono_set
      (fun _ hr=>Ioo_subset_Icc_self hr.1)
  have hweightBoundAE : ∀ᵐ r∂volume.restrict A,‖weight r‖ ≤ (M 1)*K := by
    filter_upwards [ae_restrict_mem hAm] with r hr
    exact hweightBound r hr
  have hiProd : IntegrableOn (fun r=>weight r*deriv S r) A :=
    hiS.bdd_mul hweightMeas.restrict hweightBoundAE
  have hAf : volume A≠⊤ := ne_top_of_le_ne_top (by simp : volume (Icc a z)≠⊤)
    (measure_mono (fun _ hr=>Ioo_subset_Icc_self hr.1))
  have hiOne : IntegrableOn (fun _ : ℝ=>(1:ℝ)) A := integrableOn_const hAf
  have hiWeight : IntegrableOn weight A := by
    simpa only [IntegrableOn,mul_one] using hiOne.bdd_mul hweightMeas.restrict hweightBoundAE
  have hcontactWeight : (∫r in A,weight r*deriv S r) ≤
      (9*Real.log N)*(∫r in A,weight r) := by
    have hh : ∀ᵐ r,r∈A→weight r*deriv S r ≤ (9*Real.log N)*weight r := by
      filter_upwards [hcontactDeriv] with r hdr hr
      exact (mul_le_mul_of_nonneg_left (hdr hr) (hweightPos r hr)).trans_eq (mul_comm _ _)
    have ht := setIntegral_mono_on_ae hiProd (hiWeight.const_mul _) hAm hh
    simpa only [integral_const_mul] using ht
  have ht := comparisonPhysicalRadiusTrace_boundedWeight_eventually hc hk hkc hm hM hN hlog
    hd hnd hlam hld n dphys e b h hb hh hh0 hlb α as mesh ho hend hmesh hmesh0 hlim
    ha haz hz Kb Kh hparent hfield hAm (fun _ hr=>hr.1) weight hweightMeas ((M 1)*K)
    hweightBound hweightPos hε
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hbnd : (∫r in A,weight r*deriv S r)/F ≤
      ((9*Real.log N)/F)*(∫r in A,weight r) := by
    have ht := div_le_div_of_nonneg_right hcontactWeight hF.le
    convert ht using 1 <;> ring
  filter_upwards [ht] with j hj
  exact hj.trans (by dsimp only [S,bf,hf,R,F,weight] at hbnd;linarith)
end
end OAI.SKFluctuations.LaplaceWindowFormalization
