module

public import ComparisonContactIntegration
public import VariableEndpointComparisonContact

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 1000000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem actual_variableEndpoint_contact_weighted_integral_le
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
    {a z : ℝ} (ha : 0 < a) (haz : a ≤ z) (hz : z ≤ 1)
    (Kb Kh : ℝ≥0)
    (hparent : LipschitzOnWith Kb (fun r=>b (α.val.val r)) (Icc a z))
    (hfield : LipschitzOnWith Kh (fun r=>h (α.val.val r)) (Icc a z)) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS (n+1) bf hf (α.val.val r)
    let A := {r | r∈Icc a z ∧ H r=0}
    IntegrableOn (fun r=>deriv α.val.val r*deriv S r) A ∧
      (∫r in A,deriv α.val.val r*deriv S r) ≤
        (9*Real.log N)*(∫r in A,deriv α.val.val r) := by
  dsimp only
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let g := laplaceComparisonStrength d lam
  let bf := fun u=>(b u-g (R u)).toNNReal
  let hf := fun u=>(h u+g (R u)*R u).toNNReal
  let S := orderedPathS (n+1) bf hf
  let B := orderedPathB (n+1) bf hf
  let Sr := fun r=>S (α.val.val r)
  let Br := fun r=>B (α.val.val r)
  let p := comparisonLogSlope g
  let κ := (1/3)/Real.log N
  let A := {r | r∈Icc a z ∧ H r=0}
  have hsub : Icc a z⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha.le hz
  have hκ : 0 < κ := div_pos (by norm_num) (by linarith)
  have hpm : MonotoneOn p (Ioc (0:ℝ) 1) := by
    intro r hr t ht hrt
    dsimp only [p,g]
    rw [laplaceComparisonStrength_logSlope hd.ne' hlam.ne',laplaceComparisonStrength_logSlope hd.ne' hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt hlam.le) (pow_nonneg hd.le _))
  have hpb (r : ℝ) (hr : r∈Ioc (0:ℝ) 1) : p r∈Icc (0:ℝ) (1-κ) :=
    ⟨(laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).1,by
      have hs := laplaceComparisonStrength_uniform_slope hN hlog hd hnd hlam hld ⟨hr.1.le,hr.2⟩
      dsimp only [κ,p,g]
      linarith⟩
  have hmom := comparisonVariableEndpoint_radius_moments hc hk hkc hm hM
    (n+1) (by omega) b h hd.ne' hlam.le hlb hb hh hh0 α
  have hAC := actual_variableEndpoint_radius_overlap_absolutelyContinuous hc hk hkc hm hM
    n dphys e b h hb hh hh0 hd.ne' hlam.le hlb α ha haz hz Kb hparent Kh hfield
  have hHA : ContinuousOn H (Icc a z) := by
    apply hH.continuousOn.mono
    simpa only [uIcc_of_le zero_le_one] using hsub
  have hAm : MeasurableSet A := by
    change MeasurableSet (Icc a z ∩ H ⁻¹' {0})
    exact (hHA.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton).measurableSet
  have hbr : ∀ᵐ r,r∈A→comparisonBracket (p r) r (Sr r) (Br r)=0 := by
    filter_upwards [hzero] with r hr hAr
    have hrpos : 0 < r := ha.trans_le hAr.1.1
    have hz0 := hr (hsub hAr.1) hAr.2
    rw [comparison_gradient_slope hrpos.ne' (laplaceComparisonStrength_pos d hlam r).ne'] at hz0
    have hh : g r*comparisonBracket (p r) r (Sr r) (Br r)=0 := by
      simpa only [g,p,Sr,Br,S,B,bf,hf,R,comparisonBracket] using hz0
    exact (mul_eq_zero.mp hh).resolve_left (laplaceComparisonStrength_pos d hlam r).ne'
  have hout := comparison_contact_weighted_integral_le hκ hpm hpb hmom.1
    (hmom.2.1.mono Ioc_subset_Icc_self)
    (fun r hr=>((hmom.2.2 r ⟨hr.1.le,hr.2⟩).1).1)
    (fun r hr=>((hmom.2.2 r ⟨hr.1.le,hr.2⟩).2).1)
    hm hM α ha haz hz hAC A hAm (fun _ hr=>hr.1) hbr
  have hconst : 3/κ=9*Real.log N := by dsimp [κ];field_simp;ring
  simpa only [hconst,Sr,S,bf,hf,g,R,A] using hout
end
end OAI.SKFluctuations.LaplaceWindowFormalization
