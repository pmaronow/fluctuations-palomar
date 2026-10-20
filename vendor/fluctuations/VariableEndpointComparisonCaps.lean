module

public import ActualComparisonCaps
public import VariableEndpointComparisonPotential

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 1000000

section
variable {c : ℝ} {k M : ℝ → ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem actual_variableEndpoint_comparison_cap_interior_geometry
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n : ℕ) (hn : 0<n) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS n
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB n
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    {a z s t : ℝ} (ha : 0≤a) (hz : z≤1)
    (hs : s∈Ioo a z) (ht : t∈Ioo a z) (hst : s≤t)
    (haH : H a=0) (hzH : H z=0) (hsH : H s<0) (htH : H t<0) :
    let R := comparisonSweepQuantile hc hk hkc hm hM α
    let bf := fun u=>(b u-laplaceComparisonStrength d lam (R u)).toNNReal
    let hf := fun u=>(h u+laplaceComparisonStrength d lam (R u)*R u).toNNReal
    let S := fun r=>orderedPathS n bf hf (α.val.val r)
    let B := fun r=>orderedPathB n bf hf (α.val.val r)
    S t-S s≤9*Real.log N*(z-a) ∧ S t≤z ∧
      (S t-t)^2≤16*(z-a)^2+2*(B t-(S t)^2) := by
  dsimp only
  let g := laplaceComparisonStrength d lam
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-g (R u)).toNNReal
  let hf := fun u=>(h u+g (R u)*R u).toNNReal
  let S := orderedPathS n bf hf
  let B := orderedPathB n bf hf
  let Sr := fun r=>S (α.val.val r)
  let Br := fun r=>B (α.val.val r)
  let p := comparisonLogSlope g
  let κ := (1/3)/Real.log N
  have hlogp : 0<Real.log N := by linarith
  have hκ : 0<κ := div_pos (by norm_num) hlogp
  have haz : a<z := hs.1.trans hs.2
  have hsub : Icc a z⊆Icc (0:ℝ) 1 := Icc_subset_Icc ha hz
  have hsubo : Ioo a z⊆Ioc (0:ℝ) 1 := fun r hr=>⟨ha.trans_lt hr.1,hr.2.le.trans hz⟩
  have hJg (r : ℝ) (hr : r∈Icc a z) : 0<J r*g r :=
    mul_pos (hJ r (hsub hr)) (laplaceComparisonStrength_pos d hlam r)
  have hDp : ∀ᵐ r,r∈Icc a z→HasDerivAt H
      ((J r*g r)*comparisonBracket (p r) r (Sr r) (Br r)) r := by
    filter_upwards [hD,volume.ae_ne (0:ℝ)] with r hdr hr0 hr
    have hrpos : 0<r := lt_of_le_of_ne (hsub hr).1 hr0.symm
    have hh := hdr (hsub hr)
    rw [comparison_gradient_slope hrpos.ne' (laplaceComparisonStrength_pos d hlam r).ne'] at hh
    convert hh using 1
    dsimp only [Sr,Br,S,B,bf,hf,g,R,p,comparisonBracket]
    ring
  have hpm : MonotoneOn p (Ioo a z) := by
    intro r hr t ht hrt
    dsimp only [p,g]
    rw [laplaceComparisonStrength_logSlope hd.ne' hlam.ne',laplaceComparisonStrength_logSlope hd.ne' hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt hlam.le) (pow_nonneg hd.le _))
  have hpb (r : ℝ) (hr : r∈Ioo a z) : p r∈Icc (0:ℝ) (1-κ) :=
    ⟨(laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).1,by
      have hh := laplaceComparisonStrength_uniform_slope hN hlog hd hnd hlam hld (hsub (Ioo_subset_Icc_self hr))
      dsimp only [κ,p,g]
      linarith⟩
  have hpb' (r : ℝ) (hr : r∈Ioo a z) : p r∈Icc (0:ℝ) 1 :=
    ⟨(hpb r hr).1,by linarith [(hpb r hr).2]⟩
  have hmom := comparisonVariableEndpoint_radius_moments hc hk hkc hm hM n hn b h hd.ne' hlam.le hlb hb hh hh0 α
  have hS := hmom.1.mono (Ioo_subset_Icc_self.trans hsub)
  have hB := hmom.2.1.mono (Ioo_subset_Icc_self.trans hsub)
  have hSb (r : ℝ) (hr : r∈Ioo a z) : 0≤Sr r :=
    (hmom.2.2 r (hsub (Ioo_subset_Icc_self hr))).1.1
  have hBb (r : ℝ) (hr : r∈Ioo a z) : (Sr r)^2≤Br r :=
    (hmom.2.2 r (hsub (Ioo_subset_Icc_self hr))).2.1
  have hac : AbsolutelyContinuousOnInterval H a z := hH.mono (by simpa only [uIcc_of_le zero_le_one,uIcc_of_le haz.le] using hsub)
  have hi := cap_interior_increment ha hs ht hst hκ hac hJg hDp haH hzH hsH htH
    hpm hpb hS hB hSb hBb
  have hconstant : 3/κ=9*Real.log N := by dsimp [κ];field_simp;ring
  have hinc : Sr t-Sr s≤9*Real.log N*(z-a) := by
    have hh := (le_div_iff₀ hκ).mpr (by nlinarith [hi] : (Sr t-Sr s)*κ≤3*(z-a))
    rw [←div_mul_eq_mul_div,hconstant] at hh
    exact hh
  exact ⟨hinc,cap_S_le_right (S:=Sr) (B:=Br) (r:=t) ha ht hac hJg hDp hzH htH hpb' hS hSb hBb,
    cap_interior_mismatch (S:=Sr) (B:=Br) (r:=t) ha ht hac hJg hDp haH hzH htH hpm hpb' hS hB hSb hBb⟩
end
end OAI.SKFluctuations.LaplaceWindowFormalization
