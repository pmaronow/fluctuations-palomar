module

public import ComparisonCapSideTraceNormalized
public import ComparisonCapSideTraceTerminal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 2200000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonPhysicalLeftContactCapUnitTrace_eventually
    {N d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1)) (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0) (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ → ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    (hbang : ∀ᵐ r, r∈Icc (0:ℝ) 1 → H r<0 → deriv α.val.val r=M (α.val.val r))
    {a z : ℝ} (ha : 0 ≤ a) (haz : a < z) (hz : z ≤ 1)
    (haH : H a=0) (hzH : H z=0 ∨ z=1) (hneg : ∀r∈Ioo a z,H r<0)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    (hMa : 0 < M (α.val.val a)) {ε : ℝ} (hε : 0 < ε) :
    let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in Ioo a z,deriv α.val.val r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      (M (α.val.val z)/M (α.val.val a))*((9*Real.log N)/F)*
        (α.val.val z-α.val.val a)+ε := by
  dsimp only
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  have hF : 0 < F := mul_pos (by positivity) (mul_pos
    (div_pos (by norm_num) (by linarith)) (laplaceComparisonStrength_pos d hlam z))
  have hMz : 0 ≤ M (α.val.val z) := hMa.le.trans
    (hm (α.val.property.1 a) (α.val.property.1 z) (α.val.property.2 haz.le))
  have ht : ∀ᶠ j in atTop,
      (∫r in Ioo a z,deriv α.val.val r
        ∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM n dphys e d lam b h α (as j) (ho j))≤
      M (α.val.val z)*((9*Real.log N)*(z-a)/F)+ε := by
    rcases hzH with hcontact | hterminal
    · have hh := comparisonPhysicalWeightedCapTrace_eventually hc hk hkc hm hM
        hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD hbang
        ha haz hz haH hcontact hneg as mesh ho hend hmesh hmesh0 hlim hMz
        (Ioo a z) measurableSet_Ioo (Subset.refl _) (fun _=>1) measurable_const
        (by norm_num : (0:ℝ)≤1) (fun _ _=>by norm_num) hε
      simpa only [mul_one] using hh
    · subst z
      have hh := comparisonPhysicalSelectedTerminalCapTrace_eventually hc hk hkc hm hM
        hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD hbang
        ha haz haH hneg as mesh ho hend hmesh hmesh0 hlim
        (α.val.val 1) (α.val.property.1 1) hMz (Ioo a 1) measurableSet_Ioo (Subset.refl _)
        (fun r hr=>α.val.property.2 hr.2.le) (fun _=>1) measurable_const
        (by norm_num : (0:ℝ)≤1) (fun _ _=>by norm_num) hε
      simpa only [mul_one] using hh
  have hmass := comparison_cap_mass_lower hm hM α H hbang ha haz.le hz hneg
  have hlength : z-a ≤ (α.val.val z-α.val.val a)/M (α.val.val a) := by
    apply (le_div_iff₀ hMa).mpr
    simpa only [mul_comm] using hmass
  have hcoef : 0 ≤ M (α.val.val z)*((9*Real.log N)/F) := mul_nonneg hMz
    (div_nonneg (by positivity) hF.le)
  have hn := mul_le_mul_of_nonneg_left hlength hcoef
  have hnormal : M (α.val.val z)*((9*Real.log N)*(z-a)/F) ≤
      (M (α.val.val z)/M (α.val.val a))*((9*Real.log N)/F)*(α.val.val z-α.val.val a) := by
    convert hn using 1 <;> field_simp
  filter_upwards [ht] with j hj
  exact hj.trans (add_le_add hnormal le_rfl)

end
end OAI.SKFluctuations.LaplaceWindowFormalization
