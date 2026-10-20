module

public import ComparisonCapSideTrace
public import ComparisonCapDensity

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 1800000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0 < c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c ≤ k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0 ≤ M 1)

theorem comparisonPhysicalCapUnitTrace_eventually
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
    (haH : H a=0) (hzH : H z=0) (hneg : ∀r∈Ioo a z,H r<0)
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
  have ht := comparisonPhysicalWeightedCapTrace_eventually hc hk hkc hm hM
    hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD hbang
    ha haz hz haH hzH hneg as mesh ho hend hmesh hmesh0 hlim hMz
    (Ioo a z) measurableSet_Ioo (Subset.refl _) (fun _=>1) measurable_const
    (by norm_num : (0:ℝ)≤1) (fun _ _=>by norm_num) hε
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
  simp only [mul_one] at hj
  exact hj.trans (add_le_add hnormal le_rfl)

theorem comparisonCap_normalized_factor_le
    {N δ U L E d u v K : ℝ} (hN : 0<N) (hU : 0<U)
    (hL : 0<L) (hE : 0<E) (hd : 0≤d) (hu : 0≤u) (hv : 0≤v)
    (hK : 1≤K) (hband : v+U≤K*(u+U)) :
    comparisonCap N δ U L E d v/comparisonCap N δ U L E d u ≤ K^2 := by
  have hpos := (comparisonCap_first_term (δ:=δ) hN hU hL hE hd hu).1
  exact (div_le_iff₀ hpos).mpr (comparisonCap_comparable_density hN hU hL hE hd hu hv hK hband)

theorem comparisonCap_length_density_product_le
    {N δ U L E d V : ℝ} (hN : 0<N) (hU : 0<U)
    (hL : 0<L) (hE : 0<E) (hd : 0≤d) (hV : 0≤V)
    (hcal : d^3*L*U ≤ E) :
    comparisonCap N δ U L E d V*(L/N^δ) ≤ (V+U)+(V+U)^2/U := by
  have hpow : N^δ≠0 := (Real.rpow_pos_of_pos hN δ).ne'
  have he : comparisonCap N δ U L E d V*(L/N^δ) =
      (V+U)+(d^3*L/E)*(V+U)^2 := by
    unfold comparisonCap
    field_simp [hpow,hL.ne',hE.ne']
    <;> ring
  have hcoef : d^3*L/E ≤ 1/U := by
    apply (div_le_iff₀ hE).mpr
    rw [one_div_mul_eq_div]
    exact (le_div_iff₀ hU).mpr hcal
  rw [he]
  have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (V+U))
  simpa only [one_div,one_mul,div_eq_mul_inv,mul_comm ((V+U)^2)] using
    (add_le_add (le_refl (V+U)) hh)

theorem comparisonCap_broad_length_multiplier_le
    {N δ U L E d V v K : ℝ} (hN : 0<N) (hU : 0<U)
    (hL : 0<L) (hE : 0<E) (hd : 0≤d) (hV : 0≤V)
    (hK : 1≤K) (hUv : U≤v) (hVv : V≤K*v) (hcal : d^3*L*U ≤ E) :
    (comparisonCap N δ U L E d V/v)*(L/N^δ) ≤ (K+1)^2*(1+v/U) := by
  have hv : 0<v := hU.trans_le hUv
  have ht : 0≤V+U := by positivity
  have hk : 0≤K+1 := by linarith
  have htop : V+U≤(K+1)*v := by nlinarith
  have hKK : K+1≤(K+1)^2 := by nlinarith
  have hlin : V+U≤(K+1)^2*v := htop.trans (mul_le_mul_of_nonneg_right hKK hv.le)
  have hquad : (V+U)^2 ≤ (K+1)^2*v^2 := by
    have hh := (sq_le_sq₀ ht (mul_nonneg hk hv.le)).mpr htop
    nlinarith
  have hprofile := comparisonCap_length_density_product_le (δ:=δ) hN hU hL hE hd hV hcal
  have hh := hprofile.trans (add_le_add hlin (div_le_div_of_nonneg_right hquad hU.le))
  have hn : comparisonCap N δ U L E d V*(L/N^δ) ≤
      ((K+1)^2*(1+v/U))*v := by
    convert hh using 1 <;> field_simp <;> ring
  have hdv := (div_le_iff₀ hv).mpr hn
  convert hdv using 1 <;> ring

end
end OAI.SKFluctuations.LaplaceWindowFormalization
