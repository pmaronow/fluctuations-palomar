module

public import ComparisonCapSideTraceNormalized
public import ComparisonCapSideTraceWall
public import ComparisonCapSideTraceTerminal

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set MeasureTheory ProbabilityTheory Filter Hierarchy
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 1800000
section
variable {c : ℝ} {k M : ℝ→ℝ}
variable (hc : 0<c) (hk : ContinuousOn k (Icc (0:ℝ) 1))
variable (hkc : ∀r∈Icc (0:ℝ) 1,c≤k r)
variable (hm : MonotoneOn M (Icc (0:ℝ) 1)) (hM : 0≤M 1)

theorem comparisonPhysicalBroadCapUnitTrace_eventually
    {N δcap U L E d lam : ℝ} (hN : 1≤N) (hlog : 1≤Real.log N)
    (hU : 0<U) (hL : 0<L) (hE : 0<E) (hd : 0<d)
    (hnd : 1/N≤d) (hlam : 0<lam) (hld : lam≤d^2)
    (hMdef : M=comparisonCap N δcap U L E d)
    (n dphys : ℕ) (e : Fin (dphys+1) ≃ FeatureIndex (n+1))
    (b h : ℝ→ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1))
    (hlb : lam≤b 0) (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (α : inverseIntegralConstraints 0 0 k M)
    (H J : ℝ→ℝ) (hH : AbsolutelyContinuousOnInterval H 0 1)
    (hJ : ∀r∈Icc (0:ℝ) 1,0<J r)
    (hD : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      (J r*radiusComparisonGradient (laplaceComparisonStrength d lam) α.val.val
        (orderedPathS (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal))
        (orderedPathB (n+1)
          (fun u=>(b u-laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)).toNNReal)
          (fun u=>(h u+laplaceComparisonStrength d lam (comparisonSweepQuantile hc hk hkc hm hM α u)*comparisonSweepQuantile hc hk hkc hm hM α u).toNNReal)) r) r)
    (hbang : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r<0→deriv α.val.val r=M (α.val.val r))
    {a z v V K : ℝ} (ha : 0≤a) (haz : a<z) (hz : z≤1)
    (hboundary : (H a=0 ∧ H z=0) ∨ (a=0 ∧ H z=0) ∨ (H a=0 ∧ z=1))
    (hneg : ∀r∈Ioo a z,H r<0)
    (hK : 1≤K) (hUv : U≤v) (hV : V∈Icc (0:ℝ) 1) (hVv : V≤K*v)
    (hcal : d^3*L*U≤E)
    (A : Set ℝ) (hA : MeasurableSet A) (hAcap : A⊆Ioo a z)
    (hAV : ∀r∈A,α.val.val r≤V)
    (hslice : v≤∫r in A,deriv α.val.val r)
    (as : ℕ→List PositiveMass) (mesh : ℕ→ℝ)
    (ho : ∀j,MassOrdered 0 (as j)) (hend : ∀j,partitionEnd 0 (as j)=1)
    (hmesh : ∀j,PartitionMesh (mesh j) 0 (as j)) (hmesh0 : ∀j,0 ≤ mesh j)
    (hlim : Tendsto mesh atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) :
    let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam z)
    ∀ᶠ j in atTop,
      (∫r in A,deriv α.val.val r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j)) ≤
      C*(K+1)^2*(1+v/U)*Real.log ((1+U)/U)*(∫r in A,deriv α.val.val r)+ε := by
  dsimp only
  let F := (n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam z)
  let C := 27*(Real.log N)^2/((n+1:ℝ)*laplaceComparisonStrength d lam z)
  let T := Real.log ((1+U)/U)
  let Q := (K+1)^2*(1+v/U)
  have hNp : 0<N := by linarith
  have hv : 0<v := hU.trans_le hUv
  have hlogpos : 0<Real.log N := by linarith
  have hgpos := laplaceComparisonStrength_pos d hlam z
  have hF : 0<F := mul_pos (by positivity)
    (mul_pos (div_pos (by norm_num) hlogpos) hgpos)
  have hC : 0≤C := by dsimp [C]; positivity
  have hT : 0≤T := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hU).mpr
    linarith
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hMV : 0≤M V := by
    rw [congrFun hMdef V]
    exact (comparisonCap_first_term (δ:=δcap) hNp hU hL hE hd.le hV.1).1.le
  have hcap : ∀ᵐ r,r∈Icc (0:ℝ) 1→H r<0→
      deriv α.val.val r=comparisonCap N δcap U L E d (α.val.val r) := by
    filter_upwards [hbang] with r hr hr01 hrH
    simpa only [congrFun hMdef (α.val.val r)] using hr hr01 hrH
  have htravel := potential_comparison_cap_interval_travel (δ:=δcap)
    hNp hU hL hE hd
    (inverseIntegralConstraints_lipschitz hm hM α.property)
    (inverseConstraint_strictMonoOn hc hk hkc α.property)
    (fun r _=>α.val.property.1 r) hcap ha hz haz.le hneg
  have hlength : z-a≤(L/N^δcap)*T := htravel.2.1
  have hprofile : M V*(L/N^δcap)≤Q*v := by
    have ht := comparisonCap_broad_length_multiplier_le (δ:=δcap)
      hNp hU hL hE hd.le hV.1 hK hUv hVv hcal
    have ht' := (div_le_iff₀ hv).mp
      (show (comparisonCap N δcap U L E d V*(L/N^δcap))/v≤Q by
        convert ht using 1 <;> ring)
    simpa only [congrFun hMdef V] using ht'
  have hnormal : M V*C*(z-a)≤C*Q*T*(∫r in A,deriv α.val.val r) := by
    have h1 := mul_le_mul_of_nonneg_left hlength (mul_nonneg hMV hC)
    have h2 := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hprofile hT) hC
    have h3 := mul_le_mul_of_nonneg_left hslice (mul_nonneg (mul_nonneg hC hQ) hT)
    nlinarith
  have hcommon : (9*Real.log N)/F=C := by
    dsimp [F,C]
    field_simp [hlogpos.ne',hgpos.ne']
    <;> ring
  have ht : ∀ᶠ j in atTop,
      (∫r in A,deriv α.val.val r∂comparisonPhysicalRadiusMeasure hc hk hkc hm hM
        n dphys e d lam b h α (as j) (ho j))≤M V*C*(z-a)+ε := by
    rcases hboundary with hordinary | hinitial | hterminal
    · have hh := comparisonPhysicalSelectedCapTrace_eventually hc hk hkc hm hM
        hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD hbang
        ha haz hz hordinary.1 hordinary.2 hneg as mesh ho hend hmesh hmesh0 hlim
        V hV hMV A hA hAcap hAV (fun _=>1) measurable_const
        (show (0:ℝ)≤1 by norm_num) (fun _ _=>by norm_num) hε
      filter_upwards [hh] with j hj
      simp only [mul_one] at hj
      rw [show (9*Real.log N)*(z-a)/F=C*(z-a) by
        calc (9*Real.log N)*(z-a)/F=((9*Real.log N)/F)*(z-a) := by ring
             _=C*(z-a) := by rw [hcommon]] at hj
      nlinarith
    · have hh := comparisonPhysicalSelectedRightContactCapTrace_eventually hc hk hkc hm hM
        hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD hbang
        ha haz hz hinitial.2 hneg as mesh ho hend hmesh hmesh0 hlim
        V hV hMV A hA hAcap hAV (fun _=>1) measurable_const
        (show (0:ℝ)≤1 by norm_num) (fun _ _=>by norm_num) hε
      have hsmall : z/F≤C*(z-a) := by
        rw [←hcommon,hinitial.1,sub_zero]
        have hmul := mul_le_mul_of_nonneg_right (show (1:ℝ)≤9*Real.log N by linarith)
          (div_nonneg (by linarith : 0≤z) hF.le)
        convert hmul using 1 <;> ring
      filter_upwards [hh] with j hj
      simp only [mul_one] at hj
      exact hj.trans (add_le_add (by
        convert mul_le_mul_of_nonneg_left hsmall hMV using 1 <;> ring) le_rfl)
    · have hh := comparisonPhysicalSelectedTerminalCapTrace_eventually hc hk hkc hm hM
        hN hlog hd hnd hlam hld n dphys e b h hb hlb hh hh0 α H J hH hJ hD hbang
        ha (by linarith [hterminal.2] : a<1) hterminal.1
        (by simpa only [hterminal.2] using hneg)
        as mesh ho hend hmesh hmesh0 hlim V hV hMV A hA
        (by simpa only [hterminal.2] using hAcap) hAV (fun _=>1) measurable_const
        (show (0:ℝ)≤1 by norm_num) (fun _ _=>by norm_num) hε
      filter_upwards [hh] with j hj
      simp only [mul_one] at hj
      have heq : (9*Real.log N)*(1-a)/
          ((n+1:ℝ)*(((1/3)/Real.log N)*laplaceComparisonStrength d lam 1))=C*(z-a) := by
        simpa only [F,hterminal.2] using
          (show (9*Real.log N)*(z-a)/F=C*(z-a) by
            calc (9*Real.log N)*(z-a)/F=((9*Real.log N)/F)*(z-a) := by ring
                 _=C*(z-a) := by rw [hcommon])
      rw [heq] at hj
      nlinarith
  filter_upwards [ht] with j hj
  dsimp only [C,Q,T] at hnormal ⊢
  nlinarith

end
end OAI.SKFluctuations.LaplaceWindowFormalization
