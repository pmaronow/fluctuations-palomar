module

public import ActualComparisonContact
public import VariableEndpointComparisonPotential

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem exists_concrete_variableEndpoint_optimizer_contact_derivative
    {N δ U L E d lam : ℝ} (hN : 0<N) (hU : 0<U) (hL : 0<L)
    (hLU : L≤U) (hE : 0<E) (hd : 0<d) (hq : 2≤N^δ) (hlam : 0<lam)
    (hNlarge : 1≤N) (hlog : 1≤Real.log N) (hnd : 1/N≤d) (hld : lam≤d^2)
    (b h : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam≤b 0)
    (hh : MonotoneOn h (Icc (0:ℝ) 1)) (hh0 : 0≤h 0)
    (n : ℕ) (hn : 0<n) :
    let k := comparisonFloor N δ U
    let M := comparisonCap N δ U L E d
    let c := k 1
    let hc : 0<c := comparisonFloor_pos hN hU (by norm_num)
    let hk := comparisonFloor_continuousOn (δ:=δ) hN hU (r₀:=0) le_rfl
    let hkc := fun r (hr : r∈Icc (0:ℝ) 1)=>comparisonFloor_lower_on (δ:=δ) hN hU le_rfl hr
    let hm := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
    let hM := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le zero_le_one
    let g := laplaceComparisonStrength d lam
    ∃ (α : inverseIntegralConstraints 0 0 k M) (H : ℝ → ℝ),
      (∀γ:inverseIntegralConstraints 0 0 k M,
        comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam α≤
          comparisonVariableEndpointObjective hc hk hkc hm hM n b h d lam γ) ∧
      let R := comparisonSweepQuantile hc hk hkc hm hM α
      let bf := fun u=>(b u-g (R u)).toNNReal
      let hf := fun u=>(h u+g (R u)*R u).toNNReal
      let S := orderedPathS n bf hf
      let B := orderedPathB n bf hf
      let J := inverseControlFactor 0 (fun r=>inverseControlWeight α.val.val k M r*
        comparisonCapSlope N δ U L E d (α.val.val r))
      AbsolutelyContinuousOnInterval H 0 1 ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
        (J r*radiusComparisonGradient g α.val.val S B r) r) ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→
        (H r<0→deriv α.val.val r=M (α.val.val r)) ∧
        (0<H r→deriv α.val.val r=k r)) ∧
      (∀ᵐ r,r∈Icc (0:ℝ) 1→H r=0→
        radiusComparisonGradient g α.val.val S B r=0 ∧
        S (α.val.val r)≤r ∧
        (S (α.val.val r)-r)^2≤B (α.val.val r)-(S (α.val.val r))^2 ∧
        deriv (fun t=>S (α.val.val t)) r≤9*Real.log N) := by
  dsimp only
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  have hc : 0<k 1 := comparisonFloor_pos hN hU (by norm_num)
  have hk : ContinuousOn k (Icc (0:ℝ) 1) := comparisonFloor_continuousOn (δ:=δ) hN hU le_rfl
  have hkc : ∀r∈Icc (0:ℝ) 1,k 1≤k r := fun r hr=>comparisonFloor_lower_on (δ:=δ) hN hU le_rfl hr
  have hm : MonotoneOn M (Icc (0:ℝ) 1) := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
  have hM : 0≤M 1 := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le zero_le_one
  obtain ⟨α,H,hmin,hH,hD,hbang,hzero⟩ := exists_concrete_variableEndpoint_optimizer_potential
    hN hU hL hLU hE hd hq hlam b h hb hlb hh hh0 n hn
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
  have hpm : MonotoneOn p (Ioc (0:ℝ) 1) := by
    intro r hr t ht hrt
    dsimp only [p,g]
    rw [laplaceComparisonStrength_logSlope hd.ne' hlam.ne',laplaceComparisonStrength_logSlope hd.ne' hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt hlam.le) (pow_nonneg hd.le _))
  have hpb (r : ℝ) (hr : r∈Ioc (0:ℝ) 1) : p r∈Icc (0:ℝ) (1-κ) :=
    ⟨(laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).1,by
      have hh := laplaceComparisonStrength_uniform_slope hNlarge hlog hd hnd hlam hld ⟨hr.1.le,hr.2⟩
      dsimp only [κ,p,g]
      linarith⟩
  have hmom := comparisonVariableEndpoint_radius_moments hc hk hkc hm hM n hn b h hd.ne' hlam.le hlb hb hh hh0 α
  have hcontact := comparison_contact_ae_deriv_le hκ hpm hpb hmom.1
    (hmom.2.1.mono Ioc_subset_Icc_self)
    (fun r hr=>((hmom.2.2 r ⟨hr.1.le,hr.2⟩).1).1)
    (fun r hr=>((hmom.2.2 r ⟨hr.1.le,hr.2⟩).2).1)
  have hconstant : 3/κ=9*Real.log N := by dsimp [κ];field_simp;ring
  refine ⟨α,H,hmin,hH,hD,hbang,?_⟩
  filter_upwards [hzero,hcontact,volume.ae_ne (0:ℝ)] with r hzr hcr hr0 hr hHr
  have hrpos : 0<r := lt_of_le_of_ne hr.1 hr0.symm
  have hz := hzr hr hHr
  refine ⟨hz.1,hz.2.1,hz.2.2,?_⟩
  have hbr : comparisonBracket (p r) r (Sr r) (Br r)=0 := by
    have hg0 := hz.1
    rw [comparison_gradient_slope hrpos.ne' (laplaceComparisonStrength_pos d hlam r).ne'] at hg0
    have hh : g r*comparisonBracket (p r) r (Sr r) (Br r)=0 := by
      simpa only [g,p,Sr,Br,S,B,bf,hf,R,comparisonBracket] using hg0
    exact (mul_eq_zero.mp hh).resolve_left (laplaceComparisonStrength_pos d hlam r).ne'
  simpa only [hconstant] using hcr ⟨hrpos,hr.2⟩ hbr

end OAI.SKFluctuations.LaplaceWindowFormalization
