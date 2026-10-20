module

public import ComparisonPhysicalGeometry
public import ComparisonIntegratedDefect

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open MeasureTheory Filter Set Hierarchy
open scoped Topology NNReal

theorem exists_concrete_comparison_optimizer_defect
    {N δ U L E d lam : ℝ} (hN : 0<N) (hU : 0<U) (hL : 0<L)
    (hLU : L≤U) (hE : 0<E) (hd : 0<d) (hq : 2≤N^δ) (hlam : 0<lam)
    (b : ℝ → ℝ) (hb : MonotoneOn b (Icc (0:ℝ) 1)) (hlb : lam≤b 0)
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
    ∃ α : inverseIntegralConstraints 0 0 k M,
      comparisonSweepObjective hc hk hkc hm hM n b d lam α=
        comparisonSweepMinimum hc hk hkc hm hM n b d lam ∧
      let R := comparisonSweepQuantile hc hk hkc hm hM α
      let bf := fun u=>(b u-g (R u)).toNNReal
      let hf := fun u=>(g (R u)*R u).toNNReal
      let S := orderedPathS n bf hf
      let B := orderedPathB n bf hf
      (∫u in (0:ℝ)..1,(S u-R u)^2)≤N^(-δ)*U+
        64*((L/N^δ)*Real.log ((1+U)/U))^2+
        2*(∫u in (0:ℝ)..1,B u-(S u)^2) := by
  dsimp only
  let k := comparisonFloor N δ U
  let M := comparisonCap N δ U L E d
  have hc : 0<k 1 := comparisonFloor_pos hN hU (by norm_num)
  have hk : ContinuousOn k (Icc (0:ℝ) 1) := comparisonFloor_continuousOn (δ:=δ) hN hU le_rfl
  have hkc : ∀ r∈Icc (0:ℝ) 1,k 1≤k r := fun r hr=>comparisonFloor_lower_on (δ:=δ) hN hU le_rfl hr
  have hm : MonotoneOn M (Icc (0:ℝ) 1) := comparisonCap_monotoneOn (δ:=δ) hN hU.le hL hE hd.le
  have hM : 0≤M 1 := comparisonCap_nonneg (δ:=δ) hN hU.le hL hE hd.le zero_le_one
  obtain ⟨α,H,hmin,hH,hD,hbang,hzero⟩ := exists_concrete_comparison_optimizer_potential
    hN hU hL hLU hE hd hq hlam b hb hlb n hn
  let g := laplaceComparisonStrength d lam
  let R := comparisonSweepQuantile hc hk hkc hm hM α
  let bf := fun u=>(b u-g (R u)).toNNReal
  let hf := fun u=>(g (R u)*R u).toNNReal
  let S := orderedPathS n bf hf
  let B := orderedPathB n bf hf
  let Sr := fun r=>S (α.val.val r)
  let Br := fun r=>B (α.val.val r)
  let p := comparisonLogSlope g
  let J := inverseControlFactor 0 (fun r=>inverseControlWeight α.val.val k M r*
    comparisonCapSlope N δ U L E d (α.val.val r))
  let W := (L/N^δ)*Real.log ((1+U)/U)
  have hWp : 0<W := mul_pos (div_pos hL (Real.rpow_pos_of_pos hN _))
    (Real.log_pos ((lt_div_iff₀ hU).mpr (by linarith)))
  have hJg (r : ℝ) (_ : r∈Icc (0:ℝ) 1) : 0<J r*g r :=
    mul_pos (inverseControlFactor_pos _ _ _) (laplaceComparisonStrength_pos d hlam r)
  have hDp : ∀ᵐ r,r∈Icc (0:ℝ) 1→HasDerivAt H
      ((J r*g r)*comparisonBracket (p r) r (Sr r) (Br r)) r := by
    filter_upwards [hD,volume.ae_ne (0:ℝ)] with r hdr hr0 hr
    have hrpos : 0<r := lt_of_le_of_ne hr.1 hr0.symm
    have hh := hdr hr
    rw [comparison_gradient_slope hrpos.ne' (laplaceComparisonStrength_pos d hlam r).ne'] at hh
    convert hh using 1
    dsimp only [Sr,Br,S,B,bf,hf,J,g,R,p,comparisonBracket]
    ring
  have hpm : MonotoneOn p (Ioc (0:ℝ) 1) := by
    intro r hr t ht hrt
    dsimp only [p,g]
    rw [laplaceComparisonStrength_logSlope hd.ne' hlam.ne',laplaceComparisonStrength_logSlope hd.ne' hlam.ne']
    exact laplaceComparisonSlope_monotone (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hrt hlam.le) (pow_nonneg hd.le _))
  have hpb (r : ℝ) (_ : r∈Ioc (0:ℝ) 1) : p r∈Icc (0:ℝ) 1 :=
    ⟨(laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).1,
      (laplaceComparisonStrength_logSlope_mem hd.ne' hlam.ne' r).2.le⟩
  have hmom := comparisonSweep_radius_moments hc hk hkc hm hM n hn b hd.ne' hlam.le hlb hb α
  have htravel : (∫u in (0:ℝ)..1,1/M u)≤W := by
    simpa only [zero_add] using comparisonCap_log_travel (δ:=δ) hN hU hL hE hd.le
      (a:=0) (b:=1) le_rfl zero_le_one
  have hdef := potential_comparison_integrated_defect hWp hH hJg hDp hbang
    (hzero.mono (fun r hr hri hz=>(hr hri hz).2.2)) hpm hpb hmom.1 hmom.2.1
    (fun r hr=>(hmom.2.2 r hr).1) (fun r hr=>(hmom.2.2 r hr).2)
    (inverseIntegralConstraints_lipschitz hm hM α.property)
    (inverseConstraint_strictMonoOn hc hk hkc α.property)
    (fun r _=>α.val.property.1 r) α.property.1 α.property.2.1 hk
    (fun r hr=>(comparisonFloor_pos (δ:=δ) hN hU hr.1).le)
    (comparisonCap_continuous N δ U L E d).continuousOn
    (fun u hu=>(comparisonCap_first_term (δ:=δ) hN hU hL hE hd.le hu.1).1) htravel
  refine ⟨α,hmin,?_⟩
  rw [comparisonSweep_mismatch_substitution hc hk hkc hm hM α S,
    comparisonSweep_thermal_substitution hc hk hkc hm hM α S B]
  exact hdef.trans (by linarith [comparisonFloor_total_mass (δ:=δ) hN hU])

end OAI.SKFluctuations.LaplaceWindowFormalization
