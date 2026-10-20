module

public import ComparisonActualHighWallThetaZeroEq7OrdinaryAtomAssemblyDraft
public import ComparisonActualHighWallThetaZeroEq7BinFactorDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eq7_inner_low_post_uniform_exact_budget_rates_draft
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (hell : 2 < ell)
    (qLow qPost eps C h : ℝ)
    (hm : 0 ≤ m) (hdelta : 0 ≤ delta)
    (heps : 0 < eps) (horder :
      (14+3*delta)/((ell:ℝ)-1) ≤ eps)
    (hcl : 0 < cl) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (hN : 1 ≤ Q.data.N) (hC0N : C0 ≤ Q.data.N)
    (hlog : 1 ≤ Real.log Q.data.N)
    (hlogPow : Real.log Q.data.N ≤ Q.data.N^eps)
    (hdepth : 1/Q.data.N ≤ Q.data.d)
    (hcarrier : Q.xs = comparisonConditionalScale
      Q.data.N delta Q.data.E Q.lam)
    (hUA : comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs)
    (hlamFloor : Q.data.N^(-(10:ℝ)) ≤ Q.lam)
    (hC : 2 ≤ C) (hh : h ≤ C*Q.xs)
    (hCN : C ≤ Q.data.N)
    (hYN : 1+16*C ≤ Q.data.N)
    (hN3 : 72 ≤ Q.data.N^3)
    (hqLow : 1 ≤ qLow) (hqPost : 1 ≤ qPost)
    (hKcutLow : qLow^4*(1+16*C)^2*(16*C)^2 ≤ Q.data.N)
    (hKcutPost : qPost^4*(1+16*C)^2*(16*C)^2 ≤ Q.data.N) :
    let beta := 30+10*delta
    let L := Real.log Q.data.N
    let cut := Q.data.N^(-beta)
    let Cbin := comparisonEq7BinFactorConstant beta
    let Y := 1+16*C
    let K := max 1 ((Az+1/cl)*(1+16*C))
    (∀ j : Eq7InnerLowDyad Q h,
      Q.lam*Q.eq7InnerLowExactBudget ell qLow (beta*L) cut j ≤
        comparisonEq7OrdinaryPieceConstant Cbin C Y K qLow*
          L^5*Q.data.N^(2*delta+eps)*Q.data.E) ∧
    (∀ j : Eq7InnerPostDyad Q h,
      Q.lam*Q.eq7InnerPostExactBudget ell qPost (beta*L) cut j ≤
        comparisonEq7OrdinaryPieceConstant Cbin C Y K qPost*
          L^5*Q.data.N^(2*delta+eps)*Q.data.E) := by
  let beta := 30+10*delta
  let L := Real.log Q.data.N
  let cut := Q.data.N^(-beta)
  let Cbin := comparisonEq7BinFactorConstant beta
  let Y := 1+16*C
  let K := max 1 ((Az+1/cl)*(1+16*C))
  have hC0' : 0 ≤ C := by linarith only [hC]
  have hY : 0 ≤ Y := by dsimp only [Y]; positivity
  have hK : 1 ≤ K := le_max_left _ _
  have hbeta : 0 ≤ beta := by dsimp only [beta]; linarith only [hdelta]
  have hCbin : 0 ≤ Cbin := by
    dsimp only [Cbin,comparisonEq7BinFactorConstant,
      comparisonEq7BinTemperatureConstant]
    positivity
  have hEfloor := Q.eq7_ordinary_cutoff_energy_floor_draft
    hm hC0 hN hC0N hdepth
  have hAupper : Q.xs ≤ Q.data.N^(5+delta) := by
    rw [hcarrier]
    exact comparison_eq7_conditional_scale_upper_of_floor_draft
      hN Q.data.hE Q.data.hd Q.data.hd1 Q.hlam Q.hupper hlamFloor
  have hLowAtoms : ∀ {u : ℝ} (j : Eq7InnerLowDyad Q u),
      let v := Q.eq7InnerDyadMass j.val.val
      let M := 16*v
      let y := Q.xs+Q.eq7InnerDyadRight j.val.val
      let zg := Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)
      let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
      let diam := Q.localCapDiameter v 16+Q.data.rmin
      let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*qLow)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
      let F := nativeBinScaleLoss (beta*L)
        (216*16^2*L^2) (108*16^2*L^2) M Q.data.s
      let z := 18*(((qLow^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*cut
      ComparisonEq7OrdinaryPieceAtoms Q.data.N delta eps Q.data.E
        Q.lam L F M
        (2*((qLow^2*y)/(power*M^2))^((2:ℝ)/3))
        (3/(power*M^2)) (diam^2) rev z Cbin C Y K qLow := by
    intro u j
    let v := Q.eq7InnerDyadMass j.val.val
    have hv : 0 < v := (comparison_mass_dyadic_scale Q.data.hU j.val.val).1
    have hvA : v ≤ C*Q.xs := Q.eq7_inner_low_mass_le_carrier_draft j hC
    obtain ⟨hUv,_,hu,_,hy,hyA⟩ :=
      Q.eq7_inner_dyad_common_scalar_geometry_draft j.val hC0' hvA
    have hF := Q.eq7_inner_low_native_bin_factor_bound_draft j hbeta hlog
    have hr : 0 ≤ Q.data.rmin := Q.data.hrbounds.1.le
    have hrU := Q.radius_le_smallMass
    have hratio := Q.eq7_ordinary_safe_reverse_ratio_at_mass_draft
      hm hdelta hC0 hN hC0N hlog hAupper hC0' hCN
      hY hYN hv hvA hy.le hyA hr
    have H := Q.eq7_ordinary_atoms_at_mass_draft ell hell qLow C eps
      v Q.data.rmin
      (nativeBinScaleLoss (beta*L) (216*16^2*L^2)
        (108*16^2*L^2) (16*v) Q.data.s)
      hN hdelta heps hlog hcl hAz hcarrier hUA hlamFloor
      hEfloor hN3 hC0' hv hUv hvA hu hF hr hrU hqLow
      horder hratio hKcutLow
    simpa only [beta,L,Cbin,Y,K,cut,eq7InnerDyadRight]
      using H
  have hPostAtoms : ∀ (j : Eq7InnerPostDyad Q h),
      let v := Q.eq7InnerDyadMass j.val.val
      let M := 16*v
      let y := Q.xs+Q.eq7InnerDyadRight j.val.val
      let zg := Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)
      let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
      let diam := Q.localCapDiameter v 16
      let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*qPost)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
      let F := nativeBinScaleLoss (beta*L)
        (108*16^2*L^2) (54*16^2*L^2) M
        (Q.eq7InnerWallStart j.val.val)
      let z := 18*(((qPost^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*cut
      ComparisonEq7OrdinaryPieceAtoms Q.data.N delta eps Q.data.E
        Q.lam L F M
        (2*((qPost^2*y)/(power*M^2))^((2:ℝ)/3))
        (3/(power*M^2)) (diam^2) rev z Cbin C Y K qPost := by
    intro j
    let v := Q.eq7InnerDyadMass j.val.val
    have hv : 0 < v := (comparison_mass_dyadic_scale Q.data.hU j.val.val).1
    have hvA : v ≤ C*Q.xs := Q.eq7_inner_post_mass_le_carrier_draft j hh
    obtain ⟨hUv,_,hu,_,hy,hyA⟩ :=
      Q.eq7_inner_dyad_common_scalar_geometry_draft j.val hC0' hvA
    have hF := Q.eq7_inner_post_native_bin_factor_bound_draft j hbeta hlog
    have hratio := Q.eq7_ordinary_safe_reverse_ratio_at_mass_draft
      hm hdelta hC0 hN hC0N hlog hAupper hC0' hCN
      hY hYN hv hvA hy.le hyA (by norm_num : (0:ℝ) ≤ 0)
    have H := Q.eq7_ordinary_atoms_at_mass_draft ell hell qPost C eps
      v 0
      (nativeBinScaleLoss (beta*L) (108*16^2*L^2)
        (54*16^2*L^2) (16*v) (Q.eq7InnerWallStart j.val.val))
      hN hdelta heps hlog hcl hAz hcarrier hUA hlamFloor
      hEfloor hN3 hC0' hv hUv hvA hu hF
      (by norm_num : (0:ℝ) ≤ 0) Q.data.hU.le hqPost
      horder hratio hKcutPost
    simpa only [beta,L,Cbin,Y,K,cut,eq7InnerDyadRight,add_zero]
      using H
  constructor
  · intro j
    have H := comparison_eq7_piece_atoms_to_literal_budget_draft
      hN Q.data.hE hdelta heps hlog hlogPow
      hCbin hC0' hY hK hqLow (hLowAtoms j)
    simpa only [eq7InnerLowExactBudget,ordinaryOptimizedBudgetPositiveOrigin,
      beta,L,Cbin,Y,K,cut,eq7InnerDyadRight] using H
  · intro j
    have H := comparison_eq7_piece_atoms_to_literal_budget_draft
      hN Q.data.hE hdelta heps hlog hlogPow
      hCbin hC0' hY hK hqPost (hPostAtoms j)
    simpa only [eq7InnerPostExactBudget,ordinaryOptimizedBudget,
      beta,L,Cbin,Y,K,cut,eq7InnerDyadRight] using H

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
