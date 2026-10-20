module

public import ComparisonActualHighWallThetaZeroEq7OrdinaryPieceNormalizationDraft
public import ComparisonActualHighWallThetaZeroEq7ExactBudgetJoinDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000

def comparisonEq7OrdinaryPieceConstant
    (Cbin C Y K q : ℝ) : ℝ :=
  Cbin*(2*(q^2*Y*K)^((2:ℝ)/3)+3*K+663552+32*C+
    (2*q)^4*(2304*Y+16*C*Y))+1

def ComparisonEq7OrdinaryPieceAtoms
    (N delta eps E lam L F M a b c r z Cbin C Y K q : ℝ) : Prop :=
  0 ≤ F ∧ F ≤ Cbin*L^4 ∧
  lam*M*a ≤ 2*(q^2*Y*K)^((2:ℝ)/3)*N^(4*delta/3)*E ∧
  lam*M*b ≤ 3*K*N^delta*E ∧
  lam*M*c ≤ (663552*L^2*N^(-2*delta)+32*C*N^(2*delta))*E ∧
  lam*M*r ≤ (2*q)^4*(2304*Y*L+16*C*Y*N^(2*delta))*N^eps*E ∧
  lam*z ≤ E

theorem comparison_eq7_piece_atoms_to_literal_budget_draft
    {N delta eps E lam L F M a b c r z Cbin C Y K q : ℝ}
    (hN : 1 ≤ N) (hE : 0 < E) (hdelta : 0 ≤ delta)
    (heps : 0 < eps) (hL : 1 ≤ L) (hLpow : L ≤ N^eps)
    (hCbin : 0 ≤ Cbin) (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hK : 1 ≤ K) (hq : 1 ≤ q)
    (hatoms : ComparisonEq7OrdinaryPieceAtoms
      N delta eps E lam L F M a b c r z Cbin C Y K q) :
    lam*(F*M*(a+b+c+r)+z) ≤
      comparisonEq7OrdinaryPieceConstant Cbin C Y K q*
        L^5*N^(2*delta+eps)*E := by
  rcases hatoms with ⟨hF0,hF,ha,hb,hc,hr,hz⟩
  exact comparison_eq7_ordinary_piece_from_atoms_draft
    hN hE hdelta heps hL hLpow hF0 hCbin hC hY hK hq
    hF ha hb hc hr hz

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eq7_inner_low_post_literal_piece_rates_draft
    (ell : ℕ) (hell : 2 < ell)
    (qLow qPost eps Cbin C Y K : ℝ)
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hN : 1 ≤ Q.data.N) (hdelta : 0 ≤ delta)
    (heps : 0 < eps)
    (hL : 1 ≤ Real.log Q.data.N)
    (hLpow : Real.log Q.data.N ≤ Q.data.N^eps)
    (hCbin : 0 ≤ Cbin) (hC : 0 ≤ C) (hY : 0 ≤ Y)
    (hK : 1 ≤ K) (hqLow : 1 ≤ qLow) (hqPost : 1 ≤ qPost)
    (hLow : ∀ {h : ℝ} (j : Eq7InnerLowDyad Q h),
      let v := Q.eq7InnerDyadMass j.val.val
      let M := 16*v
      let y := Q.xs+Q.eq7InnerDyadRight j.val.val
      let zg := Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)
      let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
      let diam := Q.localCapDiameter v 16+Q.data.rmin
      let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*qLow)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
      let F := nativeBinScaleLoss ((30+10*delta)*Real.log Q.data.N)
        (216*16^2*(Real.log Q.data.N)^2)
        (108*16^2*(Real.log Q.data.N)^2) M Q.data.s
      let z := 18*(((qLow^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*
        Q.data.N^(-(30+10*delta))
      ComparisonEq7OrdinaryPieceAtoms Q.data.N delta eps Q.data.E
        Q.lam (Real.log Q.data.N) F M
        (2*((qLow^2*y)/(power*M^2))^((2:ℝ)/3))
        (3/(power*M^2)) (diam^2) rev z Cbin C Y K qLow)
    (hPost : ∀ {h : ℝ} (j : Eq7InnerPostDyad Q h),
      let v := Q.eq7InnerDyadMass j.val.val
      let M := 16*v
      let y := Q.xs+Q.eq7InnerDyadRight j.val.val
      let zg := Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)
      let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
      let diam := Q.localCapDiameter v 16
      let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*qPost)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
      let F := nativeBinScaleLoss ((30+10*delta)*Real.log Q.data.N)
        (108*16^2*(Real.log Q.data.N)^2)
        (54*16^2*(Real.log Q.data.N)^2) M
        (Q.eq7InnerWallStart j.val.val)
      let z := 18*(((qPost^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*
        Q.data.N^(-(30+10*delta))
      ComparisonEq7OrdinaryPieceAtoms Q.data.N delta eps Q.data.E
        Q.lam (Real.log Q.data.N) F M
        (2*((qPost^2*y)/(power*M^2))^((2:ℝ)/3))
        (3/(power*M^2)) (diam^2) rev z Cbin C Y K qPost) :
    (∀ {h : ℝ} (j : Eq7InnerLowDyad Q h),
      Q.lam*Q.eq7InnerLowExactBudget ell qLow
        ((30+10*delta)*Real.log Q.data.N)
        (Q.data.N^(-(30+10*delta))) j ≤
      comparisonEq7OrdinaryPieceConstant Cbin C Y K qLow*
        (Real.log Q.data.N)^5*Q.data.N^(2*delta+eps)*Q.data.E) ∧
    (∀ {h : ℝ} (j : Eq7InnerPostDyad Q h),
      Q.lam*Q.eq7InnerPostExactBudget ell qPost
        ((30+10*delta)*Real.log Q.data.N)
        (Q.data.N^(-(30+10*delta))) j ≤
      comparisonEq7OrdinaryPieceConstant Cbin C Y K qPost*
        (Real.log Q.data.N)^5*Q.data.N^(2*delta+eps)*Q.data.E) := by
  constructor
  · intro h j
    let v := Q.eq7InnerDyadMass j.val.val
    let M := 16*v
    let y := Q.xs+Q.eq7InnerDyadRight j.val.val
    let zg := Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)
    let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
    let diam := Q.localCapDiameter v 16+Q.data.rmin
    let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
      ((2*qLow)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
    let F := nativeBinScaleLoss ((30+10*delta)*Real.log Q.data.N)
      (216*16^2*(Real.log Q.data.N)^2)
      (108*16^2*(Real.log Q.data.N)^2) M Q.data.s
    let z := 18*(((qLow^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*
      Q.data.N^(-(30+10*delta))
    have H := comparison_eq7_piece_atoms_to_literal_budget_draft
      hN Q.data.hE hdelta heps hL hLpow hCbin hC hY hK hqLow
      (hLow j)
    change Q.lam*(F*M*(2*((qLow^2*y)/(power*M^2))^((2:ℝ)/3)+
      3/(power*M^2)+diam^2+rev)+z) ≤ _
    exact H
  · intro h j
    let v := Q.eq7InnerDyadMass j.val.val
    let M := 16*v
    let y := Q.xs+Q.eq7InnerDyadRight j.val.val
    let zg := Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)
    let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
    let diam := Q.localCapDiameter v 16
    let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
      ((2*qPost)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
    let F := nativeBinScaleLoss ((30+10*delta)*Real.log Q.data.N)
      (108*16^2*(Real.log Q.data.N)^2)
      (54*16^2*(Real.log Q.data.N)^2) M
      (Q.eq7InnerWallStart j.val.val)
    let z := 18*(((qPost^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*
      Q.data.N^(-(30+10*delta))
    have H := comparison_eq7_piece_atoms_to_literal_budget_draft
      hN Q.data.hE hdelta heps hL hLpow hCbin hC hY hK hqPost
      (hPost j)
    change Q.lam*(F*M*(2*((qPost^2*y)/(power*M^2))^((2:ℝ)/3)+
      3/(power*M^2)+diam^2+rev)+z) ≤ _
    exact H

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
