module

public import ComparisonActualHighWallThetaZeroEq7OrdinaryDyadGeometryDraft
public import ComparisonActualHighWallThetaZeroEq7BinFactorDraft
public import ComparisonActualHighWallThetaZeroEq7FixedStrengthDraft
public import ComparisonActualHighWallThetaZeroEq7OrdinaryCoreDraft
public import ComparisonActualHighWallThetaZeroEq7DiameterSquareDraft
public import ComparisonActualHighWallThetaZeroEq7OrdinaryReversePriceDraft
public import ComparisonActualHighWallThetaZeroEq7CutoffProjectionsDraft
public import ComparisonActualHighWallThetaZeroEq7LiteralLowPostPieceDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter Hierarchy
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 12000000

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eq7_ordinary_safe_reverse_ratio_at_mass_draft
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    {v r C Y y : ℝ}
    (hm : 0 ≤ m) (hdelta : 0 ≤ delta) (hC0 : 0 < C0)
    (hN : 1 ≤ Q.data.N) (hC0N : C0 ≤ Q.data.N)
    (hlog : 1 ≤ Real.log Q.data.N)
    (hA : Q.xs ≤ Q.data.N^(5+delta))
    (hC : 0 ≤ C) (hCN : C ≤ Q.data.N)
    (hY : 0 ≤ Y) (hYN : Y ≤ Q.data.N)
    (hv : 0 < v) (hvA : v ≤ C*Q.xs)
    (hy : 0 ≤ y) (hyA : y ≤ Y*Q.xs)
    (hr : 0 ≤ r) :
    y/(Q.localCapDiameter v 16+r) ≤ Q.data.N^(14+3*delta) := by
  have hNp : 0 < Q.data.N := Q.data.hN
  have hYprod := mul_le_mul hYN hA Q.hxs.le
    (zero_lt_one.trans_le hN).le
  have hPow : Q.data.N*Q.data.N^(5+delta) =
      Q.data.N^(6+delta) := by
    calc
      _ = Q.data.N^(1:ℝ)*Q.data.N^(5+delta) := by rw [Real.rpow_one]
      _ = Q.data.N^((1:ℝ)+(5+delta)) :=
        (Real.rpow_add hNp 1 (5+delta)).symm
      _ = _ := by congr 1; ring
  have hyN : y ≤ Q.data.N^(6+delta) := by
    rw [hPow] at hYprod
    exact hyA.trans hYprod
  have Hpost := Q.eq7_inner_post_exact_reverse_ratio_of_raw_gate_draft
    hm hdelta hC0 hN hC0N hlog hA hC hCN hv hvA hy hyN
  have hD : 0 < Q.localCapDiameter v 16 := by
    dsimp only [localCapDiameter]
    have hLp : 0 < Real.log Q.data.N := by linarith only [hlog]
    have hE := Q.data.hE
    have hd := Q.data.hd
    positivity
  have hden : Q.localCapDiameter v 16 ≤
      Q.localCapDiameter v 16+r := le_add_of_nonneg_right hr
  exact (div_le_div_of_nonneg_left hy hD hden).trans Hpost

theorem eq7_ordinary_atoms_at_mass_draft
    (Q : ActualThetaZeroOverlapMinimum
      (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (hell : 2 < ell)
    (q C eps v r F : ℝ)
    (hN : 1 ≤ Q.data.N) (hdelta : 0 ≤ delta)
    (heps : 0 < eps) (hlog : 1 ≤ Real.log Q.data.N)
    (hcl : 0 < cl) (hAz : 0 ≤ Az)
    (hcarrier : Q.xs = comparisonConditionalScale
      Q.data.N delta Q.data.E Q.lam)
    (hUA : comparisonSmallMass Q.data.N Q.data.E ≤ Q.xs)
    (hlamFloor : Q.data.N^(-(10:ℝ)) ≤ Q.lam)
    (hEfloor : Q.data.N^(-(5:ℝ)) ≤ Q.data.E)
    (hN3 : 72 ≤ Q.data.N^3)
    (hC : 0 ≤ C) (hv : 0 < v)
    (hUv : comparisonSmallMass Q.data.N Q.data.E ≤ v)
    (hvA : v ≤ C*Q.xs)
    (hu : min (16*v) 1 ∈ Set.Icc (0:ℝ) 1)
    (hF : 0 ≤ F ∧ F ≤
      comparisonEq7BinFactorConstant (30+10*delta)*
        (Real.log Q.data.N)^4)
    (hr : 0 ≤ r) (hrU : r ≤ comparisonSmallMass Q.data.N Q.data.E)
    (hq : 1 ≤ q)
    (horder : (14+3*delta)/((ell:ℝ)-1) ≤ eps)
    (hratio :
      (Q.xs+min (16*v) 1)/(Q.localCapDiameter v 16+r) ≤
        Q.data.N^(14+3*delta))
    (hKcut : q^4*(1+16*C)^2*(16*C)^2 ≤ Q.data.N) :
    let M := 16*v
    let u := min (16*v) 1
    let y := Q.xs+u
    let zg := Q.shiftedNativeModel.R u
    let e := laplaceComparisonStrength Q.data.d Q.lam zg
    let power := Q.data.N*e
    let diam := Q.localCapDiameter v 16+r
    let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
      ((2*q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
    let z := 18*(((q^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*
      Q.data.N^(-(30+10*delta))
    ComparisonEq7OrdinaryPieceAtoms Q.data.N delta eps Q.data.E Q.lam
      (Real.log Q.data.N) F M
      (2*((q^2*y)/(power*M^2))^((2:ℝ)/3))
      (3/(power*M^2)) (diam^2) rev z
      (comparisonEq7BinFactorConstant (30+10*delta)) C
      (1+16*C) (max 1 ((Az+1/cl)*(1+16*C))) q := by
  let M := 16*v
  let u := min (16*v) 1
  let y := Q.xs+u
  let zg := Q.shiftedNativeModel.R u
  let e := laplaceComparisonStrength Q.data.d Q.lam zg
  let power := Q.data.N*e
  let diam := Q.localCapDiameter v 16+r
  let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  let z := 18*(((q^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*
    Q.data.N^(-(30+10*delta))
  let K := max 1 ((Az+1/cl)*(1+16*C))
  have hD16 : Q.localCapDiameter v 16 =
      144*Real.log Q.data.N*Q.data.E/(Q.data.N^delta*Q.data.d^3*v) := by
    dsimp only [localCapDiameter]
    ring
  have hK : 1 ≤ K := le_max_left _ _
  have hC16 : 0 ≤ 16*C := by positivity
  have huA : u ≤ (16*C)*Q.xs := by
    have H := mul_le_mul_of_nonneg_left hvA
      (by norm_num : (0:ℝ) ≤ 16)
    dsimp only [u]
    linarith only [H,min_le_left (16*v) 1]
  have hy : 0 < y := by
    dsimp only [y,u]
    linarith only [Q.hxs,hu.1]
  have hyA : y ≤ (1+16*C)*Q.xs := by
    dsimp only [y,u]
    nlinarith only [huA]
  have hY : 0 ≤ 1+16*C := by positivity
  have hM : comparisonSmallMass Q.data.N Q.data.E ≤ M := by
    dsimp only [M]
    linarith only [hUv,hv]
  have he : 0 < e := by
    dsimp only [e]
    exact laplaceComparisonStrength_pos Q.data.d Q.hlam zg
  have hstrengthN := Q.eq7_fixed_strength_at_mass_draft
    hcl hAz hN hdelta hcarrier hu hC16 huA
  change Q.data.N*(Q.data.N^(-delta)*Q.lam) ≤ K*(Q.data.N*e) at hstrengthN
  have hstrength : Q.data.N^(-delta)*Q.lam ≤ K*e := by
    have H : Q.data.N*(Q.data.N^(-delta)*Q.lam) ≤
        Q.data.N*(K*e) := by
      calc
        _ ≤ K*(Q.data.N*e) := hstrengthN
        _ = Q.data.N*(K*e) := by
          rw [←mul_assoc,mul_comm K Q.data.N,mul_assoc]
    exact le_of_mul_le_mul_left H Q.data.hN
  have hyA' : y ≤ (1+16*C)*
      comparisonConditionalScale Q.data.N delta Q.data.E Q.lam := by
    simpa only [hcarrier] using hyA
  have hlog0 : 0 ≤ Real.log Q.data.N := by linarith only [hlog]
  have Hopt := comparison_eq7_ordinary_optimized_core_draft
    Q.data.hN Q.data.hE Q.hlam he hK hstrength hM
    hy.le hY hyA' hq
  have Hinv := comparison_eq7_ordinary_inverse_core_draft
    Q.data.hN Q.data.hE Q.hlam he hK hstrength hM
  have Hdiam := comparison_eq7_ordinary_diameter_square_price_draft
    Q.data.hN Q.data.hd Q.data.hE Q.hlam Q.hld Q.hupper
    Q.hxs hC hlog0 hcarrier hUv hvA hr hrU hUA
  have Hdiam' : Q.lam*M*diam^2 ≤
      (663552*(Real.log Q.data.N)^2*Q.data.N^(-2*delta)+
        32*C*Q.data.N^(2*delta))*Q.data.E := by
    calc
      _ ≤ 663552*(Real.log Q.data.N)^2*Q.data.N^(-2*delta)*Q.data.E+
          32*C*Q.data.N^(2*delta)*Q.data.E := by
        simpa only [M,diam,hD16] using Hdiam
      _ = _ := by ring
  have hD : 0 < diam := by
    dsimp only [diam,localCapDiameter]
    have hlogp : 0 < Real.log Q.data.N := by linarith only [hlog]
    have hNp := Real.rpow_pos_of_pos Q.data.hN delta
    have hE := Q.data.hE
    have hd := Q.data.hd
    have hlocal : 0 <
        9*Real.log Q.data.N*16*Q.data.E/
          (Q.data.N^delta*Q.data.d^3*v) := by positivity
    linarith only [hlocal,hr]
  have Hinterp : rev ≤ (2*q)^4*diam*y*Q.data.N^eps := by
    simpa only [rev,comparisonReverseMoment] using
      comparison_reverse_polynomial_loss hell hN hD hq hy
        hratio horder
  have hprod : Q.lam*Q.xs ≤ Q.data.N^delta*Q.data.d^3 := by
    rw [hcarrier]
    exact comparison_conditional_scale_strength_product
      Q.data.hN Q.data.hE Q.data.hd Q.hlam Q.hld Q.hupper
  have Hinterp' : rev ≤ (2*q)^4*
      (144*Real.log Q.data.N*Q.data.E/(Q.data.N^delta*Q.data.d^3*v)+r)*
        y*Q.data.N^eps := by
    simpa only [diam,hD16] using Hinterp
  have Hrev := comparison_eq7_ordinary_reverse_price_of_interpolation_draft
    Q.data.hN Q.data.hd Q.data.hE Q.hlam hv hlog0
    Q.hxs hC hY hcarrier hvA hr hrU hy.le hyA hprod
    Hinterp'
  have Hcut := Q.eq7_ordinary_cutoff_at_mass_draft
    q C (1+16*C) v hN hdelta hcarrier hlamFloor hEfloor
    hN3 hC hY hv.le hvA hy.le hyA hKcut
  change 0 ≤ F ∧ F ≤ comparisonEq7BinFactorConstant (30+10*delta)*
      (Real.log Q.data.N)^4 ∧
    Q.lam*M*(2*((q^2*y)/(power*M^2))^((2:ℝ)/3)) ≤
      2*(q^2*(1+16*C)*K)^((2:ℝ)/3)*
        Q.data.N^(4*delta/3)*Q.data.E ∧
    Q.lam*M*(3/(power*M^2)) ≤ 3*K*Q.data.N^delta*Q.data.E ∧
    Q.lam*M*diam^2 ≤
      (663552*(Real.log Q.data.N)^2*Q.data.N^(-2*delta)+
        32*C*Q.data.N^(2*delta))*Q.data.E ∧
    Q.lam*M*rev ≤
      (2*q)^4*(2304*(1+16*C)*Real.log Q.data.N+
        16*C*(1+16*C)*Q.data.N^(2*delta))*Q.data.N^eps*Q.data.E ∧
    Q.lam*z ≤ Q.data.E
  exact ⟨hF.1,hF.2,Hopt,Hinv,Hdiam',Hrev,Hcut⟩

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
