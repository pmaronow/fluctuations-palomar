module

public import ComparisonActualGeneralTargetResponseLevelVariableSavedNumerics

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open scoped BigOperators
set_option maxHeartbeats 18000000

theorem actual_general_finite_level_sum_le
    (depth : ℕ) (f : Fin depth→ℝ) (a : ℝ) (hf : ∀j,f j ≤ a) :
    (∑j : Fin depth,f j) ≤ (depth:ℝ)*a := by
  calc
    _ ≤ ∑_j : Fin depth,a:=Finset.sum_le_sum (fun j _=>hf j)
    _ = (depth:ℝ)*a:=by simp

theorem exists_actual_general_target_response_common_modulus_constant
    (depth : ℕ) (den Cd CA CB CF CZ CQ CT CI : ℝ)
    (hden : 0 < den) (hCd : 0 ≤ Cd)
    (hCA : 0 ≤ CA) (hCB : 0 ≤ CB) (hCF : 0 ≤ CF) (hCZ : 0 ≤ CZ)
    (hCQ : 0 ≤ CQ) (hCT : 0 ≤ CT) (hCI : 0 ≤ CI) :
    ∃Creader : ℝ,0 < Creader ∧
      ∀d R eta : ℝ,0 < d → 0 ≤ R → 0 ≤ eta →
      ∀A B F Z : Fin depth→ℝ,∀Q T I : ℝ,
        (∀j,A j ≤ CA*(R+eta)) → (∀j,B j ≤ CB*d*(R+eta)) →
        (∀j,F j ≤ CF*eta) → (∀j,Z j ≤ CZ) →
        Q ≤ CQ*eta → T ≤ CT*eta → I ≤ CI →
        (depth:ℝ)*(d^2*(∑j : Fin depth,B j)/den+
          d^3*((Cd*Q+∑j : Fin depth,A j)/den+
            (∑j : Fin depth,F j)+(∑j : Fin depth,Z j)*d^2))+
          T*d^3+I*d^5 ≤ Creader*d^3*(R+eta+d^2) := by
  let vA:=(depth:ℝ)*CA
  let vB:=(depth:ℝ)*CB
  let vF:=(depth:ℝ)*CF
  let vZ:=(depth:ℝ)*CZ
  let K:=(depth:ℝ)*(vB/den+(Cd*CQ+vA)/den+vF+vZ)+CT+CI
  have hdepth : (0:ℝ) ≤ depth:=Nat.cast_nonneg _
  have hvA : 0 ≤ vA:=mul_nonneg hdepth hCA
  have hvB : 0 ≤ vB:=mul_nonneg hdepth hCB
  have hvF : 0 ≤ vF:=mul_nonneg hdepth hCF
  have hvZ : 0 ≤ vZ:=mul_nonneg hdepth hCZ
  have hK : 0 ≤ K:=by dsimp only [K];positivity
  refine ⟨K+1,by linarith,?_⟩
  intro d R eta hd hR heta A B F Z Q T I HA HB HF HZ HQ HT HI
  let X:=R+eta+d^2
  have hX : 0 ≤ X:=by dsimp only [X];positivity
  have hRX : R+eta ≤ X:=by dsimp only [X];linarith [sq_nonneg d]
  have hetaX : eta ≤ X:=by dsimp only [X];linarith [sq_nonneg d]
  have hdX : d^2 ≤ X:=by dsimp only [X];linarith
  have HAsum : (∑j : Fin depth,A j) ≤ vA*X:=by
    have H:=actual_general_finite_level_sum_le depth A (CA*X)
      (fun j=>(HA j).trans (mul_le_mul_of_nonneg_left hRX hCA))
    convert H using 1
    ring
  have HBsum : (∑j : Fin depth,B j) ≤ vB*d*X:=by
    have H:=actual_general_finite_level_sum_le depth B (CB*d*X)
      (fun j=>(HB j).trans (mul_le_mul_of_nonneg_left hRX (mul_nonneg hCB hd.le)))
    convert H using 1
    ring
  have HFsum : (∑j : Fin depth,F j) ≤ vF*X:=by
    have H:=actual_general_finite_level_sum_le depth F (CF*X)
      (fun j=>(HF j).trans (mul_le_mul_of_nonneg_left hetaX hCF))
    convert H using 1
    ring
  have HZsum : (∑j : Fin depth,Z j) ≤ vZ:=
    actual_general_finite_level_sum_le depth Z CZ HZ
  have Hq : Cd*Q ≤ (Cd*CQ)*X:=by
    have H:=mul_le_mul_of_nonneg_left
      (HQ.trans (mul_le_mul_of_nonneg_left hetaX hCQ)) hCd
    convert H using 1
    ring
  have Hnumer : Cd*Q+(∑j : Fin depth,A j) ≤ (Cd*CQ+vA)*X:=by
    have H:=add_le_add Hq HAsum
    nlinarith only [H]
  have Hfirst : d^2*(∑j : Fin depth,B j)/den ≤ d^3*(vB/den)*X:=by
    calc
      _ ≤ d^2*(vB*d*X)/den:=div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left HBsum (sq_nonneg d)) hden.le
      _ = d^3*(vB/den)*X:=by ring
  have Hfrac : (Cd*Q+(∑j : Fin depth,A j))/den ≤ ((Cd*CQ+vA)/den)*X:=by
    calc
      _ ≤ ((Cd*CQ+vA)*X)/den:=div_le_div_of_nonneg_right Hnumer hden.le
      _ = ((Cd*CQ+vA)/den)*X:=by ring
  have HZ : (∑j : Fin depth,Z j)*d^2 ≤ vZ*X:=
    (mul_le_mul_of_nonneg_right HZsum (sq_nonneg d)).trans
      (mul_le_mul_of_nonneg_left hdX hvZ)
  have Hinside:=add_le_add (add_le_add Hfrac HFsum) HZ
  have HT' : T*d^3 ≤ CT*d^3*X:=by
    have H:=mul_le_mul_of_nonneg_right
      (HT.trans (mul_le_mul_of_nonneg_left hetaX hCT)) (pow_nonneg hd.le 3)
    convert H using 1
    ring
  have HI' : I*d^5 ≤ CI*d^3*X:=by
    calc
      _ ≤ CI*d^5:=mul_le_mul_of_nonneg_right HI (pow_nonneg hd.le 5)
      _ = CI*d^3*d^2:=by ring
      _ ≤ CI*d^3*X:=mul_le_mul_of_nonneg_left hdX (mul_nonneg hCI (pow_nonneg hd.le 3))
  have H:=add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left
      (add_le_add Hfirst (mul_le_mul_of_nonneg_left Hinside (pow_nonneg hd.le 3))) hdepth)
    HT') HI'
  calc
    _ ≤ (depth:ℝ)*(d^3*(vB/den)*X+
      d^3*(((Cd*CQ+vA)/den)*X+vF*X+vZ*X))+CT*d^3*X+CI*d^3*X:=H
    _ = K*d^3*X:=by dsimp only [K];ring
    _ ≤ (K+1)*d^3*X:=by
      have HH:=mul_nonneg (pow_nonneg hd.le 3) hX
      nlinarith only [HH]

end OAI.SKFluctuations.Cavity
