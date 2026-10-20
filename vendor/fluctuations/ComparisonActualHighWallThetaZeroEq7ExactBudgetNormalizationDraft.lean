module

public import ComparisonActualHighWallThetaZeroEq7ExactBudgetJoinDraft

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000

theorem comparison_eq7_ordinary_literal_components_draft
    {lam L X F M a b c r z Cbin Ka Kb Kc Kr Kz : ℝ}
    (hL : 1 ≤ L) (hX : 0 ≤ X) (hF : 0 ≤ F)
    (hCbin : 0 ≤ Cbin)
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKc : 0 ≤ Kc)
    (hKr : 0 ≤ Kr) (hKz : 0 ≤ Kz)
    (hscale : F ≤ Cbin*L^4)
    (ha : lam*M*a ≤ Ka*L*X)
    (hb : lam*M*b ≤ Kb*L*X)
    (hc : lam*M*c ≤ Kc*L*X)
    (hr : lam*M*r ≤ Kr*L*X)
    (hz : lam*z ≤ Kz*L^5*X) :
    lam*(F*M*(a+b+c+r)+z) ≤
      (Cbin*(Ka+Kb+Kc+Kr)+Kz)*L^5*X := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have hB : 0 ≤ (Ka+Kb+Kc+Kr)*L*X := by positivity
  have hsum : lam*M*(a+b+c+r) ≤ (Ka+Kb+Kc+Kr)*L*X := by
    nlinarith only [ha,hb,hc,hr]
  have h1 := mul_le_mul_of_nonneg_left hsum hF
  have h2 := mul_le_mul_of_nonneg_right hscale hB
  nlinarith only [h1,h2,hz]

theorem comparison_eq7_broad_literal_components_draft
    {lam L X side diameter reverse covariance cutoff
      Ks Kd Kr Kc Kz : ℝ}
    (hL : 1 ≤ L) (hX : 0 ≤ X)
    (hKs : 0 ≤ Ks) (hKd : 0 ≤ Kd) (hKr : 0 ≤ Kr)
    (hKc : 0 ≤ Kc) (hKz : 0 ≤ Kz)
    (hs : lam*side ≤ Ks*L^5*X)
    (hd : lam*diameter ≤ Kd*L^5*X)
    (hr : lam*reverse ≤ Kr*L^5*X)
    (hc : lam*covariance ≤ Kc*L^5*X)
    (hz : lam*cutoff ≤ Kz*L^5*X) :
    lam*(side+diameter+reverse+covariance+cutoff) ≤
      (Ks+Kd+Kr+Kc+Kz)*L^5*X := by
  nlinarith only [hs,hd,hr,hc,hz]

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem eq7_inner_low_exact_rate_of_components_draft
    {h : ℝ} (j : Eq7InnerLowDyad Q h)
    (ell : ℕ) (q Lside cut eps Cbin Ka Kb Kc Kr Kz : ℝ)
    (hlog : 1 ≤ Real.log Q.data.N)
    (hCbin : 0 ≤ Cbin)
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKc : 0 ≤ Kc)
    (hKr : 0 ≤ Kr) (hKz : 0 ≤ Kz)
    (hscale :
      let v := Q.eq7InnerDyadMass j.val.val
      let M := 16*v
      let F := nativeBinScaleLoss Lside
        (216*16^2*(Real.log Q.data.N)^2)
        (108*16^2*(Real.log Q.data.N)^2) M Q.data.s
      0 ≤ F ∧ F ≤ Cbin*(Real.log Q.data.N)^4)
    (hcomponents :
      let v := Q.eq7InnerDyadMass j.val.val
      let M := 16*v
      let y := Q.xs+Q.eq7InnerDyadRight j.val.val
      let zg := Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)
      let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
      let diam := Q.localCapDiameter v 16+Q.data.rmin
      let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
      let X := Q.data.N^(2*delta+eps)*Q.data.E
      Q.lam*M*(2*((q^2*y)/(power*M^2))^((2:ℝ)/3)) ≤
          Ka*(Real.log Q.data.N)*X ∧
      Q.lam*M*(3/(power*M^2)) ≤ Kb*(Real.log Q.data.N)*X ∧
      Q.lam*M*diam^2 ≤ Kc*(Real.log Q.data.N)*X ∧
      Q.lam*M*rev ≤ Kr*(Real.log Q.data.N)*X ∧
      Q.lam*(18*(((q^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*cut) ≤
          Kz*(Real.log Q.data.N)^5*X) :
    Q.lam*Q.eq7InnerLowExactBudget ell q Lside cut j ≤
      (Cbin*(Ka+Kb+Kc+Kr)+Kz)*
        (Real.log Q.data.N)^5*Q.data.N^(2*delta+eps)*Q.data.E := by
  let v := Q.eq7InnerDyadMass j.val.val
  let M := 16*v
  let y := Q.xs+Q.eq7InnerDyadRight j.val.val
  let zg := Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)
  let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
  let F := nativeBinScaleLoss Lside
    (216*16^2*(Real.log Q.data.N)^2)
    (108*16^2*(Real.log Q.data.N)^2) M Q.data.s
  let diam := Q.localCapDiameter v 16+Q.data.rmin
  let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  let a := 2*((q^2*y)/(power*M^2))^((2:ℝ)/3)
  let b := 3/(power*M^2)
  let c := diam^2
  let r := rev
  let z := 18*(((q^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*cut
  let X := Q.data.N^(2*delta+eps)*Q.data.E
  have hX : 0 ≤ X := by
    have hN := Q.data.hN
    have hE := Q.data.hE
    dsimp [X]
    positivity
  obtain ⟨hF0,hF⟩ := hscale
  obtain ⟨ha,hb,hc,hr,hz⟩ := hcomponents
  have H := comparison_eq7_ordinary_literal_components_draft
    hlog hX hF0 hCbin hKa hKb hKc hKr hKz hF ha hb hc hr hz
  change Q.lam*(F*M*(a+b+c+r)+z) ≤
    (Cbin*(Ka+Kb+Kc+Kr)+Kz)*(Real.log Q.data.N)^5*
      Q.data.N^(2*delta+eps)*Q.data.E
  simpa only [X,F,M,a,b,c,r,z,v,y,zg,power,diam,rev,mul_assoc] using H

theorem eq7_inner_post_exact_rate_of_components_draft
    {h : ℝ} (j : Eq7InnerPostDyad Q h)
    (ell : ℕ) (q Lside cut eps Cbin Ka Kb Kc Kr Kz : ℝ)
    (hlog : 1 ≤ Real.log Q.data.N)
    (hCbin : 0 ≤ Cbin)
    (hKa : 0 ≤ Ka) (hKb : 0 ≤ Kb) (hKc : 0 ≤ Kc)
    (hKr : 0 ≤ Kr) (hKz : 0 ≤ Kz)
    (hscale :
      let v := Q.eq7InnerDyadMass j.val.val
      let M := 16*v
      let F := nativeBinScaleLoss Lside
        (108*16^2*(Real.log Q.data.N)^2)
        (54*16^2*(Real.log Q.data.N)^2) M
        (Q.eq7InnerWallStart j.val.val)
      0 ≤ F ∧ F ≤ Cbin*(Real.log Q.data.N)^4)
    (hcomponents :
      let v := Q.eq7InnerDyadMass j.val.val
      let M := 16*v
      let y := Q.xs+Q.eq7InnerDyadRight j.val.val
      let zg := Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)
      let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
      let diam := Q.localCapDiameter v 16
      let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
      let X := Q.data.N^(2*delta+eps)*Q.data.E
      Q.lam*M*(2*((q^2*y)/(power*M^2))^((2:ℝ)/3)) ≤
          Ka*(Real.log Q.data.N)*X ∧
      Q.lam*M*(3/(power*M^2)) ≤ Kb*(Real.log Q.data.N)*X ∧
      Q.lam*M*diam^2 ≤ Kc*(Real.log Q.data.N)*X ∧
      Q.lam*M*rev ≤ Kr*(Real.log Q.data.N)*X ∧
      Q.lam*(18*(((q^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*cut) ≤
          Kz*(Real.log Q.data.N)^5*X) :
    Q.lam*Q.eq7InnerPostExactBudget ell q Lside cut j ≤
      (Cbin*(Ka+Kb+Kc+Kr)+Kz)*
        (Real.log Q.data.N)^5*Q.data.N^(2*delta+eps)*Q.data.E := by
  let v := Q.eq7InnerDyadMass j.val.val
  let M := 16*v
  let y := Q.xs+Q.eq7InnerDyadRight j.val.val
  let zg := Q.shiftedNativeModel.R (Q.eq7InnerDyadRight j.val.val)
  let power := Q.data.N*laplaceComparisonStrength Q.data.d Q.lam zg
  let F := nativeBinScaleLoss Lside
    (108*16^2*(Real.log Q.data.N)^2)
    (54*16^2*(Real.log Q.data.N)^2) M
    (Q.eq7InnerWallStart j.val.val)
  let diam := Q.localCapDiameter v 16
  let rev := diam^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  let a := 2*((q^2*y)/(power*M^2))^((2:ℝ)/3)
  let b := 3/(power*M^2)
  let c := diam^2
  let r := rev
  let z := 18*(((q^2*y)^2*power*M^2)^((1:ℝ)/3)+2)*cut
  let X := Q.data.N^(2*delta+eps)*Q.data.E
  have hX : 0 ≤ X := by
    have hN := Q.data.hN
    have hE := Q.data.hE
    dsimp [X]
    positivity
  obtain ⟨hF0,hF⟩ := hscale
  obtain ⟨ha,hb,hc,hr,hz⟩ := hcomponents
  have H := comparison_eq7_ordinary_literal_components_draft
    hlog hX hF0 hCbin hKa hKb hKc hKr hKz hF ha hb hc hr hz
  change Q.lam*(F*M*(a+b+c+r)+z) ≤
    (Cbin*(Ka+Kb+Kc+Kr)+Kz)*(Real.log Q.data.N)^5*
      Q.data.N^(2*delta+eps)*Q.data.E
  simpa only [X,F,M,a,b,c,r,z,v,y,zg,power,diam,rev,mul_assoc] using H

theorem eq7_inner_broad_exact_rate_of_components_draft
    {P : Q.Potential} {ι : Type*}
    (c : ι → ShiftedCapInterval Q P) {h : ℝ}
    (b : Eq7InnerRelevantBroadSlice c h)
    (ell : ℕ) (q Lside cut eps Ks Kd Kr Kc Kz : ℝ)
    (hlog : 1 ≤ Real.log Q.data.N)
    (hKs : 0 ≤ Ks) (hKd : 0 ≤ Kd)
    (hKr : 0 ≤ Kr) (hKc : 0 ≤ Kc) (hKz : 0 ≤ Kz)
    (hcomponents :
      let v := (eq7InnerBroadSampler c b.val.1).scale b.val.2
      let width := ∫r in eq7InnerBroadSlice c b.val,
        deriv Q.alpha.val.val r
      let loss := (32:ℝ)^2+
        Q.criticalBroadTraceLoss 4 v (min (4*v) 1)+1
      let power := Q.criticalBroadMassPower v
      let diam := Q.criticalBroadMassDiameter
      let rev := Q.criticalBroadMassReverse ell q v
      let X := Q.data.N^(2*delta+eps)*Q.data.E
      Q.lam*(48*(108*loss*(Real.log Q.data.N)^2/
        (power*(v/4))*Real.log (width/cut))) ≤
          Ks*(Real.log Q.data.N)^5*X ∧
      Q.lam*((76+64*Lside)*width*diam^2) ≤
          Kd*(Real.log Q.data.N)^5*X ∧
      Q.lam*(32*width*rev) ≤
          Kr*(Real.log Q.data.N)^5*X ∧
      Q.lam*((66+64*Lside+65536*(1+Lside)^2)*
        (54*loss*(Real.log Q.data.N)^2*width/
          (power*(v/4)^2))) ≤
          Kc*(Real.log Q.data.N)^5*X ∧
      Q.lam*(16*cut) ≤ Kz*(Real.log Q.data.N)^5*X) :
    Q.lam*eq7InnerBroadExactBudget c ell q Lside cut b ≤
      (Ks+Kd+Kr+Kc+Kz)*(Real.log Q.data.N)^5*
        Q.data.N^(2*delta+eps)*Q.data.E := by
  let v := (eq7InnerBroadSampler c b.val.1).scale b.val.2
  let width := ∫r in eq7InnerBroadSlice c b.val,
    deriv Q.alpha.val.val r
  let loss := (32:ℝ)^2+
    Q.criticalBroadTraceLoss 4 v (min (4*v) 1)+1
  let power := Q.criticalBroadMassPower v
  let diam := Q.criticalBroadMassDiameter
  let rev := Q.criticalBroadMassReverse ell q v
  let side := 48*(108*loss*(Real.log Q.data.N)^2/
    (power*(v/4))*Real.log (width/cut))
  let diameter := (76+64*Lside)*width*diam^2
  let reverse := 32*width*rev
  let covariance := (66+64*Lside+65536*(1+Lside)^2)*
    (54*loss*(Real.log Q.data.N)^2*width/(power*(v/4)^2))
  let cutoff := 16*cut
  let X := Q.data.N^(2*delta+eps)*Q.data.E
  have hX : 0 ≤ X := by
    have hN := Q.data.hN
    have hE := Q.data.hE
    dsimp [X]
    positivity
  obtain ⟨hs,hd,hr,hc,hz⟩ := hcomponents
  have H := comparison_eq7_broad_literal_components_draft
    hlog hX hKs hKd hKr hKc hKz hs hd hr hc hz
  convert H using 1 <;>
    dsimp only [eq7InnerBroadExactBudget,criticalBroadMassBudget,
      nativeConditionalLedgerBudget,side,diameter,reverse,covariance,cutoff,
      X,v,width,loss,power,diam,rev] <;> ring

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
