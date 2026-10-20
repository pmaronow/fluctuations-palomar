module

public import ComparisonActualHighOnlyConditionalOuterGeometry
public import ComparisonPhysicalLedgerAbsorption
public import ComparisonPhysicalCutoffCost
public import ComparisonNativeOuterBroadPhysicalGeometry

@[expose] public section
noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 9000000
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem eventually_actual_conditional_outer_broad_price_high_only
    (ell : ℕ) (hell : 2 < ell) (Q : ℝ) (hQ : 1 ≤ Q)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (horder : (delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn : ℕ in atTop,∀a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀v : ℝ,0 < v → v ≤ 1 → a.data.U ≤ v → a.data.s < v/2 →
      a.xs ≤ v → 4*cu*Az*a.xs ≤ v → a.cavityCapTravel ≤ a.xs →
      ∀width : ℝ,0 ≤ width → width ≤ 4*v → width ≤ 1 →
      3*laplaceComparisonStrength a.data.d a.lam (a.R (v/2))*
        a.canonicalComparableBroadMassBudgetAtDiameter ell Q (10*Real.log a.data.N) (a.data.N^(-(10:ℝ))) v width
          (a.canonicalOuterBroadMassDiameter v)+
      16*laplaceComparisonStrength a.data.d a.lam (a.R (v/2))*(a.canonicalOuterBroadMassDiameter v)^2*width ≤
        a.data.N^(4*delta)*a.data.E := by
  let K := 32*cu/cl
  let Cdiam := 32*cu^3/cl^3
  let J0 : ℝ := max 9 (16*9*Cdiam)
  let L0 := 64*cu
  let loss := nativeOuterComparableTraceConstant cl cu
  have hloss : 0 ≤ loss := native_outer_comparable_trace_constant_nonneg hcl hcu
  let Fcoef := nativeBinScalePolynomial (108*loss) (54*loss) 10 64
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hCd : 0 < Cdiam := by dsimp [Cdiam];positivity
  have hJ0 : 0 ≤ J0 := (by norm_num : (0:ℝ) ≤ 9).trans (le_max_left _ _)
  have hL0 : 0 ≤ L0 := by dsimp [L0];positivity
  have hsR : Tendsto (fun n:ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hbin := hsR.eventually (comparison_log_loss_eventually (C:=Fcoef) (p:=4)
    (nativeBinScalePolynomial_nonneg (by positivity) (by positivity) (by norm_num) (by norm_num)) hdelta)
  have Hlog := hsR.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  have Hcore := hsR.eventually (comparison_outer_error_core_eventually (Q:=Q) hdelta hm.le
    (show 0 < 1/C0 by positivity) (by norm_num : (0:ℝ) ≤ 2) hK hJ0 hL0)
  have Hcut := hsR.eventually (comparison_ordinary_cutoff_eventually (Q:=Q) (P0:=1) (V0:=16)
    (by norm_num) (by norm_num) (by norm_num : (3:ℝ) ≤ 10))
  have Htwo := hsR.eventually (comparison_log_loss_eventually (C:=2) (p:=0) (by norm_num) hdelta)
  filter_upwards [Hbin,Hlog,Hcore,Hcut,Htwo,eventually_actual_minimum_physical_scalar_data_high_only hm hC0]
    with n hnBin hnLog hnCore hnCut hnTwo hnScalar
  intro a hd1 hxs hyN v hv hv1 hUv hs hvxs houter htravel width hw hwidth hwidth1
  have hscalar := hnScalar a hd1
  have hN : 1 ≤ a.data.N := by exact_mod_cast Nat.succ_pos n
  have hNp := a.data.hN
  have hE := a.data.hE
  have hd := a.data.hd
  have hxs0 := a.hxs
  have hU0 := a.data.hU
  have hlog : 0 < Real.log a.data.N := by linarith
  let P := a.canonicalMassPower v
  let Y := a.canonicalMassHeight v
  let gs := laplaceComparisonStrength a.data.d a.lam (a.R (v/2))
  let q := v
  let Dm := a.canonicalOuterBroadMassDiameter v
  let Jcap := 9*Real.log a.data.N*Cdiam
  let J := J0*Real.log a.data.N
  let L := L0*Real.log a.data.N
  let F := nativeBinScaleLoss (10*Real.log a.data.N) (108*loss*(Real.log a.data.N)^2)
    (54*loss*(Real.log a.data.N)^2) (16*v) (v/4)
  have hP : 0 < P := a.canonical_mass_power_pos v
  have hY : 0 < Y := by dsimp [Y,canonicalMassHeight];positivity
  have hgs : 0 < gs := laplaceComparisonStrength_pos a.data.d a.hlam _
  have hq : 0 < q := by dsimp [q];have hU:=a.data.hU;positivity
  have hJcap : 0 < Jcap := by dsimp [Jcap];positivity
  have hJ : 0 ≤ J := by dsimp [J];positivity
  have hL : 0 ≤ L := by dsimp [L,L0];positivity
  have hTravel : 0 < a.cavityCapTravel := by
    have hLogU : 0 < Real.log ((1+a.data.U)/a.data.U) := Real.log_pos ((one_lt_div a.data.hU).mpr (by linarith))
    dsimp [cavityCapTravel]
    have HL:=a.data.hL
    positivity
  have hD : 0 < Dm := by
    dsimp [Dm,canonicalOuterBroadMassDiameter]
    exact mul_pos (by positivity) (lt_min hTravel (by positivity))
  have hYbound : Y ≤ 2*(16*v) := by dsimp [Y,canonicalMassHeight];linarith [min_le_left (16*v) 1]
  have hY_N : Y ≤ a.data.N := by dsimp [Y,canonicalMassHeight];linarith [min_le_right (16*v) 1]
  have hStrength : a.data.N*gs ≤ K*P := a.conditional_outer_strength_geometry_high_only hcl hcu hAz hv hv1 hs houter
  have Hgeom := a.conditional_outer_radius_geometry_high_only hcl hcu hAz hv hv1 hs houter
  have Hmass : 16*v ≤ (32*cu)*a.R (v/2) := by
    have H := (div_le_iff₀ (mul_pos (by norm_num) hcu)).mp Hgeom.1
    nlinarith only [H]
  have Hradius := laplaceComparisonStrength_radius_upper hN hnLog hd hscalar.2.2.1 a.hlam a.hld
    (a.shiftedNativeModel.R_bounds (v/2))
  change laplaceComparisonStrength a.data.d a.lam (a.R (v/2))*a.R (v/2) ≤ 2*a.data.d^3*Real.log a.data.N at Hradius
  have hMass : gs*(16*v) ≤ a.data.d^3*L := by
    have H := mul_le_mul_of_nonneg_left Hmass hgs.le
    have HR := mul_le_mul_of_nonneg_left Hradius (show 0 ≤ 32*cu by positivity)
    dsimp only [gs,L,L0]
    dsimp only [gs] at H
    nlinarith only [H,HR]
  have hlower : (1/C0)*a.data.N^(-(2:ℝ)/3+m)*a.data.d ≤ a.data.E := by
    have H := mul_le_mul_of_nonneg_left a.hlower (show 0 ≤ 1/C0 by positivity)
    simpa only [←mul_assoc,one_div_mul_cancel hC0.ne',one_mul] using H
  let D0 := 9*Real.log a.data.N*a.cavityCapTravel
  let Dl := Jcap*a.data.N^(-delta)*a.data.E/(a.data.d^3*v)
  have hDformula : Dm=min D0 Dl := by
    dsimp [Dm,canonicalOuterBroadMassDiameter,D0,Dl,Jcap]
    rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ 9*Real.log a.data.N),Real.rpow_neg hNp.le]
    congr 1
    dsimp [Cdiam]
    field_simp
  have hD0 : Dm ≤ D0 := hDformula.trans_le (min_le_left _ _)
  have hDl : Dm ≤ Dl := hDformula.trans_le (min_le_right _ _)
  have hglobal : Dm ≤ J*(16*v) := by
    have H:=mul_le_mul_of_nonneg_left (htravel.trans hvxs) (by positivity : 0 ≤ 9*Real.log a.data.N)
    have HJ:=mul_le_mul_of_nonneg_right (le_max_left 9 (16*9*Cdiam))
      (show 0 ≤ Real.log a.data.N*v by positivity)
    dsimp only [D0] at hD0
    dsimp only [D0,J,J0] at H HJ ⊢
    have H9 : 9*Real.log a.data.N*v ≤ J*v := by
      dsimp [J,J0]
      nlinarith only [HJ]
    have Hgrow : J*v ≤ J*(16*v) := mul_le_mul_of_nonneg_left (by linarith) hJ
    exact hD0.trans (H.trans (H9.trans Hgrow))
  have hlocal : Dm ≤ J*a.data.N^(-delta)*a.data.E/(a.data.d^3*(16*v)) := by
    apply hDl.trans
    apply (div_le_div_iff₀ (mul_pos (pow_pos hd 3) hv) (by positivity : 0 < a.data.d^3*(16*v))).mpr
    have H:=mul_le_mul_of_nonneg_right (le_max_right 9 (16*9*Cdiam))
      (show 0 ≤ Real.log a.data.N*a.data.N^(-delta)*a.data.E*a.data.d^3*v by positivity)
    dsimp [Dl,Jcap,J,J0]
    nlinarith only [H]
  have hclcu : cl ≤ cu := by
    have H:=a.regular 1 ⟨a.hz.2,le_rfl⟩
    linarith
  have hCd32 : 32 ≤ Cdiam := by
    have H:=pow_le_pow_left₀ hcl.le hclcu 3
    apply (le_div_iff₀ (pow_pos hcl 3)).mpr
    nlinarith only [H]
  have hfactor : a.data.d^3*v ≤ Jcap := by
    have H:=mul_le_mul_of_nonneg_right (pow_le_one₀ hd.le hd1 : a.data.d^3 ≤ 1) hv.le
    have HJ:=mul_le_mul hnLog hCd32 (by norm_num : (0:ℝ) ≤ 32) hlog.le
    dsimp [Jcap]
    nlinarith only [H,HJ,hv1]
  have hr0 := comparison_physical_reverse_ratio (delta:=delta) hN hnLog a.data.hU hscalar.2.2.2.2.1
    hscalar.2.2.2.2.2.2.2.1 hY.le hY_N
  change Y/D0 ≤ a.data.N^(delta+2) at hr0
  have hrl := comparison_local_diameter_reverse_ratio (delta:=delta) hN hd hE hv hscalar.2.2.2.2.1 hfactor hY.le hY_N
  change Y/Dl ≤ a.data.N^(delta+2) at hrl
  have hratio : Y/Dm ≤ a.data.N^(delta+2) := by
    apply (div_le_iff₀ hD).mpr
    rw [hDformula,mul_min_of_nonneg _ _ (Real.rpow_pos_of_pos hNp _).le]
    exact le_min ((div_le_iff₀ (by dsimp [D0];positivity : 0 < D0)).mp hr0)
      ((div_le_iff₀ (by dsimp [Dl];positivity : 0 < Dl)).mp hrl)
  have hprice := comparison_outer_ledger_physical_cost hell hN (show 0 < 1/C0 by positivity) hE hd hlower
    hP hgs (show comparisonSmallMass a.data.N a.data.E ≤ 16*v by change a.data.U ≤ 16*v;linarith)
    hY (by norm_num : (0:ℝ) ≤ 2) hK hQ hYbound hStrength hL hMass hD hJ hJ hglobal hlocal hratio horder
  have hF : 0 ≤ F := by dsimp [F,nativeBinScaleLoss];positivity
  have hFpoly : F ≤ Fcoef*(Real.log a.data.N)^4 := by
    apply nativeBinScaleLoss_le_log_polynomial hnLog (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by positivity) (by positivity) (by norm_num) (by norm_num)
      le_rfl le_rfl le_rfl
    field_simp
    norm_num
  have hFpow : F ≤ a.data.N^delta := hFpoly.trans (by simpa only [Real.rpow_natCast,Real.rpow_ofNat] using hnBin)
  let core := comparisonOuterPhysicalCore a.data.N delta m (1/C0) a.data.E Q 2 K J J L delta
  have hDcost : gs*(16*v)*Dm^2 ≤ core := by
    have Hnonneg : 0 ≤ 2*((Q^2*Y)/(P*(16*v)^2))^((2:ℝ)/3)+3/(P*(16*v)^2)+comparisonReverseMoment ell Dm Q Y := by
      unfold comparisonReverseMoment
      positivity
    have H := mul_nonneg (mul_pos hgs (by positivity : 0 < 16*v)).le Hnonneg
    dsimp only [core] at ⊢
    nlinarith only [hprice,H]
  have hCore := hnCore a.data.E F delta hE.le hF hFpow le_rfl
  have hgs1 : gs ≤ 1 := (laplaceComparisonStrength_le a.data.d a.hlam.le _).trans (by nlinarith [a.hld])
  have hPN : P ≤ a.data.N := by
    have H : laplaceComparisonStrength a.data.d a.lam (a.R (min (16*v) 1)) ≤ 1 :=
      (laplaceComparisonStrength_le a.data.d a.hlam.le _).trans (by nlinarith [a.hld])
    exact (mul_le_mul_of_nonneg_left H hNp.le).trans_eq (mul_one _)
  have hCut := hnCut P Y (16*v) gs a.data.E hP.le (by simpa only [one_mul] using hPN) hY.le hY_N
    (by positivity) (by linarith) hgs.le hgs1 hscalar.2.1
  have Hledger := mul_le_mul_of_nonneg_left hprice (show 0 ≤ 3*F by positivity)
  let Lside := 10*Real.log a.data.N
  let AS := 108*loss*(Real.log a.data.N)^2
  let AC := 54*loss*(Real.log a.data.N)^2
  let Rm := a.canonicalMassReverseAtDiameter ell Q v Dm
  let B := 16*v
  let rho := v/4
  let cut := a.data.N^(-(10:ℝ))
  have hLside : 0 ≤ Lside := by dsimp [Lside];positivity
  have hAS : 0 ≤ AS := by dsimp [AS];positivity
  have hAC : 0 ≤ AC := by dsimp [AC];positivity
  have hB : 0 < B := by dsimp [B];positivity
  have hrho : 0 < rho := by dsimp [rho];positivity
  have hRm : 0 ≤ Rm := by dsimp [Rm,canonicalMassReverseAtDiameter];positivity
  have hwidthB : width ≤ B := by dsimp [B];linarith
  have hlogside : Real.log (width/cut) ≤ Lside := by
    by_cases hp : 0 < width
    · exact (comparison_broad_side_log_le hp hwidth1 (Real.rpow_pos_of_pos hNp _)
        (comparison_physical_cutoff_log (C:=10) hNp).2.le).trans_eq rfl
    · have hz : width=0 := le_antisymm (le_of_not_gt hp) hw
      simp only [hz,zero_div,Real.log_zero]
      exact hLside
  have hV : AS/(P*rho)*Real.log (width/cut) ≤ AS*Lside/(P*rho) := by
    have H:=mul_le_mul_of_nonneg_left hlogside (div_nonneg hAS (mul_nonneg hP.le hrho.le))
    simpa only [div_mul_eq_mul_div] using H
  have hT : AC*width/(P*rho^2) ≤ AC*B/(P*rho^2) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hwidthB hAC) (by positivity)
  have hDiam := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwidthB (show 0 ≤ 76+64*Lside by positivity)) (sq_nonneg Dm)
  have hRev := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hwidthB (by norm_num : (0:ℝ) ≤ 32)) hRm
  have hVmul := mul_le_mul_of_nonneg_left hV (by norm_num : (0:ℝ) ≤ 48)
  have hTmul := mul_le_mul_of_nonneg_left hT (show 0 ≤ 66+64*Lside+65536*(1+Lside)^2 by positivity)
  have hDom : a.canonicalComparableBroadMassBudgetAtDiameter ell Q Lside cut v width Dm ≤
      nativeConditionalLedgerBudget 1 B cut Dm (AS*Lside/(P*rho)) (AC*B/(P*rho^2)) Rm Lside := by
    unfold canonicalComparableBroadMassBudgetAtDiameter nativeConditionalLedgerBudget
    dsimp only [AS,AC,P,rho,Rm,loss] at hVmul hTmul hDiam hRev ⊢
    norm_num only [Nat.cast_one,mul_one]
    nlinarith only [hVmul,hTmul,hDiam,hRev]
  have hBin := nativeConditionalLedgerBudget_le_bin_scale (Q:=0) (y:=0) (k:=1)
    hLside hAS hAC hB hrho hP hD.le (by norm_num) (by norm_num) hRm (by norm_num) cut
  norm_num only [Nat.cast_one,zero_pow,zero_mul,zero_div,zero_add,div_one,one_mul,mul_one] at hBin
  have hNoise : Dm^2+2/(P*B^2)+Rm ≤
      2*((Q^2*Y)/(P*B^2))^((2:ℝ)/3)+3/(P*B^2)+Dm^2+Rm := by
    have H0 : 0 ≤ ((Q^2*Y)/(P*B^2))^((2:ℝ)/3) := by positivity
    have H1 : 0 ≤ 1/(P*B^2) := by positivity
    have H12 : 2/(P*B^2) ≤ 3/(P*B^2) := div_le_div_of_nonneg_right (by norm_num) (by positivity)
    linarith only [H0,H12]
  have hBinNoise := mul_le_mul_of_nonneg_left hNoise (show 0 ≤ F*B by positivity)
  change _ ≤ F*B*(Dm^2+2/(P*B^2)+Rm)+16*cut at hBin
  have hBudget := hDom.trans (hBin.trans (add_le_add hBinNoise le_rfl))
  have hBudgetPrice := mul_le_mul_of_nonneg_left hBudget (show 0 ≤ 3*gs by positivity)
  have hSmallCut : 48*gs*cut ≤ a.data.E := by
    have H0 : 0 ≤ ((Q^2*Y)^2*P*B^2)^((1:ℝ)/3) := by positivity
    have H1 : 0 ≤ gs*cut := by positivity
    dsimp only [cut,B] at H1 H0 ⊢
    nlinarith only [hCut,H0,H1]
  have hDcostWidth : gs*width*Dm^2 ≤ core := by
    have H:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwidthB hgs.le) (sq_nonneg Dm)
    exact H.trans (by dsimp [B];nlinarith only [hDcost])
  have hFull : 3*gs*a.canonicalComparableBroadMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v width Dm+16*gs*Dm^2*width ≤ (3*F+16)*core+a.data.E := by
    dsimp only [Rm,canonicalMassReverseAtDiameter,comparisonReverseMoment,Lside,cut,B] at hBudgetPrice
    dsimp only [comparisonReverseMoment,P,Y,F,core] at Hledger hBudgetPrice hSmallCut hDcostWidth ⊢
    nlinarith only [Hledger,hBudgetPrice,hSmallCut,hDcostWidth]
  have hCore0 : (3*F+16)*core ≤ a.data.N^(3*delta)*a.data.E := hCore
  have hFullCore : 3*gs*a.canonicalComparableBroadMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v width Dm+16*gs*Dm^2*width ≤ a.data.N^(3*delta)*a.data.E+a.data.E :=
    hFull.trans (by linarith only [hCore0])
  simp only [Real.rpow_zero,mul_one] at hnTwo
  have Hlast := mul_le_mul_of_nonneg_right hnTwo (show 0 ≤ a.data.N^(3*delta)*a.data.E by positivity)
  have Heq : a.data.N^delta*(a.data.N^(3*delta)*a.data.E)=a.data.N^(4*delta)*a.data.E := by
    rw [←mul_assoc,←Real.rpow_add hNp]
    congr 2
    ring
  rw [Heq] at Hlast
  have hraise := mul_le_mul_of_nonneg_right (Real.one_le_rpow hN (show 0 ≤ 3*delta by linarith)) hE.le
  exact hFullCore.trans (by nlinarith only [Hlast,hraise])

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
