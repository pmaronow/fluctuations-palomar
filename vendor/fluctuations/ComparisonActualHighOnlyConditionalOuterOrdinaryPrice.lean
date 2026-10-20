module

public import ComparisonActualHighOnlyConditionalOuterGeometry
public import ComparisonPhysicalLedgerAbsorption
public import ComparisonPhysicalCutoffCost

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

theorem eventually_actual_conditional_outer_ordinary_price_high_only
    (ell : ℕ) (hell : 2 < ell) (Q : ℝ) (hQ : 1 ≤ Q)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0)
    (horder : (delta+2)/((ell:ℝ)-1) ≤ delta) :
    ∀ᶠn : ℕ in atTop,∀a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.d ≤ 1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1 ≤ a.data.N → ∀v : ℝ,0 < v → v ≤ 1 → a.data.U ≤ v → a.data.s < v/2 →
      a.xs ≤ v → 4*cu*Az*a.xs ≤ v →
      3*laplaceComparisonStrength a.data.d a.lam (a.R (v/2))*
        a.canonicalOrdinaryMassBudgetAtDiameter ell Q (10*Real.log a.data.N) (a.data.N^(-(10:ℝ))) v
          (a.canonicalLocalMassDiameter v)+
      16*laplaceComparisonStrength a.data.d a.lam (a.R (v/2))*(a.canonicalLocalMassDiameter v)^2*(16*v) ≤
        a.data.N^(4*delta)*a.data.E := by
  let K := 32*cu/cl
  let J0 : ℝ := 9*32*32
  let L0 := 64*cu
  let Fcoef := nativeBinScalePolynomial (108*32^2) (54*32^2) 10 64
  have hK : 0 ≤ K := by dsimp [K];positivity
  have hJ0 : 0 ≤ J0 := by norm_num [J0]
  have hL0 : 0 ≤ L0 := by dsimp [L0];positivity
  have hsR : Tendsto (fun n:ℕ=>((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hbin := hsR.eventually (comparison_log_loss_eventually (C:=Fcoef) (p:=4)
    (nativeBinScalePolynomial_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hdelta)
  have Hlog := hsR.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  have Hcore := hsR.eventually (comparison_outer_error_core_eventually (Q:=Q) hdelta hm.le
    (show 0 < 1/C0 by positivity) (by norm_num : (0:ℝ) ≤ 2) hK hJ0 hL0)
  have Hcut := hsR.eventually (comparison_ordinary_cutoff_eventually (Q:=Q) (P0:=1) (V0:=16)
    (by norm_num) (by norm_num) (by norm_num : (3:ℝ) ≤ 10))
  have Htwo := hsR.eventually (comparison_log_loss_eventually (C:=2) (p:=0) (by norm_num) hdelta)
  filter_upwards [Hbin,Hlog,Hcore,Hcut,Htwo,eventually_actual_minimum_physical_scalar_data_high_only hm hC0]
    with n hnBin hnLog hnCore hnCut hnTwo hnScalar
  intro a hd1 hxs hyN v hv hv1 hUv hs hvxs houter
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
  let q := v/2+a.data.U
  let Dm := a.canonicalLocalMassDiameter v
  let Jcap := 9*Real.log a.data.N*32
  let J := J0*Real.log a.data.N
  let L := L0*Real.log a.data.N
  let F := nativeBinScaleLoss (10*Real.log a.data.N) (108*32^2*(Real.log a.data.N)^2)
    (54*32^2*(Real.log a.data.N)^2) (16*v) (v/4)
  have hP : 0 < P := a.canonical_mass_power_pos v
  have hY : 0 < Y := by dsimp [Y,canonicalMassHeight];positivity
  have hgs : 0 < gs := laplaceComparisonStrength_pos a.data.d a.hlam _
  have hq : 0 < q := by dsimp [q];have hU:=a.data.hU;positivity
  have hJcap : 0 < Jcap := by dsimp [Jcap];positivity
  have hJ : 0 ≤ J := by dsimp [J];positivity
  have hL : 0 ≤ L := by dsimp [L,L0];positivity
  have hD : 0 < Dm := by dsimp [Dm,canonicalLocalMassDiameter];positivity
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
  have hroom : a.data.E ≤ a.data.N^delta*a.data.d^3*q^2 := by
    have H := comparison_conditional_outer_room hN hdelta.le hE hd a.hlam a.hld hscalar.2.2.2.2.2.2.2.2
    rw [←hxs] at H
    have hqxs : a.xs/2 ≤ q := by dsimp [q];have hU:=a.data.hU;linarith
    exact H.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hqxs 2) (by positivity))
  have hDformula : Dm=Jcap*a.data.N^(-delta)*a.data.E/(a.data.d^3*q) := by
    dsimp [Dm,canonicalLocalMassDiameter,Jcap,q]
    rw [Real.rpow_neg hNp.le]
    field_simp
  have hqBand : q ≤ 32*(16*v) := by dsimp [q];linarith
  have hBandq : 16*v ≤ 32*q := by dsimp [q];have hU:=a.data.hU;linarith
  have hglobal : Dm ≤ J*(16*v) := by
    rw [hDformula]
    apply (comparison_local_diameter_spatial_bound hNp hd hq hJcap.le hroom).trans
    have H := mul_le_mul_of_nonneg_left hqBand hJcap.le
    convert H using 1 <;> dsimp [J,J0,Jcap] <;> ring
  have hlocal : Dm ≤ J*a.data.N^(-delta)*a.data.E/(a.data.d^3*(16*v)) := by
    rw [hDformula]
    apply (div_le_div_iff₀ (mul_pos (pow_pos hd 3) hq) (by positivity : 0 < a.data.d^3*(16*v))).mpr
    have H := mul_le_mul_of_nonneg_left hBandq (show 0 ≤ Jcap*a.data.N^(-delta)*a.data.E*a.data.d^3 by positivity)
    dsimp [J,J0,Jcap] at H ⊢
    nlinarith only [H]
  have hfactor : a.data.d^3*q ≤ Jcap := by
    have hd3 : a.data.d^3 ≤ 1 := pow_le_one₀ hd.le hd1
    have hqmax : q ≤ 3/2 := by dsimp [q];linarith
    have H := mul_le_mul_of_nonneg_right hd3 hq.le
    dsimp [Jcap]
    nlinarith only [H,hqmax,hnLog]
  have hratio : Y/Dm ≤ a.data.N^(delta+2) := by
    have H := comparison_local_diameter_reverse_ratio (delta:=delta) hN hd hE hq hscalar.2.2.2.2.1 hfactor hY.le hY_N
    rw [←hDformula] at H
    exact H
  have hprice := comparison_outer_ledger_physical_cost hell hN (show 0 < 1/C0 by positivity) hE hd hlower
    hP hgs (show comparisonSmallMass a.data.N a.data.E ≤ 16*v by change a.data.U ≤ 16*v;linarith)
    hY (by norm_num : (0:ℝ) ≤ 2) hK hQ hYbound hStrength hL hMass hD hJ hJ hglobal hlocal hratio horder
  have hF : 0 ≤ F := by dsimp [F,nativeBinScaleLoss];positivity
  have hFpoly : F ≤ Fcoef*(Real.log a.data.N)^4 := by
    apply nativeBinScaleLoss_le_log_polynomial hnLog (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
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
  have hFull : 3*gs*a.canonicalOrdinaryMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v Dm+16*gs*Dm^2*(16*v) ≤ (3*F+16)*core+a.data.E := by
    unfold canonicalOrdinaryMassBudgetAtDiameter canonicalMassReverseAtDiameter
    dsimp only [comparisonReverseMoment,P,Y,F,core] at Hledger hCut hDcost ⊢
    nlinarith only [Hledger,hCut,hDcost]
  have hCore0 : (3*F+16)*core ≤ a.data.N^(3*delta)*a.data.E := hCore
  have hFullCore : 3*gs*a.canonicalOrdinaryMassBudgetAtDiameter ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v Dm+16*gs*Dm^2*(16*v) ≤ a.data.N^(3*delta)*a.data.E+a.data.E :=
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
