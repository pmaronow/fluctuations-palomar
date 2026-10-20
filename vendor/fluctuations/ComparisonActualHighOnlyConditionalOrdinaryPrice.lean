module

public import ComparisonActualHighOnlyConditionalDensityBasics
public import ComparisonActualHighOnlyMassBudgetScale
public import ComparisonNativeInnerStrengthDistortion
public import ComparisonNativeOrdinaryPhysicalRates

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option maxHeartbeats 24000000
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}

theorem canonical_conditional_inner_strength_high_only
    (a : ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (hdelta : 0≤delta) (hcl : 0 < cl) (hAz : 0≤Az) {Cv : ℝ} (hCv : 0≤Cv)
    (hxs : a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam)
    {v : ℝ} (hv : 0 < v) (hvA : v≤Cv*a.xs) :
    a.data.N*(a.data.N^(-delta)*a.lam)≤
      (max 1 ((Az+1/cl)*(1+16*Cv)))*a.canonicalMassPower v := by
  let K:=max 1 ((Az+1/cl)*(1+16*Cv))
  have hK:1≤K:=le_max_left _ _
  have hN:1≤a.data.N:=by exact_mod_cast Nat.succ_pos n
  have hmin:min (16*v) 1∈Icc (0:ℝ) 1:=⟨le_min (by positivity) zero_le_one,min_le_right _ _⟩
  have hR:0≤a.R (min (16*v) 1):=(a.shiftedNativeModel.R_bounds _).1
  by_cases hr:a.R (min (16*v) 1)=0
  · have hp:a.data.N^(-delta)≤1:=Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
    have H:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp a.hlam.le) a.data.hN.le
    have HK:=mul_le_mul_of_nonneg_right hK (mul_nonneg a.data.hN.le a.hlam.le)
    unfold canonicalMassPower
    rw [hr]
    have hg:laplaceComparisonStrength a.data.d a.lam 0=a.lam:=by
      norm_num [laplaceComparisonStrength,comparisonStrength,laplaceComparisonShape]
    rw [hg]
    nlinarith only [H,HK]
  · have hRpos:0 < a.R (min (16*v) 1):=lt_of_le_of_ne hR (Ne.symm hr)
    have HR:=a.inverse_radius_le_source_mass hcl hAz hmin
    have HX:a.xs+min (16*v) 1≤(1+16*Cv)*a.xs:=by linarith [min_le_left (16*v) 1]
    have HH:=mul_le_mul_of_nonneg_left HX (show 0≤Az+1/cl by positivity)
    have HK:=mul_le_mul_of_nonneg_right (le_max_right 1 ((Az+1/cl)*(1+16*Cv))) a.hxs.le
    have HRA:a.R (min (16*v) 1)≤K*comparisonConditionalScale a.data.N delta a.data.E a.lam:=by
      rw [←hxs]
      dsimp only [K]
      nlinarith only [HR,HH,HK]
    exact comparison_canonical_inner_strength hN hdelta a.data.hE a.data.hd a.hlam a.hld a.hupper hK hRpos HRA

theorem eventually_actual_conditional_ordinary_budget_price_high_only
    (ell : ℕ) (hell : 2 < ell) (Q Cv : ℝ) (hQ : 1≤Q) (hCv : 0≤Cv)
    (hm : 0 < m) (hdelta : 0 < delta) (hcl : 0 < cl) (hAz : 0≤Az) (hC0 : 0 < C0)
    (horder : (delta+2)/((ell:ℝ)-1)≤delta) :
    ∀ᶠn:ℕ in atTop,∀a:ActualHighOnlyOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      a.data.d≤1 → a.xs=comparisonConditionalScale a.data.N delta a.data.E a.lam →
      a.xs+1≤a.data.N → ∀v:ℝ,0 < v → v≤1 → a.data.U≤v → v≤Cv*a.xs →
      3*a.lam*a.canonicalOrdinaryMassBudget ell Q (10*Real.log a.data.N) (a.data.N^(-(10:ℝ))) v+
        16*a.lam*a.canonicalMassDiameter^2*(16*v)≤a.data.N^(7*delta)*a.data.E := by
  let K:=max 1 ((Az+1/cl)*(1+16*Cv))
  let C:=1+16*Cv
  let Fcoef:=nativeBinScalePolynomial (108*32^2) (54*32^2) 10 64
  have hK:1≤K:=le_max_left _ _
  have hC:0≤C:=by dsimp [C];positivity
  have hsR:Tendsto (fun n:ℕ=>((n+1:ℕ):ℝ)) atTop atTop:=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have Hbin:=hsR.eventually (comparison_log_loss_eventually (C:=Fcoef) (p:=4)
    (nativeBinScalePolynomial_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hdelta)
  have Hlog:=hsR.eventually (Real.tendsto_log_atTop.eventually_ge_atTop (1:ℝ))
  have HJ:=hsR.eventually (comparison_capLogFactor_eventually hdelta)
  have Hcore:=hsR.eventually (comparison_inner_error_core_eventually (Q:=Q) hdelta hC)
  have Hcut:=hsR.eventually (comparison_ordinary_cutoff_eventually (Q:=Q) (P0:=1) (V0:=16)
    (by norm_num) (by norm_num) (by norm_num : (3:ℝ)≤10))
  have HK:=hsR.eventually (comparison_log_loss_eventually (C:=K) (p:=0) (zero_le_one.trans hK) hdelta)
  have Htwo:=hsR.eventually (comparison_log_loss_eventually (C:=2) (p:=0) (by norm_num) hdelta)
  filter_upwards [Hbin,Hlog,HJ,Hcore,Hcut,HK,Htwo,
    eventually_actual_minimum_physical_scalar_data_high_only hm hC0] with n hnBin hnLog hnJ hnCore hnCut hnK hnTwo hnScalar
  intro a hd1 hxs hyN v hv hv1 hUv hvA
  have hscalar:=hnScalar a hd1
  have hxs0:=a.hxs
  have hU0:=a.data.hU
  have hL0:=a.data.hL
  have hE0:=a.data.hE
  have hlam0:=a.hlam
  have hN0:=a.data.hN
  have hlogPos:0 < Real.log a.data.N:=by linarith
  have hN:1≤a.data.N:=by exact_mod_cast Nat.succ_pos n
  let P:=a.canonicalMassPower v
  let Y:=a.canonicalMassHeight v
  let Dm:=a.canonicalMassDiameter
  let J:=9*Real.log a.data.N*Real.log ((1+a.data.U)/a.data.U)/a.data.N^delta
  let F:=nativeBinScaleLoss (10*Real.log a.data.N) (108*32^2*(Real.log a.data.N)^2)
    (54*32^2*(Real.log a.data.N)^2) (16*v) (v/4)
  have hP:0 < P:=a.canonical_mass_power_pos v
  have hY:0 < Y:=by dsimp [Y,canonicalMassHeight];positivity
  have hYbound:Y≤C*a.xs:=a.canonical_mass_height_le hCv hvA
  have hY_N:Y≤a.data.N:=by dsimp [Y,canonicalMassHeight];linarith [min_le_right (16*v) 1]
  have hV_A:16*v≤C*a.xs:=by dsimp [C];nlinarith only [hvA,a.hxs]
  have hJ:0≤J:=by
    have H:0≤Real.log ((1+a.data.U)/a.data.U):=Real.log_nonneg ((one_le_div a.data.hU).mpr (by linarith))
    dsimp [J];positivity
  have hJ1:J≤1:=hnJ a.data.U a.data.hU hscalar.2.2.2.2.1 hscalar.2.2.2.1
  have hD:0 < Dm:=by
    have H:0 < Real.log ((1+a.data.U)/a.data.U):=Real.log_pos ((one_lt_div a.data.hU).mpr (by linarith))
    dsimp [Dm,canonicalMassDiameter,cavityCapTravel];positivity
  have hDJ:Dm=J*a.data.L:=by dsimp [Dm,canonicalMassDiameter,cavityCapTravel,J];ring
  have hF:0≤F:=by dsimp [F,nativeBinScaleLoss];positivity
  have hFpoly:F≤Fcoef*(Real.log a.data.N)^4:=by
    apply nativeBinScaleLoss_le_log_polynomial hnLog (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      le_rfl le_rfl le_rfl
    field_simp
    norm_num
  have hFpow:F≤a.data.N^delta:=hFpoly.trans (by simpa only [Real.rpow_natCast,Real.rpow_ofNat] using hnBin)
  have hStrength:a.data.N*(a.data.N^(-delta)*a.lam)≤K*P:=
    a.canonical_conditional_inner_strength_high_only hdelta.le hcl hAz hCv hxs hv hvA
  have hratio:Y/Dm≤a.data.N^(delta+2):=comparison_physical_reverse_ratio hN hnLog a.data.hU
    hscalar.2.2.2.2.1 hscalar.2.2.2.2.2.2.2.1 hY.le hY_N
  have hprice:=comparison_inner_ledger_with_strength_distortion hell hN a.data.hE a.hlam hP hK hStrength
    (show comparisonSmallMass a.data.N a.data.E≤16*v by change a.data.U≤16*v;linarith)
    (hxs ▸ hV_A) hY (hxs ▸ hYbound) hD hQ hC hJ a.data.hL.le (min_le_left _ _)
    (hxs ▸ hscalar.2.2.2.2.2.1) hDJ.le hratio horder
  have hCore:=hnCore a.data.E F J delta a.data.hE.le hF hFpow hJ hJ1 le_rfl
  have hCoreK:=mul_le_mul_of_nonneg_left hCore (zero_le_one.trans hK)
  have hPN:P≤a.data.N:=by
    have H:laplaceComparisonStrength a.data.d a.lam (a.R (min (16*v) 1))≤1:=
      (laplaceComparisonStrength_le _ a.hlam.le _).trans (by nlinarith [a.hld,a.data.hd,hd1])
    exact (mul_le_mul_of_nonneg_left H a.data.hN.le).trans_eq (mul_one _)
  have hCut:=hnCut P Y (16*v) a.lam a.data.E hP.le (by simpa only [one_mul] using hPN) hY.le hY_N (by positivity)
    (by linarith) a.hlam.le (by nlinarith [a.hld,a.data.hd,hd1]) hscalar.2.1
  have hlength:=comparison_conditional_inner_length_cost a.data.hN a.data.hE a.hlam hC
    (by positivity : 0≤16*v) (hxs ▸ hV_A) a.data.hL.le (min_le_left _ _)
  have hLA:a.data.L≤a.xs:=(min_le_left _ _).trans hscalar.2.2.2.2.2.1
  have hDmSq:Dm^2≤J^2*a.xs*a.data.L:=by
    rw [hDJ]
    have H:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hLA a.data.hL.le) (sq_nonneg J)
    nlinarith only [H]
  have hSquare:a.lam*(16*v)*Dm^2≤J^2*C*a.data.N^(2*delta)*a.data.E:=by
    have H1:=mul_le_mul_of_nonneg_left hDmSq (show 0≤a.lam*(16*v) by positivity)
    have H2:=mul_le_mul_of_nonneg_left hlength (sq_nonneg J)
    rw [←hxs] at H2
    nlinarith only [H1,H2]
  have hSquareK:=mul_le_mul_of_nonneg_right hK
    (show 0≤16*J^2*C*a.data.N^(2*delta)*a.data.E by positivity)
  have hPriceF:=mul_le_mul_of_nonneg_left hprice (show 0≤3*F by positivity)
  have hFull:3*a.lam*a.canonicalOrdinaryMassBudget ell Q (10*Real.log a.data.N)
      (a.data.N^(-(10:ℝ))) v+16*a.lam*Dm^2*(16*v)≤K*a.data.N^(5*delta)*a.data.E+a.data.E:=by
    unfold canonicalOrdinaryMassBudget canonicalMassReverse
    dsimp only [P,Y,Dm,F,comparisonReverseMoment] at hPriceF hCut hSquare hCoreK hSquareK ⊢
    nlinarith only [hPriceF,hCut,hSquare,hCoreK,hSquareK]
  simp only [Real.rpow_zero,mul_one] at hnK hnTwo
  have hRaise:=mul_le_mul_of_nonneg_right hnK (show 0≤a.data.N^(5*delta)*a.data.E by positivity)
  have he6:a.data.N^delta*(a.data.N^(5*delta)*a.data.E)=a.data.N^(6*delta)*a.data.E:=by
    rw [←mul_assoc,←Real.rpow_add a.data.hN];congr 2;ring
  rw [he6] at hRaise
  have hlast:=mul_le_mul_of_nonneg_right hnTwo (show 0≤a.data.N^(6*delta)*a.data.E by positivity)
  have he7:a.data.N^delta*(a.data.N^(6*delta)*a.data.E)=a.data.N^(7*delta)*a.data.E:=by
    rw [←mul_assoc,←Real.rpow_add a.data.hN];congr 2;ring
  rw [he7] at hlast
  have hp6:1≤a.data.N^(6*delta):=Real.one_le_rpow hN (by linarith)
  have hEraise:=mul_le_mul_of_nonneg_right hp6 a.data.hE.le
  exact hFull.trans (by nlinarith only [hRaise,hlast,hEraise])

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
