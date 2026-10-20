module

public import ComparisonActualHighOnlySelectedThermalLedger
public import ComparisonActualHighOnlyCapEndpointLedger
public import ComparisonNativeBinScale
public import ComparisonNativeCavityConcentrationBareRadius

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def ordinaryOptimizedBudget
    (a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q K0 Lside cut bandMass rho y v K zg : ℝ) : ℝ:=
  let power:=a.data.N*(laplaceComparisonStrength a.data.d a.lam) zg
  let AS:=108*K0^2*(Real.log a.data.N)^2
  let AC:=54*K0^2*(Real.log a.data.N)^2
  let diameter:=a.localCapDiameter v K
  let reverse:=diameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  nativeBinScaleLoss Lside AS AC bandMass rho*bandMass*
    (2*((Q^2*y)/(power*bandMass^2))^((2:ℝ)/3)+3/(power*bandMass^2)+diameter^2+reverse)+
      18*(((Q^2*y)^2*power*bandMass^2)^((1:ℝ)/3)+2)*cut

end ActualHighOnlyOverlapMinimum

theorem eventually_actual_high_only_ordinary_optimized_budget
    (ell : ℕ) (hell : 2< ell) (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< margin) (hdelta : 0< delta) (hroom : delta<3*margin)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0 ≤ Az) (hC0 : 0< C0) (hCt : 0 ≤ Ct) :
    ∃Q : ℝ,1 ≤ Q ∧ ∀ᶠn : ℕ in atTop,
      ∀(a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
        (hs : a.data.s ≤ 1/4) (hsxs : a.data.s ≤ a.xs)
        (P : a.Potential) (ι : Type*) [Fintype ι] (c : ι→ActualHighOnlyOverlapMinimum.ShiftedCapInterval a P)
        (ag zg lo hi K0 bandMass rho y v K Lside cut : ℝ),
        (∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right) →
        (∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1)) →
        Pairwise (fun t u=> Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)) →
        (0:ℝ)< ag → ag ≤ zg → zg ≤ 1 →
        NativePullbackClockRegularity a.alpha.val.val a.b a.h ag zg →
        (∀t,ag ≤ (c t).left) → (∀t,(c t).right ≤ zg) →
        0 ≤ lo → 1 ≤ K0 →
        hi+comparisonSmallMass a.data.N a.data.E ≤ K0*(lo+comparisonSmallMass a.data.N a.data.E) →
        (∀t,lo ≤ a.alpha.val.val (c t).left) → (∀t,a.alpha.val.val (c t).right ≤ hi) →
        0< bandMass → a.alpha.val.val zg-a.alpha.val.val ag ≤ bandMass →
        0< rho → rho ≤ a.alpha.val.val ag → 0< y → a.xs+a.alpha.val.val zg ≤ y →
        0< v → 0< K →
        (∀t,v ≤ a.alpha.val.val (c t).left+comparisonSmallMass a.data.N a.data.E) →
        (∀t,a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ K*v) →
        0 ≤ Lside → 0< cut → Real.log (1/cut) ≤ Lside →
        (∫u in 0..1,(P.retainedSupport c ag zg).indicator (fun _=>1) (a.shiftedNativeModel.R u)*
          a.shiftedNativeModel.thermal u) ≤
          a.ordinaryOptimizedBudget ell Q K0 Lside cut bandMass rho y v K zg := by
  obtain ⟨Q,hQ,Hmaster⟩:=eventually_exists_actual_high_only_selected_master ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hdepth:=(tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  refine ⟨Q,hQ,?_⟩
  filter_upwards [Hmaster,Hdepth,Hlog] with n hnMaster hnDepth hnLog
  intro a hs hsxs P ι inst c ag zg lo hi K0 bandMass rho y v K Lside cut hwhole hcontacts hdisjoint
    hag hagz hzg hclock hleft hright hlo hK0 hband hamass hzmass hmass hmassSpan hrho hrhoFloor hy hY hv hK
    hsourceLeft hsourceSpan hLside hcut hlogcut
  have hN : 1 ≤ a.data.N:=by
    dsimp only [ActualHighOnlyComparisonData.N]
    exact_mod_cast Nat.succ_pos n
  have hlog : 1 ≤ Real.log a.data.N:=hnLog
  have hnd : 1/a.data.N ≤ a.data.d:=by
    have HD:=hnDepth a.data.E a.data.d a.data.hE a.data.hd a.hlower
    have HS : comparisonLowerScale (n+1:ℕ) a.data.E a.data.d ≤ a.data.d:=by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.data.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact HD.trans HS
  let power:=a.data.N*(laplaceComparisonStrength a.data.d a.lam) zg
  let AS:=108*K0^2*(Real.log a.data.N)^2
  let AC:=54*K0^2*(Real.log a.data.N)^2
  let diameter:=a.localCapDiameter v K
  let reverse:=diameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  have hP : 0< power:=mul_pos a.data.hN (laplaceComparisonStrength_pos a.data.d a.hlam zg)
  have hAS : 0 ≤ AS:=by dsimp [AS];positivity
  have hAC : 0 ≤ AC:=by dsimp [AC];positivity
  have hD0 : 0 ≤ diameter := mul_nonneg (show 0≤9*Real.log a.data.N by linarith) a.cavityCapTravel_nonneg
  have heven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  have hrev : 0 ≤ reverse:=mul_nonneg (Real.rpow_nonneg hD0 _)
    (Real.rpow_nonneg (mul_nonneg heven (pow_nonneg hy.le _)) _)
  obtain ⟨bins,hbins,hsize,Hopt⟩:=exists_integer_native_bin_scale hLside hAS hAC hmass hrho hP hD0
    (zero_le_one.trans hQ) hy.le hrev cut
  let width:=(Q^2*y)/(bins:ℝ)
  obtain ⟨hwidth,hcoverage⟩:=native_bin_width_coverage (zero_lt_one.trans_le hQ) hy hbins
  let Dcuts:=P.capEndpointLedger c
  obtain ⟨M⟩:=hnMaster a hs hsxs P ι c Dcuts ag zg bins (by omega) width cut hag hzg hwidth hleft hright
    (P.capEndpointLedger_interiors_clear c hcontacts)
  have Hphys:=M.full_thermal_le_band_budget hwhole hcontacts hdisjoint hag hagz hzg hclock hleft hright
    (P.capEndpointLedger_interiors_clear c hcontacts) hlo hK0 hband hamass hzmass hN hlog hnd hv hK
    hsourceLeft hsourceSpan hell hmassSpan hy.le hwidth hcut hLside hY hcoverage hlogcut
    (Fintype.card (FeatureIndex (n+1))-1) (cavityCanonicalFeatureEquiv n)
  have hc : 0< a.alpha.val.val ag:=a.shiftedNativeModel.profile_pos hag (hagz.trans hzg)
  have hCS : AS/(power*a.alpha.val.val ag) ≤ AS/(power*rho):=
    div_le_div_of_nonneg_left hAS (mul_pos hP hrho)
      (mul_le_mul_of_nonneg_left hrhoFloor hP.le)
  have hCT : AC/(power*(a.alpha.val.val ag)^2) ≤ AC/(power*rho^2):=
    div_le_div_of_nonneg_left hAC (mul_pos hP (sq_pos_of_pos hrho))
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrho.le hrhoFloor 2) hP.le)
  have Hscalar : nativeConditionalLedgerBudget bins bandMass cut (width+diameter)
      ((AS/(power*a.alpha.val.val ag))*(bins:ℝ)*Lside)
      ((AC/(power*(a.alpha.val.val ag)^2))*bandMass) reverse Lside ≤
      nativeConditionalLedgerBudget bins bandMass cut (width+diameter)
        (AS*Lside*(bins:ℝ)/(power*rho)) (AC*bandMass/(power*rho^2)) reverse Lside:=by
    have HV:=mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCS (Nat.cast_nonneg bins)) hLside)
      (by norm_num : (0:ℝ) ≤ 48)
    have HT:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCT hmass.le)
      (show 0 ≤ 66+64*Lside+65536*(1+Lside)^2 by positivity)
    have HVeq : AS/(power*rho)*(bins:ℝ)*Lside=AS*Lside*(bins:ℝ)/(power*rho):=by ring_nf
    have HTeq : AC/(power*rho^2)*bandMass=AC*bandMass/(power*rho^2):=by ring_nf
    rw [HVeq] at HV
    rw [HTeq] at HT
    unfold nativeConditionalLedgerBudget
    linarith only [HV,HT]
  have Hphys' : (∫u in 0..1,(P.retainedSupport c ag zg).indicator (fun _=>1)
      (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u) ≤
      nativeConditionalLedgerBudget bins bandMass cut (width+diameter)
        ((AS/(power*a.alpha.val.val ag))*(bins:ℝ)*Lside)
        ((AC/(power*(a.alpha.val.val ag)^2))*bandMass) reverse Lside+2*(bins:ℝ)*cut:=by
    simpa only [ActualHighOnlyOverlapMinimum.SelectedMasterFamily.limitThermal,
      ActualHighOnlyOverlapMinimum.SelectedMasterFamily.fullLimitSupport,AS,AC,power,diameter,reverse,
      ActualHighOnlyComparisonData.N,Nat.cast_add,Nat.cast_one] using Hphys
  have Hcut:=mul_le_mul_of_nonneg_right hsize (mul_nonneg (by norm_num : (0:ℝ) ≤ 18) hcut.le)
  have Hfinal:=Hphys'.trans (add_le_add Hscalar le_rfl)
  have Hopt' : nativeConditionalLedgerBudget bins bandMass cut (width+diameter)
      (AS*Lside*(bins:ℝ)/(power*rho)) (AC*bandMass/(power*rho^2)) reverse Lside+
      2*(bins:ℝ)*cut ≤ a.ordinaryOptimizedBudget ell Q K0 Lside cut bandMass rho y v K zg:=by
    unfold ActualHighOnlyOverlapMinimum.ordinaryOptimizedBudget
    nlinarith only [Hopt,Hcut]
  exact Hfinal.trans Hopt'

end OAI.SKFluctuations.LaplaceWindowFormalization
