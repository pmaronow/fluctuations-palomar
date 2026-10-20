module

public import ComparisonActualHighOnlySelectedThermalLedger
public import ComparisonActualHighOnlySelectedLedgerAtDiameter
public import ComparisonActualHighOnlySelectedSideTrace
public import ComparisonActualConditionalLedgerLimit
public import ComparisonActualHighOnlySelectedUnionTrace
public import ComparisonActualHighOnlySelectedDefectLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable

namespace ActualHighOnlyOverlapMinimum.SelectedMasterFamily
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential} {ι : Type*} [Fintype ι] {c : ι→ShiftedCapInterval a P}
variable {Dcuts : Finset ℝ} {ag zg w cut Q : ℝ} {bins ell : ℕ} {hbins : 0<bins}
variable (M : SelectedMasterFamily a P c Dcuts ag zg bins hbins w cut ell Q)

theorem thermal_le_conditional_ledger_at_diameter
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)))
    (hag : (0:ℝ)< ag) (hagz : ag ≤ zg) (hzg : zg ≤ 1)
    (hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h ag zg)
    (hleft : ∀t,ag ≤ (c t).left) (hright : ∀t,(c t).right ≤ zg)
    (hinterior : ∀t,∀d∈Dcuts,d∉Ioo (c t).left (c t).right)
    {lo hi K0 : ℝ} (hlo : 0 ≤ lo) (hK0 : 1 ≤ K0)
    (hband : hi+comparisonSmallMass a.data.N a.data.E ≤ K0*(lo+comparisonSmallMass a.data.N a.data.E))
    (hamass : ∀t,lo ≤ a.alpha.val.val (c t).left) (hzmass : ∀t,a.alpha.val.val (c t).right ≤ hi)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    {v K : ℝ} (hv : 0<v) (hK : 0<K)
    (hsourceLeft : ∀t,v ≤ a.alpha.val.val (c t).left+comparisonSmallMass a.data.N a.data.E)
    (hsourceSpan : ∀t,a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ K*v)
    (baseDiameter : ℝ) (hbaseDiameter : 0 < baseDiameter)
    (hinc : ∀t,∀s∈Ioo (c t).left (c t).right,∀r∈Ioo (c t).left (c t).right,s ≤ r →
      a.radiusS r-a.radiusS s ≤ baseDiameter)
    (hell : 2<ell) {B : ℕ} (hB : 0<B) (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    (hkept : ∀b,M.keep (label b)=true) {y Lside : ℝ}
    (hy : 0 ≤ y) (hw : 0<w) (hcut : 0<cut) (hLside : 0 ≤ Lside)
    (hY : a.xs+a.alpha.val.val zg ≤ y) (hRange : Q^2*y ≤ (bins:ℝ)*w)
    (hlogcut : Real.log (1/cut) ≤ Lside) (dphys : ℕ) (ephys : Fin (dphys+1)≃FeatureIndex (n+1)) :
    M.limitThermal (M.selectedLimitSupport label) ≤
      nativeConditionalLedgerBudget B (∑b,M.f (label b) ⟨1,by simp⟩) cut
        (w+baseDiameter)
        ((108*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) zg*a.alpha.val.val ag))*(B:ℝ)*Lside)
        ((54*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) zg*(a.alpha.val.val ag)^2))*
          (∑b,M.f (label b) ⟨1,by simp⟩))
        ((baseDiameter)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
          ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))) Lside := by
  apply actual_conditional_ledger_limit_le B ell hell cut w y Q Lside _ _ _ _ _
    hLside hy hbaseDiameter (fun j=>∑b,M.width j (label b)) (M.diameterAt baseDiameter) M.rawValue
    (M.sideFilled label dphys ephys) (M.unionFilled label dphys ephys) (M.defect label)
  · intro j
    exact Finset.sum_nonneg (fun b _=>(M.width_mem j (label b)).1)
  · exact M.diameterAt_nonneg hbaseDiameter.le
  · exact M.rawValue_nonneg
  · exact M.raw
  · exact M.finite_budget_at_diameter hwhole (fun t=>⟨Or.inl (hcontacts t).1,(hcontacts t).2⟩) hag hzg hN hlog hnd hv hK hsourceLeft hsourceSpan baseDiameter hbaseDiameter.le hinc
      hell hB label hlabel hkept hy hw hcut hLside hY hRange hlogcut dphys ephys
  · exact M.total_width_tendsto label
  · exact M.diameterAt_tendsto baseDiameter
  · exact M.defect_tendsto hag hzg label
  · intro epsilon hepsilon
    exact M.side_filled_sum_eventually hwhole hcontacts hdisjoint hag hagz hzg hclock hleft hright hinterior
      hlo hK0 hband hamass hzmass hN hlog hnd hcut hlogcut label hkept dphys ephys hepsilon
  · intro epsilon hepsilon
    exact M.union_filled_eventually hwhole hcontacts hdisjoint hag hagz hzg hclock hleft hright
      hlo hK0 hband hamass hzmass hN hlog hnd hB label hlabel dphys ephys hepsilon

theorem full_thermal_le_band_budget_at_diameter
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)))
    (hag : (0:ℝ)< ag) (hagz : ag ≤ zg) (hzg : zg ≤ 1)
    (hclock : NativePullbackClockRegularity a.alpha.val.val a.b a.h ag zg)
    (hleft : ∀t,ag ≤ (c t).left) (hright : ∀t,(c t).right ≤ zg)
    (hinterior : ∀t,∀d∈Dcuts,d∉Ioo (c t).left (c t).right)
    {lo hi K0 : ℝ} (hlo : 0 ≤ lo) (hK0 : 1 ≤ K0)
    (hband : hi+comparisonSmallMass a.data.N a.data.E ≤ K0*(lo+comparisonSmallMass a.data.N a.data.E))
    (hamass : ∀t,lo ≤ a.alpha.val.val (c t).left) (hzmass : ∀t,a.alpha.val.val (c t).right ≤ hi)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    {v K : ℝ} (hv : 0<v) (hK : 0<K)
    (hsourceLeft : ∀t,v ≤ a.alpha.val.val (c t).left+comparisonSmallMass a.data.N a.data.E)
    (hsourceSpan : ∀t,a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ K*v)
    (baseDiameter : ℝ) (hbaseDiameter : 0 < baseDiameter)
    (hinc : ∀t,∀s∈Ioo (c t).left (c t).right,∀r∈Ioo (c t).left (c t).right,s ≤ r →
      a.radiusS r-a.radiusS s ≤ baseDiameter)
    (hell : 2<ell) {bandMass y Lside : ℝ}
    (hbandMass : a.alpha.val.val zg-a.alpha.val.val ag ≤ bandMass)
    (hy : 0 ≤ y) (hw : 0<w) (hcut : 0<cut) (hLside : 0 ≤ Lside)
    (hY : a.xs+a.alpha.val.val zg ≤ y) (hRange : Q^2*y ≤ (bins:ℝ)*w)
    (hlogcut : Real.log (1/cut) ≤ Lside) (dphys : ℕ) (ephys : Fin (dphys+1)≃FeatureIndex (n+1)) :
    M.limitThermal M.fullLimitSupport ≤
      nativeConditionalLedgerBudget bins bandMass cut (w+baseDiameter)
        ((108*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) zg*a.alpha.val.val ag))*(bins:ℝ)*Lside)
        ((54*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) zg*(a.alpha.val.val ag)^2))*bandMass)
        ((baseDiameter)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
          ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))) Lside+2*(bins:ℝ)*cut := by
  let CS:=108*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) zg*a.alpha.val.val ag)
  let CT:=54*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*(laplaceComparisonStrength a.data.d a.lam) zg*(a.alpha.val.val ag)^2)
  let rev:=(baseDiameter)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  have hc : 0<a.alpha.val.val ag:=a.shiftedNativeModel.profile_pos hag (hagz.trans hzg)
  have hg : 0<(laplaceComparisonStrength a.data.d a.lam) zg:=laplaceComparisonStrength_pos a.data.d a.hlam zg
  have hCS : 0 ≤ CS:=by dsimp [CS];positivity
  have hCT : 0 ≤ CT:=by dsimp [CT];positivity
  have hD0 : 0 ≤ baseDiameter := hbaseDiameter.le
  have heven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  have hrev : 0 ≤ rev:=mul_nonneg (Real.rpow_nonneg hD0 _)
    (Real.rpow_nonneg (mul_nonneg heven (pow_nonneg hy _)) _)
  have hMass0 : 0 ≤ bandMass:=
    (sub_nonneg.mpr (a.alpha.val.property.2 hagz)).trans hbandMass
  have Hrestore:=M.full_thermal_le_selected_add_2_bins_cut hag hzg hcut.le M.keptLabel
    M.keptLabel_kept M.keptLabel_surjective
  by_cases hB : 0<M.keptCount
  · have H:=M.thermal_le_conditional_ledger_at_diameter hwhole hcontacts hdisjoint hag hagz hzg hclock hleft hright
      hinterior hlo hK0 hband hamass hzmass hN hlog hnd hv hK hsourceLeft hsourceSpan baseDiameter hbaseDiameter hinc hell hB
      M.keptLabel M.keptLabel_injective M.keptLabel_kept hy hw hcut hLside hY hRange hlogcut dphys ephys
    have hCount : M.keptCount ≤ bins:=by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective M.keptLabel M.keptLabel_injective
    have hTotal0 : 0 ≤ ∑b,M.f (M.keptLabel b) ⟨1,by simp⟩:=
      Finset.sum_nonneg (fun b _=>(M.width_limit_mem (M.keptLabel b)).1)
    have hTotal : (∑b,M.f (M.keptLabel b) ⟨1,by simp⟩) ≤ bandMass:=
      (M.total_width_limit_le_band M.keptLabel M.keptLabel_injective hagz).trans hbandMass
    have HE:=actual_conditional_ledger_enlarge (eta:=w+baseDiameter) hCount hTotal0 hTotal
      hcut.le hCS hCT hrev hLside
    apply Hrestore.trans
    have HB:=H.trans HE
    exact add_le_add HB le_rfl
  · have hB0 : M.keptCount=0:=by omega
    have Hem : M.selectedLimitSupport M.keptLabel=∅:=by
      ext r
      constructor
      · rintro ⟨b,_,_⟩
        have HB:=b.isLt
        omega
      · simp
    have HT0 : M.limitThermal (M.selectedLimitSupport M.keptLabel)=0:=by
      rw [Hem]
      simp only [limitThermal,indicator_empty,zero_mul,intervalIntegral.integral_zero]
    rw [HT0,zero_add] at Hrestore
    have Hbudget : 0 ≤ nativeConditionalLedgerBudget bins bandMass cut (w+baseDiameter)
      (CS*(bins:ℝ)*Lside) (CT*bandMass) rev Lside:=by
      unfold nativeConditionalLedgerBudget
      positivity
    exact Hrestore.trans (le_add_of_nonneg_left Hbudget)

end ActualHighOnlyOverlapMinimum.SelectedMasterFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
