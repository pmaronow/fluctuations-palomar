module

public import ComparisonActualHighWallSelectedSideTrace
public import ComparisonActualConditionalLedgerLimit
public import ComparisonActualHighWallSelectedUnionTrace
public import ComparisonActualHighWallSelectedDefectLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option linter.unusedSectionVars false
attribute [local instance] Classical.propDecidable

theorem actual_conditional_ledger_enlarge {B bins : ℕ} {v band cut eta CS CT R L : ℝ}
    (hB : B ≤ bins) (_hv : 0 ≤ v) (hband : v ≤ band) (hcut : 0 ≤ cut)
    (hCS : 0 ≤ CS) (hCT : 0 ≤ CT) (hR : 0 ≤ R) (hL : 0 ≤ L) :
    nativeConditionalLedgerBudget B v cut eta (CS*(B:ℝ)*L) (CT*v) R L ≤
      nativeConditionalLedgerBudget bins band cut eta (CS*(bins:ℝ)*L) (CT*band) R L := by
  have hBr : (B:ℝ) ≤ bins:=by exact_mod_cast hB
  have hmean : 0 ≤ 76+64*L:=by positivity
  have hcov : 0 ≤ 66+64*L+65536*(1+L)^2:=by positivity
  have HS:=mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBr hCS) hL) (by norm_num : (0:ℝ) ≤ 48)
  have HM:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hband hmean) (sq_nonneg eta)
  have HR:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hband (by norm_num : (0:ℝ) ≤ 32)) hR
  have HT:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hband hCT) hcov
  have HC:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hBr (by norm_num : (0:ℝ) ≤ 16)) hcut
  unfold nativeConditionalLedgerBudget
  linarith

namespace ActualHighWallOverlapMinimum.SelectedMasterFamily
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighWallOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential} {ι : Type*} [Fintype ι] {c : ι→ShiftedCapInterval a P}
variable {Dcuts : Finset ℝ} {ag zg w cut Q : ℝ} {bins ell : ℕ} {hbins : 0<bins}
variable (M : SelectedMasterFamily a P c Dcuts ag zg bins hbins w cut ell Q)

theorem side_filled_sum_eventually
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)))
    (hag : a.data.rmin< ag) (hagz : ag ≤ zg) (hzg : zg ≤ 1)
    (hleft : ∀t,ag ≤ (c t).left) (hright : ∀t,(c t).right ≤ zg)
    (hinterior : ∀t,∀d∈Dcuts,d∉Ioo (c t).left (c t).right)
    {lo hi K0 : ℝ} (hlo : 0 ≤ lo) (hK : 1 ≤ K0)
    (hband : hi+comparisonSmallMass a.data.N a.data.E ≤ K0*(lo+comparisonSmallMass a.data.N a.data.E))
    (hamass : ∀t,lo ≤ a.alpha.val.val (c t).left) (hzmass : ∀t,a.alpha.val.val (c t).right ≤ hi)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    (hcut : 0<cut) {Lside : ℝ} (hlogcut : Real.log (1/cut) ≤ Lside)
    {B : ℕ} (label : Fin B→Fin bins) (hkept : ∀b,M.keep (label b)=true)
    (dphys : ℕ) (ephys : Fin (dphys+1)≃FeatureIndex (n+1))
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∀ᶠj in atTop,M.sideFilled label dphys ephys j ≤
      (108*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g zg*a.alpha.val.val ag))*
        (B:ℝ)*Lside+epsilon := by
  let coefficient:=108*K0^2*(Real.log a.data.N)^2/
    ((n+1:ℝ)*a.data.g zg*a.alpha.val.val ag)
  let err:=epsilon/((B:ℝ)+1)
  have herr : 0<err:=div_pos hepsilon (by positivity)
  have hmass : 0<a.alpha.val.val ag:=a.shiftedNativeModel.profile_pos hag (hagz.trans hzg)
  have hcoef : 0 ≤ coefficient:=by
    dsimp [coefficient]
    have HG:=laplaceComparisonStrength_pos a.data.d (sq_pos_of_pos a.data.hd) zg
    positivity
  have hlogb (b : Fin B) : Real.log ((M.f (label b) ⟨1,by simp⟩)/cut) ≤ Lside:=by
    have hwidth : 2*cut ≤ M.f (label b) ⟨1,by simp⟩:=ge_of_tendsto (M.widths (label b))
      (Eventually.of_forall (fun j=>(M.cutoffs j (label b)).mpr (hkept b)))
    apply (Real.log_le_log (div_pos (by linarith) hcut) _).trans hlogcut
    exact div_le_div_of_nonneg_right (M.width_limit_mem (label b)).2 hcut.le
  have hall : ∀b : Fin B,∀ᶠj in atTop,
      (2*(∫r,deriv a.alpha.val.val r*a.shiftedNativeModel.unitColumn (M.as j) (M.bin j (label b))
        (M.co j (label b)).unit (fun u=>sideSquareColumn (M.co j (label b)).x cut
          (M.width j (label b)) u.val) r
          ∂a.shiftedNativeModel.radiusMeasure dphys ephys (M.as j) (M.ho j))+4*M.mesh j/cut)/
        a.alpha.val.val ag ≤ coefficient*Real.log ((M.f (label b) ⟨1,by simp⟩)/cut)+err:=by
    intro b
    exact M.bin_side_filled_eventually hwhole hcontacts hdisjoint hag hagz hzg hleft hright hinterior
      hlo hK hband hamass hzmass hN hlog hnd hcut (label b) (hkept b) dphys ephys herr
  filter_upwards [Filter.eventually_all.mpr hall] with j hj
  have HS:=Finset.sum_le_sum (s:=Finset.univ) (fun b _=>(hj b).trans
    (add_le_add (mul_le_mul_of_nonneg_left (hlogb b) hcoef) le_rfl))
  change (∑b,_) ≤ _
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at HS
  have herrbound : (B:ℝ)*err ≤ epsilon:=by
    dsimp [err]
    rw [←mul_div_assoc]
    apply (div_le_iff₀ (by positivity : 0<(B:ℝ)+1)).mpr
    nlinarith
  change (∑b,_) ≤ coefficient*(B:ℝ)*Lside+epsilon
  have HE : (B:ℝ)*(coefficient*Lside+err)=coefficient*(B:ℝ)*Lside+(B:ℝ)*err:=by ring_nf
  rw [HE] at HS
  exact HS.trans (add_le_add le_rfl herrbound)

abbrev KeptBin := {b : Fin bins // M.keep b=true}
def keptCount : ℕ:=Fintype.card M.KeptBin
def keptLabel : Fin M.keptCount→Fin bins:=fun b=>((Fintype.equivFin M.KeptBin).symm b).val

theorem keptLabel_injective : Function.Injective M.keptLabel:=
  Subtype.coe_injective.comp (Fintype.equivFin M.KeptBin).symm.injective

theorem keptLabel_kept (b : Fin M.keptCount) : M.keep (M.keptLabel b)=true:=
  ((Fintype.equivFin M.KeptBin).symm b).property

theorem keptLabel_surjective (b : Fin bins) (hb : M.keep b=true) :
    ∃d : Fin M.keptCount,M.keptLabel d=b:=by
  refine ⟨(Fintype.equivFin M.KeptBin) ⟨b,hb⟩,?_⟩
  simp only [keptLabel,Equiv.symm_apply_apply]

theorem kept_support_eq :
    (⋃b : Fin M.keptCount,P.retainedSupport c ag zg∩Ioo (M.l (M.keptLabel b)).val (M.u (M.keptLabel b)).val)=
      nativeKeptSupport (fun b=>P.retainedSupport c ag zg∩Ioo (M.l b).val (M.u b).val) M.keep:=by
  ext r
  constructor
  · intro hr
    obtain ⟨b,hb⟩:=mem_iUnion.mp hr
    exact ⟨M.keptLabel b,M.keptLabel_kept b,hb⟩
  · rintro ⟨b,hb,hr⟩
    obtain ⟨d,rfl⟩:=M.keptLabel_surjective b hb
    exact mem_iUnion.mpr ⟨d,hr⟩

theorem thermal_le_conditional_ledger
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)))
    (hag : a.data.rmin< ag) (hagz : ag ≤ zg) (hzg : zg ≤ 1)
    (hleft : ∀t,ag ≤ (c t).left) (hright : ∀t,(c t).right ≤ zg)
    (hinterior : ∀t,∀d∈Dcuts,d∉Ioo (c t).left (c t).right)
    {lo hi K0 : ℝ} (hlo : 0 ≤ lo) (hK0 : 1 ≤ K0)
    (hband : hi+comparisonSmallMass a.data.N a.data.E ≤ K0*(lo+comparisonSmallMass a.data.N a.data.E))
    (hamass : ∀t,lo ≤ a.alpha.val.val (c t).left) (hzmass : ∀t,a.alpha.val.val (c t).right ≤ hi)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    {v K : ℝ} (hv : 0<v) (hK : 0<K)
    (hsourceLeft : ∀t,v ≤ a.alpha.val.val (c t).left+comparisonSmallMass a.data.N a.data.E)
    (hsourceSpan : ∀t,a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ K*v)
    (hell : 2<ell) {B : ℕ} (hB : 0<B) (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    (hkept : ∀b,M.keep (label b)=true) {y Lside : ℝ}
    (hy : 0 ≤ y) (hw : 0<w) (hcut : 0<cut) (hLside : 0 ≤ Lside)
    (hY : a.xs+a.alpha.val.val zg ≤ y) (hRange : Q^2*y ≤ (bins:ℝ)*w)
    (hlogcut : Real.log (1/cut) ≤ Lside) (dphys : ℕ) (ephys : Fin (dphys+1)≃FeatureIndex (n+1)) :
    M.limitThermal (M.selectedLimitSupport label) ≤
      nativeConditionalLedgerBudget B (∑b,M.f (label b) ⟨1,by simp⟩) cut
        (w+a.localCapDiameter v K)
        ((108*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g zg*a.alpha.val.val ag))*(B:ℝ)*Lside)
        ((54*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g zg*(a.alpha.val.val ag)^2))*
          (∑b,M.f (label b) ⟨1,by simp⟩))
        ((a.localCapDiameter v K)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
          ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))) Lside := by
  have hD0 : 0<a.localCapDiameter v K:=by
    unfold ActualHighWallOverlapMinimum.localCapDiameter
    have hE:=a.data.hE
    have hNp:=a.data.hN
    have hd:=a.data.hd
    have hLp : 0<Real.log a.data.N:=by linarith
    positivity
  apply actual_conditional_ledger_limit_le B ell hell cut w y Q Lside _ _ _ _ _
    hLside hy hD0 (fun j=>∑b,M.width j (label b)) (M.diameter v K) M.rawValue
    (M.sideFilled label dphys ephys) (M.unionFilled label dphys ephys) (M.defect label)
  · intro j
    exact Finset.sum_nonneg (fun b _=>(M.width_mem j (label b)).1)
  · exact M.diameter_nonneg hv hK (by linarith)
  · exact M.rawValue_nonneg
  · exact M.raw
  · exact M.finite_budget hwhole hcontacts hag hzg hN hlog hnd hv hK hsourceLeft hsourceSpan
      hell hB label hlabel hkept hy hw hcut hLside hY hRange hlogcut dphys ephys
  · exact M.total_width_tendsto label
  · exact M.diameter_tendsto v K
  · exact M.defect_tendsto hag hzg label
  · intro epsilon hepsilon
    exact M.side_filled_sum_eventually hwhole hcontacts hdisjoint hag hagz hzg hleft hright hinterior
      hlo hK0 hband hamass hzmass hN hlog hnd hcut hlogcut label hkept dphys ephys hepsilon
  · intro epsilon hepsilon
    exact M.union_filled_eventually hwhole hcontacts hdisjoint hag hagz hzg hleft hright
      hlo hK0 hband hamass hzmass hN hlog hnd hB label hlabel dphys ephys hepsilon

theorem full_thermal_le_band_budget
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)))
    (hag : a.data.rmin< ag) (hagz : ag ≤ zg) (hzg : zg ≤ 1)
    (hleft : ∀t,ag ≤ (c t).left) (hright : ∀t,(c t).right ≤ zg)
    (hinterior : ∀t,∀d∈Dcuts,d∉Ioo (c t).left (c t).right)
    {lo hi K0 : ℝ} (hlo : 0 ≤ lo) (hK0 : 1 ≤ K0)
    (hband : hi+comparisonSmallMass a.data.N a.data.E ≤ K0*(lo+comparisonSmallMass a.data.N a.data.E))
    (hamass : ∀t,lo ≤ a.alpha.val.val (c t).left) (hzmass : ∀t,a.alpha.val.val (c t).right ≤ hi)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    {v K : ℝ} (hv : 0<v) (hK : 0<K)
    (hsourceLeft : ∀t,v ≤ a.alpha.val.val (c t).left+comparisonSmallMass a.data.N a.data.E)
    (hsourceSpan : ∀t,a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ K*v)
    (hell : 2<ell) {bandMass y Lside : ℝ}
    (hbandMass : a.alpha.val.val zg-a.alpha.val.val ag ≤ bandMass)
    (hy : 0 ≤ y) (hw : 0<w) (hcut : 0<cut) (hLside : 0 ≤ Lside)
    (hY : a.xs+a.alpha.val.val zg ≤ y) (hRange : Q^2*y ≤ (bins:ℝ)*w)
    (hlogcut : Real.log (1/cut) ≤ Lside) (dphys : ℕ) (ephys : Fin (dphys+1)≃FeatureIndex (n+1)) :
    M.limitThermal M.fullLimitSupport ≤
      nativeConditionalLedgerBudget bins bandMass cut (w+a.localCapDiameter v K)
        ((108*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g zg*a.alpha.val.val ag))*(bins:ℝ)*Lside)
        ((54*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g zg*(a.alpha.val.val ag)^2))*bandMass)
        ((a.localCapDiameter v K)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
          ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))) Lside+2*(bins:ℝ)*cut := by
  let CS:=108*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g zg*a.alpha.val.val ag)
  let CT:=54*K0^2*(Real.log a.data.N)^2/((n+1:ℝ)*a.data.g zg*(a.alpha.val.val ag)^2)
  let rev:=(a.localCapDiameter v K)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  have hc : 0<a.alpha.val.val ag:=a.shiftedNativeModel.profile_pos hag (hagz.trans hzg)
  have hg : 0<a.data.g zg:=laplaceComparisonStrength_pos a.data.d (sq_pos_of_pos a.data.hd) zg
  have hCS : 0 ≤ CS:=by dsimp [CS];positivity
  have hCT : 0 ≤ CT:=by dsimp [CT];positivity
  have hD0 : 0 ≤ a.localCapDiameter v K:=by
    unfold ActualHighWallOverlapMinimum.localCapDiameter
    have hE:=a.data.hE
    have hNp:=a.data.hN
    have hd:=a.data.hd
    have hLp : 0<Real.log a.data.N:=by linarith
    positivity
  have heven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  have hrev : 0 ≤ rev:=mul_nonneg (Real.rpow_nonneg hD0 _)
    (Real.rpow_nonneg (mul_nonneg heven (pow_nonneg hy _)) _)
  have hMass0 : 0 ≤ bandMass:=
    (sub_nonneg.mpr (a.alpha.val.property.2 hagz)).trans hbandMass
  have Hrestore:=M.full_thermal_le_selected_add_2_bins_cut hag hzg hcut.le M.keptLabel
    M.keptLabel_kept M.keptLabel_surjective
  by_cases hB : 0<M.keptCount
  · have H:=M.thermal_le_conditional_ledger hwhole hcontacts hdisjoint hag hagz hzg hleft hright
      hinterior hlo hK0 hband hamass hzmass hN hlog hnd hv hK hsourceLeft hsourceSpan hell hB
      M.keptLabel M.keptLabel_injective M.keptLabel_kept hy hw hcut hLside hY hRange hlogcut dphys ephys
    have hCount : M.keptCount ≤ bins:=by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective M.keptLabel M.keptLabel_injective
    have hTotal0 : 0 ≤ ∑b,M.f (M.keptLabel b) ⟨1,by simp⟩:=
      Finset.sum_nonneg (fun b _=>(M.width_limit_mem (M.keptLabel b)).1)
    have hTotal : (∑b,M.f (M.keptLabel b) ⟨1,by simp⟩) ≤ bandMass:=
      (M.total_width_limit_le_band M.keptLabel M.keptLabel_injective hagz).trans hbandMass
    have HE:=actual_conditional_ledger_enlarge (eta:=w+a.localCapDiameter v K) hCount hTotal0 hTotal
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
    have Hbudget : 0 ≤ nativeConditionalLedgerBudget bins bandMass cut (w+a.localCapDiameter v K)
      (CS*(bins:ℝ)*Lside) (CT*bandMass) rev Lside:=by
      unfold nativeConditionalLedgerBudget
      positivity
    exact Hrestore.trans (le_add_of_nonneg_left Hbudget)

end ActualHighWallOverlapMinimum.SelectedMasterFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
