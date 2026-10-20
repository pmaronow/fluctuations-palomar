module

public import ComparisonActualHighWallThetaZeroOrdinaryPhysicalBudget
public import SKProof.Port.ComparisonActualOriginalQOrdinaryGroupData
public import SKProof.Port.ComparisonActualOriginalQCanonicalMassBudgets
public import SKProof.Port.OriginalQHighOnlyBridge
public import SKProof.Port.ComparisonActualOriginalQConditionalAssembly

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}

def Potential.canonicalOrdinarySupport
    {a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
    (P : a.Potential) (F : Finset (ordConnectedSection P.negativeSet)) (A : Set ℝ) (v : ℝ) : Set ℝ :=
  P.retainedSupport (P.ordinaryCapFamily (P.capFamily F) A 16 v)
    (a.shiftedNativeModel.R (v/2)) (a.shiftedNativeModel.R (min (16*v) 1))

private theorem canonical_diameter_pos_y2
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (hlog : 0<Real.log a.data.N) : 0<a.canonicalMassDiameter := by
  have htravel : 0<a.cavityCapTravel := by
    unfold cavityCapTravel
    exact mul_pos (div_pos a.data.hL (Real.rpow_pos_of_pos a.data.hN _))
      (Real.log_pos ((one_lt_div a.data.hU).mpr (by linarith)))
  exact mul_pos (mul_pos (by norm_num) hlog) htravel

private def canonicalOptimizedBudgetY2
    (a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
    (ell : ℕ) (Q K0 Lside cut bandMass rho y _v _K zg : ℝ) : ℝ:=
  let power:=a.data.N*laplaceComparisonStrength a.data.d a.lam zg
  let AS:=108*K0^2*(Real.log a.data.N)^2
  let AC:=54*K0^2*(Real.log a.data.N)^2
  let diameter:=a.canonicalMassDiameter
  let reverse:=diameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  nativeBinScaleLoss Lside AS AC bandMass rho*bandMass*
    (2*((Q^2*y)/(power*bandMass^2))^((2:ℝ)/3)+3/(power*bandMass^2)+diameter^2+reverse)+
      18*(((Q^2*y)^2*power*bandMass^2)^((1:ℝ)/3)+2)*cut

namespace SelectedMasterFamily
variable {W : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : W.Potential} {ι : Type*} [Fintype ι] {c : ι→ShiftedCapInterval W P}
variable {Dcuts : Finset ℝ} {ag zg w cut Q : ℝ} {bins ell : ℕ} {hbins : 0<bins}
variable (M : SelectedMasterFamily W P c Dcuts ag zg bins hbins w cut ell Q)
private theorem thermal_le_canonical_y2
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)))
    (hag : W.data.rmin< ag) (hagz : ag ≤ zg) (hzg : zg ≤ 1)
    (hleft : ∀t,ag ≤ (c t).left) (hright : ∀t,(c t).right ≤ zg)
    (hinterior : ∀t,∀d∈Dcuts,d∉Ioo (c t).left (c t).right)
    {lo hi K0 : ℝ} (hlo : 0 ≤ lo) (hK0 : 1 ≤ K0)
    (hband : hi+comparisonSmallMass W.data.N W.data.E ≤ K0*(lo+comparisonSmallMass W.data.N W.data.E))
    (hamass : ∀t,lo ≤ W.alpha.val.val (c t).left) (hzmass : ∀t,W.alpha.val.val (c t).right ≤ hi)
    (hN : 1 ≤ W.data.N) (hlog : 1 ≤ Real.log W.data.N) (hnd : 1/W.data.N ≤ W.data.d)
    {v K : ℝ} (hv : 0<v) (hK : 0<K)
    (hsourceLeft : ∀t,v ≤ W.alpha.val.val (c t).left+comparisonSmallMass W.data.N W.data.E)
    (hsourceSpan : ∀t,W.alpha.val.val (c t).right-W.alpha.val.val (c t).left ≤ K*v)
    (hell : 2<ell) {B : ℕ} (hB : 0<B) (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    (hkept : ∀b,M.keep (label b)=true) {y Lside : ℝ}
    (hy : 0 ≤ y) (hw : 0<w) (hcut : 0<cut) (hLside : 0 ≤ Lside)
    (hY : W.xs+W.alpha.val.val zg ≤ y) (hRange : Q^2*y ≤ (bins:ℝ)*w)
    (hlogcut : Real.log (1/cut) ≤ Lside) (dphys : ℕ) (ephys : Fin (dphys+1)≃FeatureIndex (n+1)) :
    M.limitThermal (M.selectedLimitSupport label) ≤
      nativeConditionalLedgerBudget B (∑b,M.f (label b) ⟨1,by simp⟩) cut
        (w+W.canonicalMassDiameter)
        ((108*K0^2*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg*W.alpha.val.val ag))*(B:ℝ)*Lside)
        ((54*K0^2*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg*(W.alpha.val.val ag)^2))*
          (∑b,M.f (label b) ⟨1,by simp⟩))
        ((W.canonicalMassDiameter)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
          ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))) Lside := by
  have hD0 : 0<W.canonicalMassDiameter := canonical_diameter_pos_y2 W (by linarith)
  let diam j := W.canonicalMassDiameter+2*(M.mesh j*(2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) W.shiftedNativeModel.q))
  have hdiam j : 0≤diam j := by
    have hjet := ClockTree.errorJetVariation_nonneg 2 0 0
    have hclock := clockVariationBound_nonneg (physicalFeatureCoordinateBound n) W.shiftedNativeModel.q
      (completedPathClock_monotone _ W.shiftedNativeModel.hbf W.shiftedNativeModel.hhf)
    exact add_nonneg hD0.le (mul_nonneg (by norm_num)
      (mul_nonneg (M.mesh_nonneg j) (mul_nonneg (mul_nonneg (by norm_num) hjet) hclock)))
  have hdiamLimit : Tendsto diam atTop (𝓝 W.canonicalMassDiameter) := by
    simpa only [diam,mul_zero,zero_mul,add_zero] using
      ((M.mesh_tendsto.mul_const (2*ClockTree.errorJetVariation 2 0 0*
        clockVariationBound (physicalFeatureCoordinateBound n) W.shiftedNativeModel.q)).const_mul 2).const_add W.canonicalMassDiameter
  apply actual_conditional_ledger_limit_le B ell hell cut w y Q Lside _ _ _ _ _
    hLside hy hD0 (fun j=>∑b,M.width j (label b)) diam M.rawValue
    (M.sideFilled label dphys ephys) (M.unionFilled label dphys ephys) (M.defect label)
  · intro j
    exact Finset.sum_nonneg (fun b _=>(M.width_mem j (label b)).1)
  · exact hdiam
  · exact M.rawValue_nonneg
  · exact M.raw
  · intro j
    have hwidth b : 2*cut ≤ M.width j (label b):=(M.cutoffs j (label b)).mpr (hkept b)
    have hsideLog b : Real.log (M.width j (label b)/cut) ≤ Lside:=by
      have hwp : 0<M.width j (label b):=by linarith [hwidth b]
      apply (Real.log_le_log (div_pos hwp hcut) _).trans hlogcut
      apply div_le_div_of_nonneg_right _ hcut.le
      rw [width,(M.co j (label b)).width]
      exact (physicalWindowMass_mem_Icc_one _ (sampleClockSteps_ordered _ _ (M.ho j)) _).2
    have hr0 : 0 ≤ M.rawValue j:=zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)
    have hheight : (M.rawValue j)^2*y ≤ (bins:ℝ)*w:=
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hr0 (M.raw j) 2) hy).trans hRange
    have HF:=P.retained_conditional_finite_assembly_original_q c hwhole
      (fun t=>⟨Or.inl (hcontacts t).1,(hcontacts t).2⟩)
      (fun t=>(c t).wallGate_of_left_ne ((hag.trans_le (hleft t)).ne')) Dcuts hag hzg hN hlog hnd
      hv hK hsourceLeft hsourceSpan ell hell (M.as j) (M.ho j) (M.he j) (M.hmesh j) (M.mesh_nonneg j)
      hB label hlabel hw hcut hLside hY hheight hwidth hsideLog dphys ephys
    dsimp only at HF
    have HD : (∑i,(∑b,physicalSelectedCellMass (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j))
        (M.bin j (label b)) i)*actualCutReplicaDefect (n+1)
          (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j)) (W.shiftedNativeModel.q 0) i.val
          (physicalPathSecondMoment (n+1) (sampleClockSteps W.shiftedNativeModel.q 0 (M.as j))
            (W.shiftedNativeModel.q 0) i.val))=M.defect label j:=by
      unfold defect selected
      apply Finset.sum_congr rfl
      intro i _
      rw [selectedCellMass_sum_eq_biUnion _ _ (M.bin_disjoint label hlabel j)]
    rw [HD] at HF
    exact HF
  · exact M.total_width_tendsto label
  · exact hdiamLimit
  · exact M.defect_tendsto hag hzg label
  · intro epsilon hepsilon
    exact M.side_filled_sum_eventually hwhole hcontacts hdisjoint hag hagz hzg hleft hright hinterior
      hlo hK0 hband hamass hzmass hN hlog hnd hcut hlogcut label hkept dphys ephys hepsilon
  · intro epsilon hepsilon
    exact M.union_filled_eventually hwhole hcontacts hdisjoint hag hagz hzg hleft hright
      hlo hK0 hband hamass hzmass hN hlog hnd hB label hlabel dphys ephys hepsilon

private theorem full_thermal_canonical_y2
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)))
    (hag : W.data.rmin< ag) (hagz : ag ≤ zg) (hzg : zg ≤ 1)
    (hleft : ∀t,ag ≤ (c t).left) (hright : ∀t,(c t).right ≤ zg)
    (hinterior : ∀t,∀d∈Dcuts,d∉Ioo (c t).left (c t).right)
    {lo hi K0 : ℝ} (hlo : 0 ≤ lo) (hK0 : 1 ≤ K0)
    (hband : hi+comparisonSmallMass W.data.N W.data.E ≤ K0*(lo+comparisonSmallMass W.data.N W.data.E))
    (hamass : ∀t,lo ≤ W.alpha.val.val (c t).left) (hzmass : ∀t,W.alpha.val.val (c t).right ≤ hi)
    (hN : 1 ≤ W.data.N) (hlog : 1 ≤ Real.log W.data.N) (hnd : 1/W.data.N ≤ W.data.d)
    {v K : ℝ} (hv : 0<v) (hK : 0<K)
    (hsourceLeft : ∀t,v ≤ W.alpha.val.val (c t).left+comparisonSmallMass W.data.N W.data.E)
    (hsourceSpan : ∀t,W.alpha.val.val (c t).right-W.alpha.val.val (c t).left ≤ K*v)
    (hell : 2<ell) {bandMass y Lside : ℝ}
    (hbandMass : W.alpha.val.val zg-W.alpha.val.val ag ≤ bandMass)
    (hy : 0 ≤ y) (hw : 0<w) (hcut : 0<cut) (hLside : 0 ≤ Lside)
    (hY : W.xs+W.alpha.val.val zg ≤ y) (hRange : Q^2*y ≤ (bins:ℝ)*w)
    (hlogcut : Real.log (1/cut) ≤ Lside) (dphys : ℕ) (ephys : Fin (dphys+1)≃FeatureIndex (n+1)) :
    M.limitThermal M.fullLimitSupport ≤
      nativeConditionalLedgerBudget bins bandMass cut (w+W.canonicalMassDiameter)
        ((108*K0^2*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg*W.alpha.val.val ag))*(bins:ℝ)*Lside)
        ((54*K0^2*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg*(W.alpha.val.val ag)^2))*bandMass)
        ((W.canonicalMassDiameter)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
          ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))) Lside+2*(bins:ℝ)*cut := by
  let CS:=108*K0^2*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg*W.alpha.val.val ag)
  let CT:=54*K0^2*(Real.log W.data.N)^2/((n+1:ℝ)*laplaceComparisonStrength W.data.d W.lam zg*(W.alpha.val.val ag)^2)
  let rev:=(W.canonicalMassDiameter)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  have hc : 0<W.alpha.val.val ag:=W.shiftedNativeModel.profile_pos hag (hagz.trans hzg)
  have hg : 0<laplaceComparisonStrength W.data.d W.lam zg:=laplaceComparisonStrength_pos W.data.d W.hlam zg
  have hCS : 0 ≤ CS:=by dsimp [CS];positivity
  have hCT : 0 ≤ CT:=by dsimp [CT];positivity
  have hD0 : 0≤W.canonicalMassDiameter := (canonical_diameter_pos_y2 W (by linarith)).le
  have heven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  have hrev : 0 ≤ rev:=mul_nonneg (Real.rpow_nonneg hD0 _)
    (Real.rpow_nonneg (mul_nonneg heven (pow_nonneg hy _)) _)
  have hMass0 : 0 ≤ bandMass:=
    (sub_nonneg.mpr (W.alpha.val.property.2 hagz)).trans hbandMass
  have Hrestore:=M.full_thermal_le_selected_add_2_bins_cut hag hzg hcut.le M.keptLabel
    M.keptLabel_kept M.keptLabel_surjective
  by_cases hB : 0<M.keptCount
  · have H:=thermal_le_canonical_y2 M hwhole hcontacts hdisjoint hag hagz hzg hleft hright
      hinterior hlo hK0 hband hamass hzmass hN hlog hnd hv hK hsourceLeft hsourceSpan hell hB
      M.keptLabel M.keptLabel_injective M.keptLabel_kept hy hw hcut hLside hY hRange hlogcut dphys ephys
    have hCount : M.keptCount ≤ bins:=by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective M.keptLabel M.keptLabel_injective
    have hTotal0 : 0 ≤ ∑b,M.f (M.keptLabel b) ⟨1,by simp⟩:=
      Finset.sum_nonneg (fun b _=>(M.width_limit_mem (M.keptLabel b)).1)
    have hTotal : (∑b,M.f (M.keptLabel b) ⟨1,by simp⟩) ≤ bandMass:=
      (M.total_width_limit_le_band M.keptLabel M.keptLabel_injective hagz).trans hbandMass
    have HE:=actual_conditional_ledger_enlarge (eta:=w+W.canonicalMassDiameter) hCount hTotal0 hTotal
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
    have Hbudget : 0 ≤ nativeConditionalLedgerBudget bins bandMass cut (w+W.canonicalMassDiameter)
      (CS*(bins:ℝ)*Lside) (CT*bandMass) rev Lside:=by
      unfold nativeConditionalLedgerBudget
      positivity
    exact Hrestore.trans (le_add_of_nonneg_left Hbudget)

end SelectedMasterFamily
end ActualThetaZeroOverlapMinimum

private theorem eventually_canonical_optimized_y2
    (ell : ℕ) (hell : 2< ell) (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< margin) (hdelta : 0< delta) (hroom : delta<3*margin)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0 ≤ Az) (hC0 : 0< C0) (hCt : 0 ≤ Ct) :
    ∃Q : ℝ,1 ≤ Q ∧ ∀ᶠn : ℕ in atTop,
      ∀(a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock)
        (P : a.Potential) (ι : Type*) [Fintype ι] (c : ι→ActualThetaZeroOverlapMinimum.ShiftedCapInterval a P)
        (ag zg lo hi K0 bandMass rho y v K Lside cut : ℝ),
        (∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right) →
        (∀t,P.H (c t).left=0 ∧ (P.H (c t).right=0 ∨ (c t).right=1)) →
        Pairwise (fun t u=> Disjoint (Ioo (c t).left (c t).right) (Ioo (c u).left (c u).right)) →
        a.data.rmin< ag → ag ≤ zg → zg ≤ 1 →
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
          a.canonicalOptimizedBudgetY2 ell Q K0 Lside cut bandMass rho y v K zg := by
  obtain ⟨Q,hQ,Hmaster⟩:=eventually_exists_actual_theta_zero_selected_master ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  have Hdepth:=(tendsto_add_atTop_nat 1).eventually (eventually_comparisonLowerScale_depth hC0 hm)
  have Hlog:=(tendsto_add_atTop_nat 1).eventually
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (1:ℝ))
  refine ⟨Q,hQ,?_⟩
  filter_upwards [Hmaster,Hdepth,Hlog] with n hnMaster hnDepth hnLog
  intro a P ι inst c ag zg lo hi K0 bandMass rho y v K Lside cut hwhole hcontacts hdisjoint
    hag hagz hzg hleft hright hlo hK0 hband hamass hzmass hmass hmassSpan hrho hrhoFloor hy hY hv hK
    hsourceLeft hsourceSpan hLside hcut hlogcut
  have hN : 1 ≤ a.data.N:=by
    dsimp only [ActualHighWallData.N]
    exact_mod_cast Nat.succ_pos n
  have hlog : 1 ≤ Real.log a.data.N:=hnLog
  have hnd : 1/a.data.N ≤ a.data.d:=by
    have HD:=hnDepth a.data.E a.data.d a.data.hE a.data.hd a.hlower
    have HS : comparisonLowerScale (n+1:ℕ) a.data.E a.data.d ≤ a.data.d:=by
      unfold comparisonLowerScale
      exact (div_le_iff₀ a.data.hd).mpr (by simpa only [pow_two] using a.hupper)
    exact HD.trans HS
  let power:=a.data.N*laplaceComparisonStrength a.data.d a.lam zg
  let AS:=108*K0^2*(Real.log a.data.N)^2
  let AC:=54*K0^2*(Real.log a.data.N)^2
  let diameter:=a.canonicalMassDiameter
  let reverse:=diameter^(((ell:ℝ)-2)/((ell:ℝ)-1))*
    ((2*Q)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))
  have hP : 0< power:=mul_pos a.data.hN (laplaceComparisonStrength_pos a.data.d (a.hlam) zg)
  have hAS : 0 ≤ AS:=by dsimp [AS];positivity
  have hAC : 0 ≤ AC:=by dsimp [AC];positivity
  have hD0 : 0≤diameter := (ActualThetaZeroOverlapMinimum.canonical_diameter_pos_y2 a (by linarith)).le
  have heven : 0 ≤ (2*Q)^(2*ell):=by rw [Nat.mul_comm 2 ell,pow_mul];exact sq_nonneg _
  have hrev : 0 ≤ reverse:=mul_nonneg (Real.rpow_nonneg hD0 _)
    (Real.rpow_nonneg (mul_nonneg heven (pow_nonneg hy.le _)) _)
  obtain ⟨bins,hbins,hsize,Hopt⟩:=exists_integer_native_bin_scale hLside hAS hAC hmass hrho hP hD0
    (zero_le_one.trans hQ) hy.le hrev cut
  let width:=(Q^2*y)/(bins:ℝ)
  obtain ⟨hwidth,hcoverage⟩:=native_bin_width_coverage (zero_lt_one.trans_le hQ) hy hbins
  let Dcuts:=P.capEndpointLedger c
  have hmeet : ∀t,max ag (c t).left < min zg (c t).right:=by
    intro t
    rw [max_eq_right (hleft t),min_eq_right (hright t)]
    exact (c t).hlt
  obtain ⟨M⟩:=hnMaster a P ι c Dcuts ag zg bins (by omega) width cut hag hzg hwidth hmeet
    (P.capEndpointLedger_interiors_clear c hcontacts)
  have Hphys:=ActualThetaZeroOverlapMinimum.SelectedMasterFamily.full_thermal_canonical_y2 M hwhole hcontacts hdisjoint hag hagz hzg hleft hright
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
    simpa only [ActualThetaZeroOverlapMinimum.SelectedMasterFamily.limitThermal,
      ActualThetaZeroOverlapMinimum.SelectedMasterFamily.fullLimitSupport,AS,AC,power,diameter,reverse,
      ActualHighWallData.N,Nat.cast_add,Nat.cast_one] using Hphys
  have Hcut:=mul_le_mul_of_nonneg_right hsize (mul_nonneg (by norm_num : (0:ℝ) ≤ 18) hcut.le)
  have Hfinal:=Hphys'.trans (add_le_add Hscalar le_rfl)
  have Hopt' : nativeConditionalLedgerBudget bins bandMass cut (width+diameter)
      (AS*Lside*(bins:ℝ)/(power*rho)) (AC*bandMass/(power*rho^2)) reverse Lside+
      2*(bins:ℝ)*cut ≤ a.canonicalOptimizedBudgetY2 ell Q K0 Lside cut bandMass rho y v K zg:=by
    unfold ActualThetaZeroOverlapMinimum.canonicalOptimizedBudgetY2
    nlinarith only [Hopt,Hcut]
  exact Hfinal.trans Hopt'

theorem eventually_actual_ordinary_mass_budget_original_q
    (ell : ℕ) (hell : 2 < ell) (Bclock : ℝ) {margin delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < margin) (hdelta : 0 < delta) (hroom : delta < 3*margin)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct) :
    ∃Q : ℝ,1  ≤  Q ∧ ∀ᶠn : ℕ in atTop,
      ∀a : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock,
      a.data.s  ≤  1/4 → a.data.s  ≤  a.xs → ∀P : a.Potential,
      NativePullbackClockRegularity a.alpha.val.val a.b a.h a.data.rmin 1 →
      ∀F : Finset (ordConnectedSection P.negativeSet),∀A : Set ℝ,∀v Lside cut : ℝ,
      0 < v → v  ≤  1 → a.data.s < v/2 → 0  ≤  Lside → 0 < cut → Real.log (1/cut)  ≤  Lside →
      (∫u in 0..1,(P.canonicalOrdinarySupport F A v).indicator (fun _=>1)
        (a.shiftedNativeModel.R u)*a.shiftedNativeModel.thermal u)  ≤ 
        a.canonicalOrdinaryMassBudget ell Q Lside cut v := by
  obtain ⟨Q,hQ,Hphysical⟩:=eventually_canonical_optimized_y2 ell hell Bclock
    (D:=D) hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Q,hQ,?_⟩
  filter_upwards [Hphysical] with n hn
  intro a hs hsxs P hclock F A v Lside cut hv hv1 hstart hLside hcut hlogcut
  let m:=a.shiftedNativeModel
  let c:=P.ordinaryCapFamily (P.capFamily F) A 16 v
  let ag:=m.R (v/2)
  let zg:=m.R (min (16*v) 1)
  have hgeom:=P.ordinary_group_geometry (P.capFamily F) A (by norm_num : (1:ℝ)  ≤  16) hv hv1 hstart
  dsimp only at hgeom
  obtain ⟨hag,hzg,hagz,hagmass,hzgmass,hcap⟩:=hgeom
  have hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,
      wholeUnit P.negativeSet r=Ioo (c t).left (c t).right := by
    intro t r hr
    exact P.capFamily_wholeUnit F t.val hr
  have hcontacts:=P.ordinary_group_contacts (P.capFamily F) A (K:=16)
    (show a.data.s < v by linarith) (P.capFamily_contacts F)
  have hdisjoint : Pairwise (fun t u=>Disjoint (Ioo (c t).left (c t).right)
      (Ioo (c u).left (c u).right)) := by
    intro t u htu
    exact P.capFamily_disjoint F (Subtype.val_injective.ne htu)
  have hY : 0 < a.xs+min (16*v) 1 := add_pos_of_pos_of_nonneg a.hxs (le_min (by positivity) zero_le_one)
  have H:=hn a P _ c ag zg v (min (16*v) 1) 32 (16*v) (v/4)
    (a.xs+min (16*v) 1) v 16 Lside cut hwhole hcontacts hdisjoint hag hagz hzg
    (fun t=>(hcap t).1) (fun t=>(hcap t).2.1)
    hv.le (by norm_num)
    (by have H:=min_le_left (16*v) 1;have hu:=a.data.hU; nlinarith)
    (fun t=>t.property.2.1) (fun t=>t.property.2.2)
    (by positivity) (by rw [hagmass,hzgmass];have H:=min_le_left (16*v) 1;linarith)
    (by positivity) (by rw [hagmass];linarith) hY (by rw [hzgmass]) hv (by norm_num)
    (fun t=>(hcap t).2.2.1) (fun t=>(hcap t).2.2.2) hLside hcut hlogcut
  change (∫u in 0..1,(P.retainedSupport c ag zg).indicator (fun _=>1) (m.R u)*m.thermal u)  ≤  _
  exact H.trans_eq (by
    dsimp only [ActualThetaZeroOverlapMinimum.canonicalOptimizedBudgetY2,
      ActualThetaZeroOverlapMinimum.canonicalOrdinaryMassBudget,
      ActualThetaZeroOverlapMinimum.canonicalMassPower,
      ActualThetaZeroOverlapMinimum.canonicalMassHeight,
      ActualThetaZeroOverlapMinimum.canonicalMassReverse,
      zg,m]
    rfl)

end OAI.SKFluctuations.LaplaceWindowFormalization
