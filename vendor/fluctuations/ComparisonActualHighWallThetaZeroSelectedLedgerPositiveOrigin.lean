module

public import ComparisonActualHighWallThetaZeroSelectedLedger
public import ComparisonActualHighWallThetaZeroSelectedMasterPositiveOrigin
public import ComparisonActualHighWallThetaZeroRetainedConditionalAssemblyPositiveOrigin
public import ComparisonActualConditionalLedgerLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 24000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ActualThetaZeroOverlapMinimum.SelectedMasterFamily
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Qwall : ActualThetaZeroOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : Qwall.Potential} {ι : Type*} {c : ι→ShiftedCapInterval Qwall P}
variable {Dcuts : Finset ℝ} {ag zg w cut Q : ℝ} {bins ell : ℕ} {hbins : 0<bins}
variable (M : SelectedMasterFamily Qwall P c Dcuts ag zg bins hbins w cut ell Q)

def diameterOrigin (v K : ℝ) (j : ℕ) : ℝ:=Qwall.localCapDiameter v K+Qwall.data.rmin+
  2*(M.mesh j*(2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) Qwall.shiftedNativeModel.q))

theorem diameterOrigin_tendsto (v K : ℝ) :
    Tendsto (M.diameterOrigin v K) atTop (𝓝 (Qwall.localCapDiameter v K+Qwall.data.rmin)):=by
  have H:=(M.diameter_tendsto v K).add_const Qwall.data.rmin
  unfold diameterOrigin
  simpa only [diameter,add_right_comm] using H

theorem diameterOrigin_nonneg {v K : ℝ} (hv : 0<v) (hK : 0<K)
    (hlog : 0≤Real.log Qwall.data.N) (j : ℕ) : 0≤M.diameterOrigin v K j:=by
  have H:=add_nonneg (M.diameter_nonneg hv hK hlog j) Qwall.data.hrbounds.1.le
  simpa only [diameterOrigin,diameter,add_right_comm] using H

theorem finite_budget_positive_origin
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,(P.H (c t).left=0 ∨ (c t).left=Qwall.data.rmin) ∧
      (P.H (c t).right=0 ∨ (c t).right=1))
    (hag : Qwall.data.rmin≤ag) (hzg : zg ≤ 1)
    (hN : 1 ≤ Qwall.data.N) (hlog : 1 ≤ Real.log Qwall.data.N) (hnd : 1/Qwall.data.N ≤ Qwall.data.d)
    {v K : ℝ} (hv : 0<v) (hK : 0<K)
    (hsourceLeft : ∀t,v ≤ Qwall.alpha.val.val (c t).left+comparisonSmallMass Qwall.data.N Qwall.data.E)
    (hsourceSpan : ∀t,Qwall.alpha.val.val (c t).right-Qwall.alpha.val.val (c t).left ≤ K*v)
    (hell : 2<ell) {B : ℕ} (hB : 0<B) (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    (hkept : ∀b,M.keep (label b)=true) {y Lside : ℝ}
    (hy : 0 ≤ y) (hw : 0<w) (hcut : 0<cut) (hLside : 0 ≤ Lside)
    (hY : Qwall.xs+Qwall.alpha.val.val zg ≤ y) (hRange : Q^2*y ≤ (bins:ℝ)*w)
    (hlogcut : Real.log (1/cut) ≤ Lside) (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1)) (j : ℕ) :
    M.defect label j ≤ nativeConditionalLedgerBudget B (∑b,M.width j (label b)) cut
      (w+M.diameterOrigin v K j) (M.sideFilled label dphys e j) (M.unionFilled label dphys e j)
      ((M.diameterOrigin v K j)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
        ((2*M.rawValue j)^(2*ell)*y^ell)^(1/((ell:ℝ)-1))) Lside := by
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
  have HF:=P.retained_conditional_finite_assembly_positive_origin c hwhole hcontacts Dcuts hag hzg hN hlog hnd
    hv hK hsourceLeft hsourceSpan ell hell (M.as j) (M.ho j) (M.he j) (M.hmesh j) (M.mesh_nonneg j)
    hB label hlabel hw hcut hLside hY hheight hwidth hsideLog dphys e
  dsimp only at HF
  have HD : (∑i,(∑b,physicalSelectedCellMass (sampleClockSteps Qwall.shiftedNativeModel.q 0 (M.as j))
      (M.bin j (label b)) i)*actualCutReplicaDefect (n+1)
        (sampleClockSteps Qwall.shiftedNativeModel.q 0 (M.as j)) (Qwall.shiftedNativeModel.q 0) i.val
        (physicalPathSecondMoment (n+1) (sampleClockSteps Qwall.shiftedNativeModel.q 0 (M.as j))
          (Qwall.shiftedNativeModel.q 0) i.val))=M.defect label j:=by
    unfold defect selected
    apply Finset.sum_congr rfl
    intro i _
    rw [selectedCellMass_sum_eq_biUnion _ _ (M.bin_disjoint label hlabel j)]
  rw [HD] at HF
  exact HF

end ActualThetaZeroOverlapMinimum.SelectedMasterFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
