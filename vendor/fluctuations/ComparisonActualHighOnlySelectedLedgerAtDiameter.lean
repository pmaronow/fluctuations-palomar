module

public import ComparisonActualHighOnlySelectedLedger
public import ComparisonActualHighOnlyConditionalAtDiameter
public import ComparisonActualConditionalLedgerLimit

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory ProbabilityTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 22000000
set_option linter.unusedVariables false
attribute [local instance] Classical.propDecidable
namespace ActualHighOnlyOverlapMinimum.SelectedMasterFamily
variable {n : ℕ} {margin delta cl cu Az C0 Ct D Bclock : ℝ}
variable {a : ActualHighOnlyOverlapMinimum (n+1) margin delta cl cu Az C0 Ct D Bclock}
variable {P : a.Potential} {ι : Type*} {c : ι→ShiftedCapInterval a P}
variable {Dcuts : Finset ℝ} {ag zg w cut Q : ℝ} {bins ell : ℕ} {hbins : 0<bins}
variable (M : SelectedMasterFamily a P c Dcuts ag zg bins hbins w cut ell Q)

def diameterAt (baseDiameter : ℝ) (j : ℕ) : ℝ:=baseDiameter+
  2*(M.mesh j*(2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) a.shiftedNativeModel.q))

theorem diameterAt_tendsto (baseDiameter : ℝ) :
    Tendsto (M.diameterAt baseDiameter) atTop (𝓝 baseDiameter) := by
  have HH:=(M.mesh_tendsto.mul_const
    (2*ClockTree.errorJetVariation 2 0 0*clockVariationBound (physicalFeatureCoordinateBound n)
      a.shiftedNativeModel.q)).const_mul 2
  change Tendsto (fun j=>baseDiameter+2*(M.mesh j*(2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) a.shiftedNativeModel.q))) atTop (𝓝 _)
  simpa only [mul_zero,zero_mul,add_zero] using HH.const_add baseDiameter

theorem diameterAt_nonneg {baseDiameter : ℝ} (hbaseDiameter : 0 ≤ baseDiameter) (j : ℕ) :
    0 ≤ M.diameterAt baseDiameter j := by
  have hJet:=ClockTree.errorJetVariation_nonneg 2 0 0
  have hClock:=clockVariationBound_nonneg (physicalFeatureCoordinateBound n)
    a.shiftedNativeModel.q (completedPathClock_monotone (n+1) a.shiftedNativeModel.hbf a.shiftedNativeModel.hhf)
  have hm0:=M.mesh_nonneg j
  unfold diameterAt
  positivity

theorem finite_budget_at_diameter
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,(P.H (c t).left=0 ∨ (c t).left=0) ∧ (P.H (c t).right=0 ∨ (c t).right=1))
    (hag : (0:ℝ)<ag) (hzg : zg ≤ 1)
    (hN : 1 ≤ a.data.N) (hlog : 1 ≤ Real.log a.data.N) (hnd : 1/a.data.N ≤ a.data.d)
    {v K : ℝ} (hv : 0<v) (hK : 0<K)
    (hleft : ∀t,v ≤ a.alpha.val.val (c t).left+comparisonSmallMass a.data.N a.data.E)
    (hspan : ∀t,a.alpha.val.val (c t).right-a.alpha.val.val (c t).left ≤ K*v)
    (baseDiameter : ℝ) (hbaseDiameter : 0 ≤ baseDiameter)
    (hinc : ∀t,∀s∈Ioo (c t).left (c t).right,∀r∈Ioo (c t).left (c t).right,s ≤ r →
      a.radiusS r-a.radiusS s ≤ baseDiameter)
    (hell : 2<ell) {B : ℕ} (hB : 0<B) (label : Fin B→Fin bins) (hlabel : Function.Injective label)
    (hkept : ∀b,M.keep (label b)=true) {y Lside : ℝ}
    (hy : 0 ≤ y) (hw : 0<w) (hcut : 0<cut) (hLside : 0 ≤ Lside)
    (hY : a.xs+a.alpha.val.val zg ≤ y) (hRange : Q^2*y ≤ (bins:ℝ)*w)
    (hlogcut : Real.log (1/cut) ≤ Lside) (dphys : ℕ) (e : Fin (dphys+1)≃FeatureIndex (n+1)) (j : ℕ) :
    M.defect label j ≤ nativeConditionalLedgerBudget B (∑b,M.width j (label b)) cut
      (w+M.diameterAt baseDiameter j) (M.sideFilled label dphys e j) (M.unionFilled label dphys e j)
      ((M.diameterAt baseDiameter j)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
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
  have HF:=P.retained_conditional_finite_assembly_at_diameter c hwhole hcontacts Dcuts hag hzg hN hlog hnd
    hv hK hleft hspan baseDiameter hbaseDiameter hinc ell hell (M.as j) (M.ho j) (M.he j) (M.hmesh j) (M.mesh_nonneg j)
    hB label hlabel hw hcut hLside hY hheight hwidth hsideLog dphys e
  dsimp only at HF
  have HD : (∑i,(∑b,physicalSelectedCellMass (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j))
      (M.bin j (label b)) i)*actualCutReplicaDefect (n+1)
        (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j)) (a.shiftedNativeModel.q 0) i.val
        (physicalPathSecondMoment (n+1) (sampleClockSteps a.shiftedNativeModel.q 0 (M.as j))
          (a.shiftedNativeModel.q 0) i.val))=M.defect label j:=by
    unfold defect selected
    apply Finset.sum_congr rfl
    intro i _
    rw [selectedCellMass_sum_eq_biUnion _ _ (M.bin_disjoint label hlabel j)]
  rw [HD] at HF
  exact HF

end ActualHighOnlyOverlapMinimum.SelectedMasterFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
