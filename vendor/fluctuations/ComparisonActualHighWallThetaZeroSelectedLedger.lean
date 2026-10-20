module

public import ComparisonActualHighWallThetaZeroSelectedMaster
public import ComparisonActualHighWallThetaZeroRetainedConditionalAssembly
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

abbrev as (j : ℕ):=finiteCutMasses M.nodes (M.sampler j)
abbrev ho (j : ℕ):=finiteCutMasses_ordered M.nodes M.bound (M.sampler j)
abbrev he (j : ℕ):=finiteCutMasses_end M.nodes M.bound (M.sampler j)
def mesh (j : ℕ) : ℝ:=((M.sampler j+1:ℕ):ℝ)⁻¹
abbrev hmesh (j : ℕ):=finiteCutMasses_mesh M.nodes M.bound (M.sampler j)
theorem mesh_nonneg (j : ℕ) : 0 ≤ M.mesh j:=by unfold mesh;positivity
theorem mesh_tendsto : Tendsto M.mesh atTop (𝓝 0):=uniformMasses_mesh_tendsto.comp M.strict.tendsto_atTop

abbrev bin (j : ℕ) (b : Fin bins):=P.retainedBin c Dcuts ag zg (M.as j) bins w b
abbrev co (j : ℕ) (b : Fin bins):=P.retainedBinCoordinates c Dcuts ag zg (M.as j) (M.ho j) bins w b
def width (j : ℕ) (b : Fin bins) : ℝ:=(M.co j b).x (M.co j b).K

def selected {B : ℕ} (label : Fin B→Fin bins) (j : ℕ):=
  Finset.univ.biUnion (fun b=>M.bin j (label b))

def defect {B : ℕ} (label : Fin B→Fin bins) (j : ℕ) : ℝ:=
  let m:=Qwall.shiftedNativeModel
  let steps:=sampleClockSteps m.q 0 (M.as j)
  ∑i,physicalSelectedCellMass steps (M.selected label j) i*
    actualCutReplicaDefect (n+1) steps (m.q 0) i.val
      (physicalPathSecondMoment (n+1) steps (m.q 0) i.val)

def sideFilled {B : ℕ} (label : Fin B→Fin bins) (dphys : ℕ)
    (e : Fin (dphys+1)≃FeatureIndex (n+1)) (j : ℕ) : ℝ:=
  let m:=Qwall.shiftedNativeModel
  ∑b,(2*(∫r,deriv Qwall.alpha.val.val r*m.unitColumn (M.as j) (M.bin j (label b))
    (M.co j (label b)).unit (fun u=>sideSquareColumn (M.co j (label b)).x cut
      (M.width j (label b)) u.val) r∂m.radiusMeasure dphys e (M.as j) (M.ho j))+
    4*M.mesh j/cut)/Qwall.alpha.val.val ag

def unionFilled {B : ℕ} (label : Fin B→Fin bins) (dphys : ℕ)
    (e : Fin (dphys+1)≃FeatureIndex (n+1)) (j : ℕ) : ℝ:=
  let m:=Qwall.shiftedNativeModel
  (2*(∫r,deriv Qwall.alpha.val.val r*m.unitColumn (M.as j) (M.selected label j)
    (fun _=>(0:Fin 1)) (fun _=>1) r∂m.radiusMeasure dphys e (M.as j) (M.ho j))+
    2*M.mesh j)/(Qwall.alpha.val.val ag)^2

def diameter (v K : ℝ) (j : ℕ) : ℝ:=Qwall.localCapDiameter v K+
  2*(M.mesh j*(2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) Qwall.shiftedNativeModel.q))

def rawValue (j : ℕ) : ℝ:=physicalRawRatio (n+1) ell
  (sampleClockSteps Qwall.shiftedNativeModel.q 0 (M.as j)) 0 Qwall.xs
  (Measure.pi fun k=>gaussianReal 0 (Qwall.shiftedNativeModel.q 0 k)) id measurable_id

theorem bin_disjoint {B : ℕ} (label : Fin B→Fin bins) (hlabel : Function.Injective label) (j : ℕ) :
    Pairwise (fun b d=>Disjoint (M.bin j (label b)) (M.bin j (label d))) := by
  intro b d hbd
  apply Finset.disjoint_left.mpr
  intro i hi hd
  have HI:=(Finset.mem_filter.mp hi).2
  have HD:=(Finset.mem_filter.mp hd).2
  exact (hlabel.ne hbd) (Fin.ext (HI.symm.trans HD))

theorem finite_budget
    (hwhole : ∀t,∀r∈Ioo (c t).left (c t).right,wholeUnit P.negativeSet r=Ioo (c t).left (c t).right)
    (hcontacts : ∀t,P.H (c t).left=0 ∧
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
      (w+M.diameter v K j) (M.sideFilled label dphys e j) (M.unionFilled label dphys e j)
      ((M.diameter v K j)^(((ell:ℝ)-2)/((ell:ℝ)-1))*
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
  have HF:=P.retained_conditional_finite_assembly c hwhole hcontacts Dcuts hag hzg hN hlog hnd
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

theorem width_mem (j : ℕ) (b : Fin bins) : M.width j b∈Icc (0:ℝ) 1:=by
  unfold width
  rw [(M.co j b).width]
  exact physicalWindowMass_mem_Icc_one _ (sampleClockSteps_ordered _ _ (M.ho j)) _

theorem total_width_tendsto {B : ℕ} (label : Fin B→Fin bins) :
    Tendsto (fun j=>∑b,M.width j (label b)) atTop (𝓝 (∑b,M.f (label b) ⟨1,by simp⟩)):=
  tendsto_finsetSum Finset.univ (fun b _=>M.widths (label b))

theorem width_limit_mem (b : Fin bins) : M.f b ⟨1,by simp⟩∈Icc (0:ℝ) 1:=
  ⟨ge_of_tendsto (M.widths b) (Eventually.of_forall (fun j=>(M.width_mem j b).1)),
    le_of_tendsto (M.widths b) (Eventually.of_forall (fun j=>(M.width_mem j b).2))⟩

theorem diameter_tendsto (v K : ℝ) :
    Tendsto (M.diameter v K) atTop (𝓝 (Qwall.localCapDiameter v K)):=by
  have HH:=(M.mesh_tendsto.mul_const
    (2*ClockTree.errorJetVariation 2 0 0*clockVariationBound (physicalFeatureCoordinateBound n)
      Qwall.shiftedNativeModel.q)).const_mul 2
  change Tendsto (fun j=>Qwall.localCapDiameter v K+2*(M.mesh j*(2*ClockTree.errorJetVariation 2 0 0*
    clockVariationBound (physicalFeatureCoordinateBound n) Qwall.shiftedNativeModel.q))) atTop (𝓝 _)
  simpa only [mul_zero,zero_mul,add_zero] using HH.const_add (Qwall.localCapDiameter v K)

theorem diameter_nonneg {v K : ℝ} (hv : 0<v) (hK : 0<K)
    (hlog : 0 ≤ Real.log Qwall.data.N) (j : ℕ) : 0 ≤ M.diameter v K j:=by
  have hD : 0 ≤ Qwall.localCapDiameter v K:=by
    unfold ActualThetaZeroOverlapMinimum.localCapDiameter
    have hE:=Qwall.data.hE
    have hN:=Qwall.data.hN
    have hd:=Qwall.data.hd
    positivity
  have hJet:=ClockTree.errorJetVariation_nonneg 2 0 0
  have hClock:=clockVariationBound_nonneg (physicalFeatureCoordinateBound n)
    Qwall.shiftedNativeModel.q (completedPathClock_monotone (n+1) Qwall.shiftedNativeModel.hbf Qwall.shiftedNativeModel.hhf)
  have hm0:=M.mesh_nonneg j
  unfold diameter
  positivity

theorem rawValue_nonneg (j : ℕ) : 0 ≤ M.rawValue j:=
  zero_le_one.trans (physicalRawRatio_one_le _ _ _ _ _ _ _ _)

end ActualThetaZeroOverlapMinimum.SelectedMasterFamily
end OAI.SKFluctuations.LaplaceWindowFormalization
