module

public import ComparisonSignedCavitySecondLowCMarkedRestProjection
public import ComparisonSignedCavitySecondLowUnweightedCRowSource
public import ComparisonSignedCavityStarFieldMeanRegularity

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false

private theorem c_coupled_clock_smooth {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ→ι→ℝ≥0) (P : T.Assignment→ℝ) : BddSmooth 0 (T.expect w φ q P) := by
  have H:T.expect w φ q P=(T.realize q).expect w φ
      (fun σ=>P ((T.assignmentEquiv q).symm σ)):=funext (T.expect_realize w φ q P)
  rw [H]
  exact (T.realize q).expect_smooth hw φ (clockSteps_ordered ho q) _ 0

private theorem c_coupled_list_smooth {ι α : Type} [Fintype ι]
    (ps : List α) (c : α→ℝ) (F : α→(ι→ℝ)→ℝ)
    (hF : ∀p∈ps,BddSmooth 0 (F p)) : BddSmooth 0 (fun x=>(ps.map (fun p=>c p*F p x)).sum) := by
  induction ps with
  | nil=>exact BddSmooth.const 0 0
  | cons p ps ih=>
    exact ((hF p List.mem_cons_self).const_mul (c p)).add
      (ih (fun r hr=>hF r (List.mem_cons_of_mem p hr)))

private theorem c_coupled_joint_rows_smooth {ι S : Type} [Fintype ι] [Fintype S] [Nonempty S]
    {w : S→ℝ} (hw : ∀σ,0<w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) {a : ℝ} (ho : MassOrdered a as)
    (q : ℕ→ι→ℝ≥0) (ps : List (MarkedPlacement T)) (H : T.Assignment→S→ℝ) :
    BddSmooth 0 (fun x=>nativeJointAttachmentRow w φ q ps H x) := by
  unfold nativeJointAttachmentRow
  exact c_coupled_list_smooth ps (fun p=>p.coeff) _
    (fun p _=>c_coupled_clock_smooth hw φ p.tree ho q _)

def nativeSecondLowUnweightedCCoupledPrefixSource
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (f c z : T.Slot) (P : T.cavityLeft.Assignment→ℝ) : ℝ :=
  let Q:=fun sf sc sz=>restLowKernel n U b h (T.splitIndex f c) sf sc*
    restLowKernel n U b h (T.splitIndex c z) sc sz-
    (if T.splitIndex f c<U then K (T.splitIndex f c) else 0)*
      (if T.splitIndex c z<U then K (T.splitIndex c z) else 0)
  ∫x,nativeSecondLowCCouplingFold (restWeight n) (restFeature n) T.cavityLeft
      (T.cavityLeftSlot c) U 0 (cumulativeIncrements (q 0) (fun j=>q (j+1))) P
      (.slot (T.cavityLeftSlot f)) (.slot (T.cavityLeftSlot z)) Q x
    ∂Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))

theorem native_second_low_original_unweighted_c_replacement_eq_coupled_prefix
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (hU0 : 0<U) (hU : U≤as.length) (f c z : T.Slot)
    (Hfc : T.splitIndex f c<U) (Hcz : T.splitIndex c z<U)
    (P : T.cavityLeft.Assignment→ℝ) :
    nativeSecondLowUnweightedCReplacementRow n q U b h K T f c z P=
      nativeSecondLowUnweightedCCoupledPrefixSource n q U b h K T f c z P := by
  let qs:=cumulativeIncrements (q 0) (fun j=>q (j+1))
  let μ:=Measure.pi (fun i=>gaussianReal 0 (Real.toNNReal (q 0 i)))
  let Q:=fun sf sc sz=>restLowKernel n U b h (T.splitIndex f c) sf sc*
    restLowKernel n U b h (T.splitIndex c z) sc sz-
    (if T.splitIndex f c<U then K (T.splitIndex f c) else 0)*
      (if T.splitIndex c z<U then K (T.splitIndex c z) else 0)
  let H:=fun σ s=>P σ*Q (T.cavityLeft.atSlot σ (T.cavityLeftSlot f)) s
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot z))
  let rows:=nativeHighMarkedRows T.cavityLeft (T.cavityLeftSlot c) (U-1) 0
  let R:=fun x=>nativeJointAttachmentRow (restWeight n) (restFeature n) qs rows H x
  let B:=fun x=>T.cavityLeft.expect (restWeight n) (restFeature n) qs
    (fun σ=>H σ (T.cavityLeft.atSlot σ (T.cavityLeftSlot c))) x
  have hR:Integrable R μ:=by
    have HH:=(c_coupled_joint_rows_smooth (restWeight_pos n) (restFeature n)
      T.cavityLeft ho qs rows H).integrable_zero_shift (ν:=μ) 0
    simpa only [zero_add] using HH
  have hB:Integrable B μ:=by
    have HH:=(c_coupled_clock_smooth (restWeight_pos n) (restFeature n) T.cavityLeft ho qs
      (fun σ=>H σ (T.cavityLeft.atSlot σ (T.cavityLeftSlot c)))).integrable_zero_shift (ν:=μ) 0
    simpa only [zero_add] using HH
  have HPayload:∀p:MarkedPlacement T,nativeSecondLowUnweightedCPayload n U b h K T f c z P p=
      fun σ=>H (p.restRestrict σ) (p.restSpin σ):=fun _=>rfl
  have Hrow:nativeSecondLowUnweightedCRow n q U b h K T f c z P=∫x,R x ∂μ:=by
    unfold nativeSecondLowUnweightedCRow
    simp_rw [HPayload,ClockTree.disorderExpect_integral (restWeight_pos n) (restFeature n) _ ho,
      zeroContinuation]
    simp only [Pi.zero_apply,sub_zero,zero_add]
    let ps:=nativeHighMarkedRows T c (U-1) 0
    have HF:∀p∈ps,Integrable (fun y=>p.coeff*p.tree.cavityLeft.expect (restWeight n) (restFeature n) qs
        (fun σ=>H (p.restRestrict σ) (p.restSpin σ)) y) μ:=by
      intro p _
      have HH:=(c_coupled_clock_smooth (restWeight_pos n) (restFeature n) p.tree.cavityLeft ho qs
        (fun σ=>H (p.restRestrict σ) (p.restSpin σ))).integrable_zero_shift (ν:=μ) 0
      have HI:Integrable (fun y=>p.tree.cavityLeft.expect (restWeight n) (restFeature n) qs
          (fun σ=>H (p.restRestrict σ) (p.restSpin σ)) y) μ:=by
        simpa only [zero_add] using HH
      exact HI.const_mul p.coeff
    have HI:=native_integral_list_sum μ ps
      (fun p y=>p.coeff*p.tree.cavityLeft.expect (restWeight n) (restFeature n) qs
        (fun σ=>H (p.restRestrict σ) (p.restSpin σ)) y) HF
    simp only [integral_const_mul] at HI
    rw [←HI]
    apply integral_congr_ae
    exact Eventually.of_forall fun x=>native_second_low_c_HIGH_rest_row_projection
      (restWeight_pos n) (restFeature n) T c (U-1) 0 ho qs H x
  have Hbase:T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
      (nativeSecondLowUnweightedCOldPayload n U b h K T f c z P) 0=∫x,B x ∂μ:=by
    rw [ClockTree.disorderExpect_integral (restWeight_pos n) (restFeature n) _ ho]
    simp only [zeroContinuation,Pi.zero_apply,sub_zero,zero_add]
    rfl
  have HE:=native_second_low_unweighted_c_eq_old_baseline_add_forest_replacement n q U b h K T ho
    hU0 hU f c z P
  have HR:nativeSecondLowUnweightedCReplacementRow n q U b h K T f c z P=
      (∫x,R x ∂μ)-partitionPoint 0 as U*(∫x,B x ∂μ):=by
    rw [Hrow,Hbase] at HE
    linarith only [HE]
  rw [HR]
  unfold nativeSecondLowUnweightedCCoupledPrefixSource
  rw [←integral_const_mul,←integral_sub hR (hB.const_mul (partitionPoint 0 as U))]
  apply integral_congr_ae
  refine Eventually.of_forall fun x=>?_
  have hf:(NativeSecondLowCReader.slot (T.cavityLeftSlot f)).low (T.cavityLeftSlot c) U:=by
    dsimp [NativeSecondLowCReader.low]
    rw [cavityLeft_splitIndex,T.splitIndex_symm c f]
    exact Hfc
  have hz:(NativeSecondLowCReader.slot (T.cavityLeftSlot z)).low (T.cavityLeftSlot c) U:=by
    dsimp [NativeSecondLowCReader.low]
    rw [cavityLeft_splitIndex]
    exact Hcz
  have HC:=native_second_low_c_coupling_fold_eq_original (restWeight_pos n) (restFeature n) T.cavityLeft
    (T.cavityLeftSlot c) U ho hU (by omega) qs P
    (.slot (T.cavityLeftSlot f)) (.slot (T.cavityLeftSlot z)) hf hz Q x
  simp only [nativeSecondLowCReplacementValue,nativeSecondLowCSourceRows,ne_of_gt hU0,
    ite_false,NativeSecondLowCReader.read] at HC
  exact HC.symm

end OAI.SKFluctuations.Cavity
