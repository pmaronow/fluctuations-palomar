module

public import SKProof.Port.ComparisonActualOriginalQActualTripleGValue
public import ComparisonSignedCavityGTripleRowAlgebra
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 20000000
open scoped BigOperators
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeActualTripleSpineGRow_original_q
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) : ℝ :=
  ((B.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      ((r.tree.markedAttach 0).map (fun z=>z.coeff*
        (if U≤p.tree.splitIndex (p.embed base.target) p.mark ∧
            U≤r.tree.splitIndex (r.embed (p.embed base.target)) r.mark ∧
            U≤z.tree.splitIndex (z.embed (r.embed (p.embed base.target))) z.mark ∧
            z.embed r.mark≠z.mark ∧ p.embed base.target≠p.mark ∧
            V≤M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed base.target) p.mark))
          then nativeActualTripleSpineGValue_original_q spine M U p r z q else 0))).sum)).sum)).sum

theorem native_actual_triple_spine_G_row_abs_le_original_q
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) {rBound : ℕ} (hleaf : B.leaves≤rBound)
    (ε Ai Ap p0 : ℝ) (fi fp : ℕ→ℝ)
    (hε : 0≤ε) (hAi : 0≤Ai) (hAp : 0≤Ap) (hp0 : 0≤p0)
    (hfi : ∀j,0≤fi j) (hfp : ∀j,0≤fp j)
    (hF : ∀p∈B.markedAttach 0,∀r∈p.tree.markedAttach 0,∀z∈r.tree.markedAttach 0,
      U≤p.tree.splitIndex (p.embed base.target) p.mark →
      U≤r.tree.splitIndex (r.embed (p.embed base.target)) r.mark →
      U≤z.tree.splitIndex (z.embed (r.embed (p.embed base.target))) z.mark →
      z.embed r.mark≠z.mark → p.embed base.target≠p.mark →
      V≤M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed base.target) p.mark)) →
      |nativeActualTripleSpineGValue_original_q spine M U p r z q|≤
        M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed base.target) p.mark))*
          (ε*(Ai*fi (p.tree.splitIndex (p.embed base.target) p.mark)+
            Ap*fp (p.tree.splitIndex (p.embed base.target) p.mark))*p0)) :
    |nativeActualTripleSpineGRow_original_q spine M U V q| ≤
      (4*((rBound:ℝ)+1)*(rBound+2))*ε*
        (Ai*((B.markedAttach 0).map (fun p=>|p.coeff| *
          M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed base.target) p.mark))*
          nativeTargetOffDiagonalProfile B base.target
            (fun j=>if V≤M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) j) then fi j else 0) p)).sum+
         Ap*((B.markedAttach 0).map (fun p=>|p.coeff| *
          M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed base.target) p.mark))*
          nativeTargetOffDiagonalProfile B base.target
            (fun j=>if V≤M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) j) then fp j else 0) p)).sum)*p0 := by
  let R:=fun j=>M.sweepRadius (partitionPoint 0 (pre++(mid++tail)) j)
  let fI:=nativeTargetOffDiagonalProfile B base.target (fun j=>if V≤R j then fi j else 0)
  let fP:=nativeTargetOffDiagonalProfile B base.target (fun j=>if V≤R j then fp j else 0)
  have hR (j) : 0≤R j:=
    (M.R_bounds _).1
  have hI (p : MarkedPlacement B) : 0≤fI p:=by
    unfold fI nativeTargetOffDiagonalProfile
    dsimp only
    split_ifs <;> first | exact le_refl 0 | exact hfi _
  have hP (p : MarkedPlacement B) : 0≤fP p:=by
    unfold fP nativeTargetOffDiagonalProfile
    dsimp only
    split_ifs <;> first | exact le_refl 0 | exact hfp _
  have H:=native_three_marked_row_abs_le_outer B ho hleaf
    (fun p r z=>if U≤p.tree.splitIndex (p.embed base.target) p.mark ∧
        U≤r.tree.splitIndex (r.embed (p.embed base.target)) r.mark ∧
        U≤z.tree.splitIndex (z.embed (r.embed (p.embed base.target))) z.mark ∧
        z.embed r.mark≠z.mark ∧ p.embed base.target≠p.mark ∧
        V≤R (p.tree.splitIndex (p.embed base.target) p.mark)
      then nativeActualTripleSpineGValue_original_q spine M U p r z q else 0)
    (fun p=>R (p.tree.splitIndex (p.embed base.target) p.mark)*(ε*(Ai*fI p+Ap*fP p)*p0))
    (by intro p _;exact mul_nonneg (hR _) (mul_nonneg
      (mul_nonneg hε (add_nonneg (mul_nonneg hAi (hI p)) (mul_nonneg hAp (hP p)))) hp0)) (by
      intro p hp r hr z hz
      split_ifs with HH
      · simpa only [fI,fP,nativeTargetOffDiagonalProfile,ite_eq_right HH.2.2.2.2.1,
          ite_eq_left HH.2.2.2.2.2] using hF p hp r hr z hz HH.1 HH.2.1 HH.2.2.1
            HH.2.2.2.1 HH.2.2.2.2.1 HH.2.2.2.2.2
      · rw [abs_zero]
        exact mul_nonneg (hR _) (mul_nonneg
          (mul_nonneg hε (add_nonneg (mul_nonneg hAi (hI p)) (mul_nonneg hAp (hP p)))) hp0))
  apply H.trans_eq
  have HE (L : List (MarkedPlacement B)) :
      (L.map (fun p=>|p.coeff| *(R (p.tree.splitIndex (p.embed base.target) p.mark)*(ε*(Ai*fI p+Ap*fP p)*p0)))).sum=
      ε*(Ai*(L.map (fun p=>|p.coeff| *R (p.tree.splitIndex (p.embed base.target) p.mark)*fI p)).sum+
        Ap*(L.map (fun p=>|p.coeff| *R (p.tree.splitIndex (p.embed base.target) p.mark)*fP p)).sum)*p0 := by
    induction L with
    | nil=>simp
    | cons p L ih=>simp only [List.map_cons,List.sum_cons,ih];ring
  rw [HE]
  dsimp only [R,fI,fP]
  ring

end OAI.SKFluctuations.Cavity
