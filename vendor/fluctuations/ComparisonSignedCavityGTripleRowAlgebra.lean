module

public import ComparisonSignedCavityGWordSupport
public import ComparisonSignedCavityResetPairedRowAlgebra
public import ComparisonSignedCavityThreeRowVariation

@[expose] public section

noncomputable section
set_option maxHeartbeats 20000000
open scoped BigOperators
open Classical
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type} {as : List PositiveMass}

theorem native_three_marked_row_abs_le_outer (T : ClockTree S as) (ho : MassOrdered 0 as)
    {r : ℕ} (hleaf : T.leaves≤r)
    (F : (p : MarkedPlacement T)→(e : MarkedPlacement p.tree)→MarkedPlacement e.tree→ℝ)
    (D : MarkedPlacement T→ℝ) (hD : ∀p∈T.markedAttach 0,0≤D p)
    (hF : ∀p∈T.markedAttach 0,∀e∈p.tree.markedAttach 0,∀f∈e.tree.markedAttach 0,
      |F p e f|≤D p) :
    |((T.markedAttach 0).map (fun p=>p.coeff*
      ((p.tree.markedAttach 0).map (fun e=>e.coeff*
        ((e.tree.markedAttach 0).map (fun f=>f.coeff*F p e f)).sum)).sum)).sum| ≤
      (4*((r:ℝ)+1)*(r+2))*((T.markedAttach 0).map (fun p=>|p.coeff| *D p)).sum := by
  apply (abs_list_sum_le _).trans
  simp only [List.map_map,Function.comp_def,abs_mul]
  calc
    _ ≤ ((T.markedAttach 0).map (fun p=>|p.coeff| *((4*((r:ℝ)+1)*(r+2))*D p))).sum := by
      apply List.sum_le_sum
      intro p hp
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hpLeaf : p.tree.leaves≤r+1:=(T.markedAttach_leaves 0 p hp).trans (Nat.add_le_add_right hleaf 1)
      have H:=(p.tree.signedPair_abs_le_pairAbsSum (F p)).trans
        ((p.tree.pairAbsSum_mono (hF p hp)).trans (p.tree.pairAbsSum_constant_le ho hpLeaf (hD p hp)))
      convert H using 1
      push_cast
      ring
    _=_:=by simp only [mul_left_comm _ (4*((r:ℝ)+1)*(r+2)),List.sum_map_mul_left]

end OAI.SKFluctuations.Hierarchy.ClockTree
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

def nativeActualTripleSpineGRow
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) : ℝ :=
  ((B.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      ((r.tree.markedAttach 0).map (fun z=>z.coeff*
        (if U≤p.tree.splitIndex (p.embed base.target) p.mark ∧
            U≤r.tree.splitIndex (r.embed (p.embed base.target)) r.mark ∧
            U≤z.tree.splitIndex (z.embed (r.embed (p.embed base.target))) z.mark ∧
            z.embed r.mark≠z.mark ∧ p.embed base.target≠p.mark ∧
            V≤M.R (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed base.target) p.mark))
          then nativeActualTripleSpineGValue spine M U p r z q else 0))).sum)).sum)).sum

theorem native_actual_triple_spine_G_row_abs_le
    {n : ℕ} {pre mid tail : List PositiveMass}
    {B T : ClockTree (Spin n×Bool) (pre++(mid++tail))}
    {base : NativeGeneratedTest B} {P : NativeGeneratedTest T}
    (spine : NativeProjectionSpine base (pre.length+mid.length) P)
    {m delta cl cu Az C0 Ct D₀ Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D₀ Bclock)
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
      V≤M.R (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed base.target) p.mark)) →
      |nativeActualTripleSpineGValue spine M U p r z q|≤
        M.R (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed base.target) p.mark))*
          (ε*(Ai*fi (p.tree.splitIndex (p.embed base.target) p.mark)+
            Ap*fp (p.tree.splitIndex (p.embed base.target) p.mark))*p0)) :
    |nativeActualTripleSpineGRow spine M U V q| ≤
      (4*((rBound:ℝ)+1)*(rBound+2))*ε*
        (Ai*((B.markedAttach 0).map (fun p=>|p.coeff| *
          M.R (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed base.target) p.mark))*
          nativeTargetOffDiagonalProfile B base.target
            (fun j=>if V≤M.R (partitionPoint 0 (pre++(mid++tail)) j) then fi j else 0) p)).sum+
         Ap*((B.markedAttach 0).map (fun p=>|p.coeff| *
          M.R (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed base.target) p.mark))*
          nativeTargetOffDiagonalProfile B base.target
            (fun j=>if V≤M.R (partitionPoint 0 (pre++(mid++tail)) j) then fp j else 0) p)).sum)*p0 := by
  let R:=fun j=>M.R (partitionPoint 0 (pre++(mid++tail)) j)
  let fI:=nativeTargetOffDiagonalProfile B base.target (fun j=>if V≤R j then fi j else 0)
  let fP:=nativeTargetOffDiagonalProfile B base.target (fun j=>if V≤R j then fp j else 0)
  have hR (j) : 0≤R j:=
    (comparisonSweepQuantile_bounds M.context.hc M.context.hk M.context.hkc
      M.context.hm M.context.hM M.alpha _).1
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
      then nativeActualTripleSpineGValue spine M U p r z q else 0)
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
