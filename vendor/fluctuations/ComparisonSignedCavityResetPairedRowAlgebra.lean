module

public import ComparisonSignedCavityActualResetAllNormalizedRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem native_reset_paired_value_diagonal (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (p : MarkedPlacement T) (q : ℕ→RestCoordinate n→ℝ) (d : ℕ) (center : ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hd : p.embed P.target=p.mark) :
    nativeResetPairedProjectionValue n T P M p q d center=0 := by
  simp only [nativeResetPairedProjectionValue,p.restRestrict_at,MarkedPlacement.restSpin,
    hd,sub_self,zero_mul]
  rw [native_star_field_disorder_field_independent _ _ _ (restWeight_pos n) (restFeature n) ho]
  simp [ClockTree.disorderExpect]

theorem native_paired_list_row_abs_le {A : Type} (L : List A) (c F fi fp : A→ℝ)
    (ε Ai Ap P : ℝ)
    (hF : ∀a∈L,|F a| ≤ ε*(Ai*fi a+Ap*fp a)*P) :
    |(L.map (fun a=>c a*F a)).sum| ≤
      ε*(Ai*(L.map (fun a=>|c a| *fi a)).sum+Ap*(L.map (fun a=>|c a| *fp a)).sum)*P := by
  induction L with
  | nil=>simp
  | cons a L ih=>
    simp only [List.map_cons,List.sum_cons]
    have H:=hF a List.mem_cons_self
    have HL:=ih (fun b hb=>hF b (List.mem_cons_of_mem a hb))
    calc
      _ ≤ |c a*F a|+|(L.map (fun a=>c a*F a)).sum|:=abs_add_le _ _
      _ ≤ |c a| *(ε*(Ai*fi a+Ap*fp a)*P)+
          ε*(Ai*(L.map (fun a=>|c a| *fi a)).sum+Ap*(L.map (fun a=>|c a| *fp a)).sum)*P := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left H (abs_nonneg _)) HL
      _=_:=by ring

def nativeResetProjectedGammaRow (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (d : ℕ) (center : ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed P.target) p.mark*
    (if U ≤ p.tree.splitIndex (p.embed P.target) p.mark ∧
        V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) then
      nativeResetPairedProjectionValue n T P M p q d center else 0)).sum

theorem native_reset_projected_gamma_row_abs_le (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (d : ℕ) (center : ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (ε Ai Ap p0 : ℝ) (fi fp : ℕ→ℝ)
    (hε : 0 ≤ ε) (hAi : 0 ≤ Ai) (hAp : 0 ≤ Ap) (hp0 : 0 ≤ p0)
    (hfi : ∀j,0 ≤ fi j) (hfp : ∀j,0 ≤ fp j)
    (hF : ∀p∈T.markedAttach 0,U ≤ p.tree.splitIndex (p.embed P.target) p.mark →
      V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) →
      |nativeResetPairedProjectionValue n T P M p q d center| ≤
        ε*(Ai*fi (p.tree.splitIndex (p.embed P.target) p.mark)+
          Ap*fp (p.tree.splitIndex (p.embed P.target) p.mark))*p0) :
    |nativeResetProjectedGammaRow n T P M U V q K d center| ≤
      ε*(Ai*((T.markedAttach 0).map (fun p=>|p.coeff| *|fullScalarCutGamma p.tree U K (p.embed P.target) p.mark| *
        nativeTargetOffDiagonalProfile T P.target
          (fun j=>if V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) j) then fi j else 0) p)).sum+
        Ap*((T.markedAttach 0).map (fun p=>|p.coeff| *|fullScalarCutGamma p.tree U K (p.embed P.target) p.mark| *
        nativeTargetOffDiagonalProfile T P.target
          (fun j=>if V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) j) then fp j else 0) p)).sum)*p0 := by
  have H:=native_paired_list_row_abs_le (T.markedAttach 0)
    (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed P.target) p.mark)
    (fun p=>if U ≤ p.tree.splitIndex (p.embed P.target) p.mark ∧
        V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) then
      nativeResetPairedProjectionValue n T P M p q d center else 0)
    (nativeTargetOffDiagonalProfile T P.target
      (fun j=>if V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) j) then fi j else 0))
    (nativeTargetOffDiagonalProfile T P.target
      (fun j=>if V ≤ M.R (partitionPoint 0 (pre++(mid++tail)) j) then fp j else 0)) ε Ai Ap p0 (by
        intro p hp
        unfold nativeTargetOffDiagonalProfile
        by_cases hd:p.embed P.target=p.mark
        · simp only [hd,ite_true,native_reset_paired_value_diagonal n T P M p q d center ho hd]
          split_ifs <;> simp
        · simp only [hd,ite_false]
          split_ifs with hhigh hrad hrad
          · exact hF p hp hhigh.1 hhigh.2
          · exact False.elim (hrad hhigh.2)
          · simp only [abs_zero]
            exact mul_nonneg (mul_nonneg hε (add_nonneg (mul_nonneg hAi (hfi _)) (mul_nonneg hAp (hfp _)))) hp0
          · simp)
  simpa only [nativeResetProjectedGammaRow,abs_mul] using H

end OAI.SKFluctuations.Cavity
