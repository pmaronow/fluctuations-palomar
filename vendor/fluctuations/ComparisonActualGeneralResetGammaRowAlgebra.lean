module

public import ComparisonActualGeneralResetPairedValue
public import ComparisonSignedCavityResetPairedRowAlgebra

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_general_reset_paired_value_diagonal (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    (bf hf : ℝ→ℝ≥0)
    (p : MarkedPlacement T) (q : ℕ→RestCoordinate n→ℝ) (d : ℕ) (center : ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (hd : p.embed P.target=p.mark) :
    actualGeneralResetPairedProjectionValue n T P bf hf p q d center=0 := by
  simp only [actualGeneralResetPairedProjectionValue,p.restRestrict_at,MarkedPlacement.restSpin,
    hd,sub_self,zero_mul]
  rw [native_star_field_disorder_field_independent _ _ _ (restWeight_pos n) (restFeature n) ho]
  simp [ClockTree.disorderExpect]

def actualGeneralResetProjectedGammaRow (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    (bf hf : ℝ→ℝ≥0) (radius : ℝ→ℝ)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (d : ℕ) (center : ℝ) : ℝ :=
  ((T.markedAttach 0).map fun p=>p.coeff*
    fullScalarCutGamma p.tree U K (p.embed P.target) p.mark*
    (if U ≤ p.tree.splitIndex (p.embed P.target) p.mark ∧
        V ≤ radius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) then
      actualGeneralResetPairedProjectionValue n T P bf hf p q d center else 0)).sum

theorem actual_general_reset_projected_gamma_row_abs_le (n : ℕ) {pre mid tail : List PositiveMass}
    (T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (P : NativeGeneratedTest T)
    (bf hf : ℝ→ℝ≥0) (radius : ℝ→ℝ)
    (U : ℕ) (V : ℝ) (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) (d : ℕ) (center : ℝ)
    (ho : MassOrdered 0 (pre++(mid++tail))) (ε Ai Ap p0 : ℝ) (fi fp : ℕ→ℝ)
    (hε : 0 ≤ ε) (hAi : 0 ≤ Ai) (hAp : 0 ≤ Ap) (hp0 : 0 ≤ p0)
    (hfi : ∀j,0 ≤ fi j) (hfp : ∀j,0 ≤ fp j)
    (hF : ∀p∈T.markedAttach 0,U ≤ p.tree.splitIndex (p.embed P.target) p.mark →
      V ≤ radius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) →
      |actualGeneralResetPairedProjectionValue n T P bf hf p q d center| ≤
        ε*(Ai*fi (p.tree.splitIndex (p.embed P.target) p.mark)+
          Ap*fp (p.tree.splitIndex (p.embed P.target) p.mark))*p0) :
    |actualGeneralResetProjectedGammaRow n T P bf hf radius U V q K d center| ≤
      ε*(Ai*((T.markedAttach 0).map (fun p=>|p.coeff| *|fullScalarCutGamma p.tree U K (p.embed P.target) p.mark| *
        nativeTargetOffDiagonalProfile T P.target
          (fun j=>if V ≤ radius (partitionPoint 0 (pre++(mid++tail)) j) then fi j else 0) p)).sum+
        Ap*((T.markedAttach 0).map (fun p=>|p.coeff| *|fullScalarCutGamma p.tree U K (p.embed P.target) p.mark| *
        nativeTargetOffDiagonalProfile T P.target
          (fun j=>if V ≤ radius (partitionPoint 0 (pre++(mid++tail)) j) then fp j else 0) p)).sum)*p0 := by
  have H:=native_paired_list_row_abs_le (T.markedAttach 0)
    (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed P.target) p.mark)
    (fun p=>if U ≤ p.tree.splitIndex (p.embed P.target) p.mark ∧
        V ≤ radius (partitionPoint 0 (pre++(mid++tail)) (p.tree.splitIndex (p.embed P.target) p.mark)) then
      actualGeneralResetPairedProjectionValue n T P bf hf p q d center else 0)
    (nativeTargetOffDiagonalProfile T P.target
      (fun j=>if V ≤ radius (partitionPoint 0 (pre++(mid++tail)) j) then fi j else 0))
    (nativeTargetOffDiagonalProfile T P.target
      (fun j=>if V ≤ radius (partitionPoint 0 (pre++(mid++tail)) j) then fp j else 0)) ε Ai Ap p0 (by
        intro p hp
        unfold nativeTargetOffDiagonalProfile
        by_cases hd:p.embed P.target=p.mark
        · simp only [hd,ite_true,actual_general_reset_paired_value_diagonal n T P bf hf p q d center ho hd]
          split_ifs <;> simp
        · simp only [hd,ite_false]
          split_ifs with hhigh hrad hrad
          · exact hF p hp hhigh.1 hhigh.2
          · exact False.elim (hrad hhigh.2)
          · simp only [abs_zero]
            exact mul_nonneg (mul_nonneg hε (add_nonneg (mul_nonneg hAi (hfi _)) (mul_nonneg hAp (hfp _)))) hp0
          · simp)
  simpa only [actualGeneralResetProjectedGammaRow,abs_mul] using H

end OAI.SKFluctuations.Cavity
