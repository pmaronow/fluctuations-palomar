module

public import ComparisonActualGeneralFourFirstHighIteration
public import ComparisonSignedCavityGProjectedRestorationSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000

theorem actual_general_four_other_source_sum_abs_le_of_original_profiles
    {n : ℕ} (bf hf : ℝ→ℝ≥0) {as : List PositiveMass} {i star U : ℕ}
    (W seedScale C : ℝ) (f R : ℕ→ℝ)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    (H : ∀Q∈rows,|(W⁻¹)^Q.generation*actualGeneralFourOtherSourceErrorContrast bf hf U Q| ≤
      |Q.term.coefficient| *seedScale*C*(W^3+
        W*(Q.tree.forkCost f+edgeBudget 0 as f)+W^2*(Q.tree.forkCost R+edgeBudget 0 as R))) :
    |actualGeneralFourOtherSourceErrorSum bf hf U W rows| ≤
      seedScale*C*(W^3*(rows.map (fun Q=>|Q.term.coefficient|)).sum+
        W*(rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum+
        W^2*(rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum) := by
  have HE : (rows.map (fun Q=>|Q.term.coefficient| *seedScale*C*(W^3+
      W*(Q.tree.forkCost f+edgeBudget 0 as f)+W^2*(Q.tree.forkCost R+edgeBudget 0 as R)))).sum=
    seedScale*C*(W^3*(rows.map (fun Q=>|Q.term.coefficient|)).sum+
      W*(rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost f+edgeBudget 0 as f))).sum+
      W^2*(rows.map (fun Q=>|Q.term.coefficient| *(Q.tree.forkCost R+edgeBudget 0 as R))).sum) := by
    clear H
    induction rows with
    | nil=> simp
    | cons Q rows ih=> simp only [List.map_cons,List.sum_cons] at ih ⊢;rw [ih];ring
  exact (native_abs_sum_map_le _ _).trans ((List.sum_le_sum H).trans_eq HE)

theorem actual_general_high_whole_profile_linear
    {S : Type} {as : List PositiveMass} (T : ClockTree S as) (f R : ℕ→ℝ) (W : ℝ) :
    T.forkCost (fun l=> f l+W*R l)+edgeBudget 0 as (fun l=> f l+W*R l)=
      T.forkCost f+edgeBudget 0 as f+W*(T.forkCost R+edgeBudget 0 as R) := by
  simpa only [one_mul] using (show
    T.forkCost (fun l=> 1*f l+W*R l)+edgeBudget 0 as (fun l=> 1*f l+W*R l)=
      T.forkCost f+edgeBudget 0 as f+W*(T.forkCost R+edgeBudget 0 as R) from by
        rw [native_forkCost_test_linear,native_edgeBudget_test_linear];ring)

theorem actual_general_four_other_source_sum_abs_le_of_profile_and_variation
    {n : ℕ} (bf hf : ℝ→ℝ≥0) {as : List PositiveMass} {i star U : ℕ}
    (ho : MassOrdered 0 as) {W seedScale C Vcoef Vprofile : ℝ}
    (hW : 0< W) (hscale : 0≤ seedScale) (hC : 0≤ C)
    (f R : ℕ→ℝ) (hfn : ∀l,0≤ f l) (_hR : ∀l,0≤ R l)
    (rows : List (NativeActualResourceState (Spin n×Bool) as i star))
    (H : ∀Q∈rows,|(W⁻¹)^Q.generation*actualGeneralFourOtherSourceErrorContrast bf hf U Q| ≤
      |Q.term.coefficient| *seedScale*C*(W^3+
        W*(Q.tree.forkCost (fun l=> f l+W*R l)+edgeBudget 0 as (fun l=> f l+W*R l))+
          W^2*(Q.tree.forkCost R+edgeBudget 0 as R)))
    (Hcoef : (rows.map (fun Q=>|Q.term.coefficient|)).sum≤ Vcoef)
    (Hprofile : (rows.map (fun Q=>|Q.term.coefficient| *
      (Q.tree.forkCost (fun l=> f l+W*R l)+edgeBudget 0 as (fun l=> f l+W*R l)))).sum≤ Vprofile) :
    |actualGeneralFourOtherSourceErrorSum bf hf U W rows|≤
      seedScale*C*(W^3*Vcoef+2*W*Vprofile) := by
  have Hlocal Q (_hQ : Q∈rows) : W*(|Q.term.coefficient| *
      (Q.tree.forkCost R+edgeBudget 0 as R))≤
        |Q.term.coefficient| *(Q.tree.forkCost (fun l=> f l+W*R l)+
          edgeBudget 0 as (fun l=> f l+W*R l)):=by
    rw [actual_general_high_whole_profile_linear]
    have Hf:=mul_nonneg (abs_nonneg Q.term.coefficient)
      (add_nonneg (Q.tree.forkCost_nonneg hfn) (edgeBudget_nonneg ho hfn))
    nlinarith only [Hf]
  have Hsum:=List.sum_le_sum Hlocal
  rw [List.sum_map_mul_left] at Hsum
  have Htotal:=actual_general_four_other_source_sum_abs_le_of_original_profiles
    bf hf W seedScale C (fun l=> f l+W*R l) R rows H
  apply Htotal.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hscale hC)
  have HV:=mul_le_mul_of_nonneg_left Hcoef (pow_nonneg hW.le 3)
  have HP:=mul_le_mul_of_nonneg_left Hprofile hW.le
  have HR:=mul_le_mul_of_nonneg_left (Hsum.trans Hprofile) hW.le
  nlinarith only [HV,HP,HR]

end OAI.SKFluctuations.Cavity
