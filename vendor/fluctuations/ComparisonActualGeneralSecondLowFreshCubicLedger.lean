module

public import ComparisonActualGeneralResourceFullB0Readout
public import ComparisonSignedCavitySecondLowActualFreshFullB0BudgetAlong

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_general_fresh_full_B0_abs_le_of_literal_budgets
    (n : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (ho : MassOrdered 0 as) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (s : T.Slot) (star : ℕ) (hstar : star<U) (hU : U≤as.length)
    (P : T.cavityLeft.Assignment→ℝ) {Bu Bo Bb Br : ℝ}
    (Hunobserved : ∀j : Fin 8,
      let g:=nativeFreshAtSlot T 0 s star
      |nativeSecondLowClassLedger n q U b h K g.tree hU (fun old=>P (g.restRestrict old))
        (g.embed s) g.mark j false/2|≤Bu)
    (Hobserved :
      let g:=nativeFreshAtSlot T 0 s star
      let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
      |(∑j : Fin 8,nativeSecondLowClassLedger n q U b h K g.tree hU (fun old=>P (g.restRestrict old))
        (g.embed s) g.mark j true/2)-
        χ^2*nativeSecondLowFreshOccupiedUnweightedCSource n q U b h K T s star hU P|≤Bo)
    (Hbaseline : |nativeSecondLowFreshOccupiedOldCBaselineSource n q U b h K T s star hU P|≤Bb)
    (Hreplacement : |nativeSecondLowFreshOccupiedCReplacementSource n q U b h K T s star hU P|≤Br) :
    |nativeSecondLowFreshFullB0Source n q U b h K T s star P|≤8*Bu+Bo+Bb+Br := by
  let g:=nativeFreshAtSlot T 0 s star
  let Pg:=fun old=>P (g.restRestrict old)
  let χ:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  have Hsplit : g.tree.splitIndex (g.embed s) g.mark=star:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split,T.splitIndex_self,
      Nat.min_eq_left (hstar.le.trans hU)]
  have Hjoint:=native_second_low_joint_ledger_half_eq_observed_unobserved n q U b h K g.tree
    ho hU Pg (g.embed s) g.mark (Hsplit ▸ hstar)
  have HU : |∑j : Fin 8,nativeSecondLowClassLedger n q U b h K g.tree hU Pg
      (g.embed s) g.mark j false/2|≤8*Bu:=by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply (Finset.sum_le_sum (fun j _=>Hunobserved j)).trans_eq
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat]
  have Hchi : |χ^2|≤1:=by
    rw [abs_pow]
    exact (pow_le_pow_left₀ (abs_nonneg χ) (native_second_low_original_chi_abs_le_one ho U K) 2).trans_eq
      (by norm_num)
  have Hscaled (X : ℝ) : |χ^2*X|≤|X|:=by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right Hchi (abs_nonneg _)).trans_eq (one_mul _)
  have HC : |χ^2*nativeSecondLowFreshOccupiedUnweightedCSource n q U b h K T s star hU P|≤Bb+Br:=by
    rw [native_second_low_fresh_occupied_unweighted_eq_old_baseline_add_replacement n q U b h K T ho s star hstar hU P,
      mul_add]
    apply (abs_add_le _ _).trans
    apply add_le_add
    · exact (Hscaled _).trans Hbaseline
    · exact (Hscaled _).trans Hreplacement
  have H0 : |(∑j : Fin 8,nativeSecondLowClassLedger n q U b h K g.tree hU Pg
      (g.embed s) g.mark j true/2)|≤Bo+(Bb+Br):=by
    have Hident (A B : ℝ) : A=(A-B)+B:=by ring
    rw [Hident (∑j : Fin 8,nativeSecondLowClassLedger n q U b h K g.tree hU Pg
      (g.embed s) g.mark j true/2) (χ^2*nativeSecondLowFreshOccupiedUnweightedCSource n q U b h K T s star hU P)]
    exact (abs_add_le _ _).trans (add_le_add Hobserved HC)
  change |nativeSecondLowJointLedger n q U b h K g.tree Pg [g.embed s,g.mark]/2|≤_
  rw [Hjoint]
  exact ((abs_add_le _ _).trans (add_le_add H0 HU)).trans_eq (by ring)

theorem actual_general_fresh_full_B0_sub_const
    (n : ℕ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    (s : T.Slot) (star : ℕ) (P : T.cavityLeft.Assignment→ℝ) (c : ℝ) :
    nativeSecondLowFreshFullB0Source n q U b h K T s star (fun sigma=>P sigma-c)=
      nativeSecondLowFreshFullB0Source n q U b h K T s star P-
        c*nativeSecondLowFreshFullB0Source n q U b h K T s star (fun _=>1) := by
  unfold nativeSecondLowFreshFullB0Source
  dsimp only
  rw [native_second_low_joint_ledger_sub_const]
  ring

end OAI.SKFluctuations.Cavity
