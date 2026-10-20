module

public import ComparisonActualHighWallHighAllDegreeContinuumMoments
public import ComparisonSignedCavitySecondLowInheritedOriginalMeanBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_high_wall_second_low_original_mean_budget
    (degree rBound : ℕ) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp : ℝ,0 < Cp ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree → NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
          |nativeOriginalRestTestExpectation n q U b h K T (G.canonicalHighWallSource M forms).restProduct| ≤
            Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Cp^degree*M.data.d^degree := by
  obtain ⟨Cp,hCp,H⟩:=eventually_actual_high_wall_all_degree_continuum_square_even_moment
    (D:=D) degree 1 rBound (by norm_num) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,hCp,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T hT G forms hmass
  apply native_original_rest_mean_abs_le_square n _ U _ _ _ T (finiteCutMasses_ordered us hus k)
    _ (by positivity [M.data.hd])
  simpa only [ActualNaturalBoundaryShape.product_eq_restProduct,Nat.mul_one] using
    hk U T 1 1 (by norm_num) (by norm_num) hT G forms hmass

end OAI.SKFluctuations.Cavity
