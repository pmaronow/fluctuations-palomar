module

public import ComparisonActualHighWallInitialSourceMomentInterpolation
public import ComparisonSignedCavitySecondLowInheritedOriginalMeanBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_high_wall_second_low_original_mean_initial_modulus_budget
    (degree rBound : ℕ) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp Ci : ℝ,0 < Cp ∧ 0 < Ci ∧ ∀ᶠn in atTop,
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
        ∀(G : ActualNaturalBoundaryShape n (degree+1) T) (forms : Fin (degree+1) → NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
          ∀(e0 : Fin (degree+1)) (i : ℕ),forms e0=.centered →
            T.splitIndex (G.i e0) (G.j e0)=i →
          |nativeOriginalRestTestExpectation n q U b h K T (G.canonicalHighWallSource M forms).restProduct| ≤
            Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Cp^degree*M.data.d^degree*
              (Ci*M.data.d*originalInitialLowMomentModulus
                (originalHighWallInitialPairErrorScale M as i) (Ci*M.data.d) 4) := by
  obtain ⟨Cp,Ci,hCp,hCi,H⟩:=eventually_actual_high_wall_distinguished_initial_source_moment_interpolate
    (D:=D) degree 1 rBound (by norm_num) Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Ci,hCp,hCi,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T hT G forms hmass e0 i hform hinit
  have he:=original_high_wall_initial_pair_error_scale_nonneg M (finiteCutMasses us k) i
  have hr : 0 ≤ Ci*M.data.d:=mul_nonneg hCi.le M.data.hd.le
  have heta:=original_initial_low_moment_modulus_nonneg he hr 4
  apply native_original_rest_mean_abs_le_square n _ U _ _ _ T (finiteCutMasses_ordered us hus k)
    _ (mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (pow_nonneg hCp.le degree))
      (pow_nonneg M.data.hd.le degree)) (mul_nonneg hr heta))
  simpa only [ActualNaturalBoundaryShape.product_eq_restProduct,Nat.mul_one,mul_assoc] using
    hk U T 1 1 (by norm_num) (by norm_num) hT G forms hmass e0 i hform hinit

end OAI.SKFluctuations.Cavity
