module

public import ComparisonActualHighWallContinuumSourceMoments
public import ComparisonSignedCavityInheritedContinuumMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_high_wall_all_degree_continuum_square_even_moment
    (aDegree d rBound : ℕ) (hd : 0 < d)
    (Bclock Cmass : ℝ) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ Cp : ℝ,0 < Cp ∧ ∀ᶠ n : ℕ in atTop,
      ∀ M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠ jGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let Mclock:=2*max Bclock 0
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n aDegree T) (f : Fin aDegree → NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (cutFullVariance n (fun j=>Sum.elim (fun _=>b j) (fun _=>h j)) U l t b h K)
            (fun σ=>|(G.canonicalHighWallSource M f).product σ|^(2*d)) 0  ≤
            (Real.exp (wholeLawRowComparisonConstant rBound*Mclock)*Cp^aDegree*
              M.data.d^aDegree)^(2*d) := by
  by_cases ha : aDegree=0
  · subst aDegree
    refine ⟨1,by norm_num,Filter.Eventually.of_forall ?_⟩
    intro n M _ L us hus _ _
    refine Filter.Eventually.of_forall ?_
    intro jGrid
    dsimp only
    intro U T l t _ _ _ G f _
    have HP : (G.canonicalHighWallSource M f).product=(fun _=>1) := by
      funext sigma
      unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
      apply Finset.prod_eq_one
      intro e _
      exact Fin.elim0 e
    rw [HP]
    simp only [abs_one,one_pow,pow_zero,mul_one]
    have ho := finiteCutMasses_ordered us hus jGrid
    rw [T.disorderExpect_one (fullWeight_pos n) (fullFeature n) ho]
    apply one_le_pow₀
    have hb : 0 ≤ 2*max Bclock 0 := by positivity
    have hc := wholeLawRowComparisonConstant_nonneg rBound
    exact Real.one_le_exp (mul_nonneg hc hb)
  · exact eventually_actual_high_wall_canonical_continuum_square_even_moment
      aDegree d rBound (Nat.pos_of_ne_zero ha) hd Bclock Cmass hCmass
      hm hdelta hroom hcl hcu hAz hC0 hCt

end OAI.SKFluctuations.Cavity
