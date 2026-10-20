module

public import ComparisonActualHighWallSourceMoments
public import ComparisonSignedCavityCanonicalRestMoments

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 18000000

theorem sourceMonomialScale_self (a : ℕ) (d : ℝ) (I : Finset (Fin a)) :
    sourceMonomialScale d d I=d^a := by
  have HI : I.card≤ a:=by simpa using Finset.card_le_card (Finset.subset_univ I)
  unfold sourceMonomialScale
  rw [←pow_add,Nat.add_sub_of_le HI]

theorem eventually_actual_high_wall_canonical_rest_even_moment
    (a p : ℕ) (hp : 0< p) (Bclock Cmass : ℝ) (hCm : 0≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0< m) (hdelta : 0< delta) (hroom : delta<3*m)
    (hcl : 0< cl) (hcu : 0< cu) (hAz : 0≤ Az) (hC0 : 0< C0) (hCt : 0≤ Ct) :
    ∃C : ℝ,0< C ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),(∀u∈us,u.val≤1) →
        (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤ M.xs →
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm),
          (∀e,G.sourceLowMass e≤ Cmass*M.data.d) →
          T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
            (fun σ=>|(G.canonicalHighWallSource M f).restProduct σ|^(2*p)) 0≤
            (C^a*M.data.d^a)^(2*p) := by
  by_cases ha : a=0
  · subst a
    refine ⟨1,by norm_num,Eventually.of_forall ?_⟩
    intro n M hfixed L us hus hret hmesh
    apply Eventually.of_forall
    intro k
    dsimp only
    intro T G f hmass
    have ho:=finiteCutMasses_ordered us hus k
    simp [ActualNaturalBoundaryShape.restProduct,T.cavityLeft.disorderExpect_one
      (restWeight_pos n) (restFeature n) ho]
  · obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_canonical_square_even_moment
      a p (by omega) hp Bclock Cmass hCm hm hdelta hroom hcl hcu hAz hC0 hCt
    refine ⟨C,hC,?_⟩
    filter_upwards [H] with n hn
    intro M hfixed L us hus hret hmesh
    filter_upwards [hn M hfixed L us hus hret hmesh] with k hk
    dsimp only at hk ⊢
    intro T G f hmass
    rw [(G.canonicalHighWallSource M f).rest_moment_eq_full_decoupled
      (finiteCutMasses_ordered us hus k) _ _ 0 (2*p)]
    exact hk 0 T 0 0 (by norm_num) (by norm_num) G f hmass

end OAI.SKFluctuations.Cavity
