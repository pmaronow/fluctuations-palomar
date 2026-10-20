module

public import ComparisonActualHighWallCanonicalRestMoments
public import ComparisonActualHighWallRetainedPairedHighBudget
public import ComparisonSignedCavityPairedNearMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_canonical_paired_near_high
    (a : ℕ) (Bclock Cmass : ℝ) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cs Cp : ℝ,0 < Cs ∧ 0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) ,
           (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
        ∀(G₀ : ActualNaturalBoundaryShape n 1 T) (j₀' : Fin 1 → T.Slot)
          (hne₀ : ∀e,G₀.i e≠j₀' e),
          (∀e,T.splitIndex (G₀.i e) (G₀.j e)=T.splitIndex (G₀.i e) (j₀' e)) →
          G₀.sourceLowMass 0 ≤ Cmass*M.data.d →
        let H:=G₀.canonicalHighWallSource M (fun _=>NativeSourceFactorForm.centered)
        let H':=(G₀.retarget j₀' hne₀).canonicalHighWallSource M (fun _=>NativeSourceFactorForm.centered)
        let P:=G.canonicalHighWallSource M f
        let P':=(G.retarget j' hne).canonicalHighWallSource M f
        let paired:=fun σ=>(H.restProduct σ-H'.restProduct σ)*(P.restProduct σ-P'.restProduct σ)
        let Cpair:=4*Cs*M.data.d*(Cp^a*M.data.d^a)
        (T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>paired σ^2) 0 ≤ Cpair^2) ∧
        ∀(U rBound : ℕ),T.leaves ≤ rBound →
          let R:=M.data.highErrorEnvelope M.alpha as U
          |retainedSignedJets n q U b h K [restHighKernel n U b h K] T paired []| ≤
            pairForkVariation rBound*Cpair*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_canonical_rest_even_moment
    (D:=D) a 2 (by norm_num) Bclock Cmass hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_high_wall_canonical_rest_even_moment
    (D:=D) 1 2 (by norm_num) Bclock Cmass hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cs,Cp,hCs,hCp,?_⟩
  filter_upwards [HP,HS] with n hnP hnS
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh,
    hnS M hwork L us hus hret hmesh] with k hkP hkS
  dsimp only at hkP hkS ⊢
  intro T G f hmass j' hne hlow G₀ j₀' hne₀ hlow₀ hmass₀
  have hW:=M.data.hd
  have hxspos:=M.hxs
  have hscale : 0 < Cp^a*M.data.d^a := by
    positivity
  have HP:=hkP T G f hmass
  have HQ:=hkP T (G.retarget j' hne) f (by
    intro e
    rw [G.retarget_sourceLowMass j' hne hlow]
    exact hmass e)
  have HS:=hkS T G₀ (fun _=>NativeSourceFactorForm.centered) (by
    intro e
    have he : e=0:=Subsingleton.elim _ _
    simpa only [he] using hmass₀)
  have HS':=hkS T (G₀.retarget j₀' hne₀) (fun _=>NativeSourceFactorForm.centered) (by
    intro e
    rw [G₀.retarget_sourceLowMass j₀' hne₀ hlow₀]
    have he : e=0:=Subsingleton.elim _ _
    simpa only [he] using hmass₀)
  simp only [pow_one] at HS HS'
  have H:=native_rest_two_differences_square n T (finiteCutMasses_ordered us hus k) _ _ _ _ _
    (mul_pos hCs hW) hscale HS HS' HP HQ
  have HE : 4*(Cs*M.data.d)*(Cp^a*M.data.d^a)=
      4*Cs*M.data.d*(Cp^a*M.data.d^a):=by ring
  rw [HE] at H
  refine ⟨H,?_⟩
  intro U rBound hT
  exact actual_high_wall_retained_first_high_rest_L2_bound M
    T (finiteCutMasses_ordered us hus k) U rBound hT _ (by positivity) H

end OAI.SKFluctuations.Cavity
