module

public import ComparisonSignedCavityPairedNearMoments
public import ComparisonSignedCavityInheritedCanonicalRestMoments
public import ComparisonSignedCavityInheritedRetainedPairedHighBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_inherited_canonical_paired_near_high
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cf Cmass : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cs Cp : ℝ,0 < Cs ∧ 0 < Cp ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (W : ℝ),
          M.xs ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
        ∀(G₀ : ActualNaturalBoundaryShape n 1 T) (j₀' : Fin 1 → T.Slot)
          (hne₀ : ∀e,G₀.i e≠j₀' e),
          (∀e,T.splitIndex (G₀.i e) (G₀.j e)=T.splitIndex (G₀.i e) (j₀' e)) →
          G₀.sourceLowMass 0 ≤ Cmass*W →
        let H:=G₀.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)
        let H':=(G₀.retarget j₀' hne₀).canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)
        let P:=G.canonicalMinimumSource M f
        let P':=(G.retarget j' hne).canonicalMinimumSource M f
        let paired:=fun σ=>(H.restProduct σ-H'.restProduct σ)*(P.restProduct σ-P'.restProduct σ)
        let Cpair:=4*Cs*W*(Cp^a*sourceMonomialScale M.xs W initial)
        (T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>paired σ^2) 0 ≤ Cpair^2) ∧
        ∀(U rBound : ℕ),T.leaves ≤ rBound →
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
            (4*Cf+2*Temp) Temp
          |retainedSignedJets n q U b h K [restHighKernel n U b h K] T paired []| ≤
            pairForkVariation rBound*Cpair*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment
    (D:=D) a 2 ha (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_inherited_canonical_rest_even_moment
    (D:=D) 1 2 (by norm_num) (by norm_num) Bclock Temp Cf Cmass hTemp hCf hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cs,Cp,hCs,hCp,?_⟩
  filter_upwards [HP,HS] with n hnP hnS
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hnP M hsource hxs L us hus hret hmesh,
    hnS M hsource hxs L us hus hret hmesh] with k hkP hkS
  dsimp only at hkP hkS ⊢
  intro T G f initial W hxW hmass j' hne hlow G₀ j₀' hne₀ hlow₀ hmass₀
  have hW : 0 < W:=M.hxs.trans_le hxW
  have hxspos:=M.hxs
  have hscale : 0 < Cp^a*sourceMonomialScale M.xs W initial := by
    unfold sourceMonomialScale
    positivity
  have HP:=hkP T G f initial M.xs W le_rfl hxW hmass
  have HQ:=hkP T (G.retarget j' hne) f initial M.xs W le_rfl hxW (by
    intro e
    rw [G.retarget_sourceLowMass j' hne hlow]
    exact hmass e)
  have HS:=hkS T G₀ (fun _=>NativeSourceFactorForm.centered) ∅ W W hxW le_rfl (by
    intro e
    have he : e=0:=Subsingleton.elim _ _
    simpa only [he,sourceFactorScale,Finset.notMem_empty,ite_false] using hmass₀)
  have HS':=hkS T (G₀.retarget j₀' hne₀) (fun _=>NativeSourceFactorForm.centered) ∅ W W hxW le_rfl (by
    intro e
    rw [G₀.retarget_sourceLowMass j₀' hne₀ hlow₀]
    have he : e=0:=Subsingleton.elim _ _
    simpa only [he,sourceFactorScale,Finset.notMem_empty,ite_false] using hmass₀)
  simp only [sourceMonomialScale,Finset.card_empty,pow_zero,one_mul,Nat.sub_zero,pow_one] at HS HS'
  have H:=native_rest_two_differences_square n T (finiteCutMasses_ordered us hus k) _ _ _ _ _
    (mul_pos hCs hW) hscale HS HS' HP HQ
  have HE : 4*(Cs*W)*(Cp^a*sourceMonomialScale M.xs W initial)=
      4*Cs*W*(Cp^a*sourceMonomialScale M.xs W initial):=by ring
  rw [HE] at H
  refine ⟨H,?_⟩
  intro U rBound hT
  exact actual_minimum_inherited_retained_first_high_rest_L2_bound M Temp Cf hTemp hCf hsource hxs
    T (finiteCutMasses_ordered us hus k) U rBound hT _ (by positivity) H

end OAI.SKFluctuations.Cavity
