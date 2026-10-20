module

public import ComparisonActualGeneralCanonicalRestCloneTransport
public import ComparisonActualHighWallCanonicalRestProductRates

@[expose] public section

noncomputable section
set_option maxHeartbeats 22000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_high_wall_canonical_rest_clone_budget
    (a : ℕ) (Bclock Cmass Rmacro F : ℝ)
    (hCm : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,1 ≤ C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=M.data.d
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (forms : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a))
          (target : T.Slot) (cut : ℕ) (x v : ℝ),
          M.xs ≤ x → x ≤ W → 0 < v → W ≤ Rmacro/2 → cut ≤ as.length →
          (∀e,T.splitIndex target (G.i e) < cut) →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          4*W ≤ M.data.wallRadius M.alpha (partitionPoint 0 as cut) →
          M.z ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as cut)/8) (Rmacro/4) →
          (∀e,cut ≤ T.splitIndex target (G.j e) →
            M.data.wallRadius M.alpha (G.sourceLowMass e) ≤ min (M.data.wallRadius M.alpha (partitionPoint 0 as cut)/8) (Rmacro/4)) →
          v ≤ partitionPoint 0 as cut →
        let p:=nativeCloneBlockAtSlot T target cut
        p.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
          (fun σ=>((G.canonicalHighWallSource M forms).restProduct (p.restOldRestrict σ)-
            (G.canonicalHighWallSource M forms).restProduct (p.restNewRestrict σ))^2) 0 ≤
          ((a:ℝ)*(1+max Bclock 0)*(2*(n:ℝ)^(-eta)*savedExteriorScale ((2*C0)*M.xs) W v)/x*
            (C^a*sourceMonomialScale x W initial))^2 := by
  by_cases ha:0 < a
  · obtain ⟨C,hC,HC⟩:=eventually_actual_high_wall_canonical_rest_product_resampling
      (D:=D) a ha Bclock Cmass Rmacro F hCm hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hmacro hRhalf hFmass hFradius
    refine ⟨C,hC,?_⟩
    filter_upwards [HC] with n hn
    intro M hwork L us hus hret hmesh
    filter_upwards [hn M hwork L us hus hret hmesh] with k hk
    dsimp only at hk ⊢
    intro T G forms initial target cut x v hxsx hxW hv hWmacro hcut hout hmass hhigh hz hlow hvmass
    let p:=nativeCloneBlockAtSlot T target cut
    let GP:=G.onCloneOld target cut
    let js:=fun e=>p.newEmbed (G.j e)
    have Hne:=G.clone_new_targets_ne target cut hout
    have Hsame:=G.clone_new_targets_same_low target cut hout
    have Hmass:∀e,GP.sourceLowMass e ≤ Cmass*sourceFactorScale x (M.data.d) initial e:=by
      intro e
      rw [G.onCloneOld_sourceLowMass]
      exact hmass e
    have Hgeo:∀e,GP.j e≠js e →
        let rh:=M.data.wallRadius M.alpha (partitionPoint 0 (finiteCutMasses us k) (p.tree.splitIndex (GP.j e) (js e)))
        4*(M.data.d) ≤ rh ∧
        M.z ≤ min (rh/8) (Rmacro/4) ∧
        M.data.wallRadius M.alpha (GP.sourceLowMass e) ≤ min (rh/8) (Rmacro/4) ∧
        v ≤ partitionPoint 0 (finiteCutMasses us k) (p.tree.splitIndex (GP.j e) (js e)):=by
      intro e he
      have hin:cut ≤ T.splitIndex target (G.j e):=by
        by_contra H
        exact he (nativeCloneBlockAtSlot_exterior_shared T target cut (G.j e) (by omega))
      have HG:=nativeCloneBlockAtSlot_boundary_geometry T target (G.j e) (G.i e) cut hin (hout e)
      have Hcross:p.tree.splitIndex (GP.j e) (js e)=cut:=HG.2.2.2
      rw [Hcross]
      rw [G.onCloneOld_sourceLowMass]
      exact ⟨hhigh,hz,hlow e hin,hvmass⟩
    have HH:=hk p.tree GP forms initial x v hxsx hxW hv hWmacro Hmass js Hne Hsame Hgeo
    dsimp only [GP,js,p] at HH
    simp only [ActualNaturalBoundaryShape.canonicalHighWallSource] at HH ⊢
    simp_rw [G.onCloneOld_physical_restProduct M.bf M.hf forms target cut,
      G.onCloneOld_retarget_new_physical_restProduct M.bf M.hf forms target cut hout] at HH
    exact HH
  · have ha0:a=0:=by omega
    subst a
    refine ⟨1,le_refl _,Eventually.of_forall (fun n=>?_)⟩
    intro M hwork L us hus hret hmesh
    refine Eventually.of_forall fun k=>?_
    dsimp only
    intro T G forms initial target cut x v hxsx hxW hv hWmacro hcut hout hmass hhigh hz hlow hvmass
    simp only [ActualNaturalBoundaryShape.restProduct,Finset.univ_eq_empty,
      Finset.prod_empty,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),Nat.cast_zero,
      zero_mul,zero_div]
    unfold ClockTree.disorderExpect
    simp

end OAI.SKFluctuations.Cavity
