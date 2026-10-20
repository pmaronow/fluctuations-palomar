module

public import ComparisonActualHighWallSecondLowObservedAffineSavedRate
public import ComparisonSignedCavitySecondLowInheritedFreshAffineSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open MeasureTheory ProbabilityTheory Filter Set Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 35000000
set_option backward.isDefEq.respectTransparency false

def actualHighWallSecondLowCanonicalObservedFreshLowDifferenceAtom
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c bslot fslot : T.Slot)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (p : MarkedPlacement T) : ℝ :=
  let g:=nativeFreshAtSlot p.tree 0 (p.embed bslot) star
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  g.tree.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
    (fun τ=>(G.canonicalHighWallSource M forms).restProduct (p.restRestrict (g.restRestrict τ))*
      restLowKernel n U b h (p.tree.splitIndex (p.embed c) (p.embed fslot))
        (p.tree.cavityLeft.atSlot (g.restRestrict τ) (p.tree.cavityLeftSlot (p.embed fslot)))
        (p.tree.cavityLeft.atSlot (g.restRestrict τ) (p.tree.cavityLeftSlot (p.embed c)))*
      (restLowKernel n U b h (g.tree.splitIndex g.mark (g.embed p.mark))
          (p.restSpin (g.restRestrict τ)) (g.restSpin τ)-
        restLowKernel n U b h (g.tree.splitIndex g.mark (g.embed (p.embed c)))
          (p.tree.cavityLeft.atSlot (g.restRestrict τ) (p.tree.cavityLeftSlot (p.embed c))) (g.restSpin τ))) 0

def actualHighWallSecondLowCanonicalObservedFreshLowDifferenceRow
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c bslot fslot : T.Slot)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*fullScalarCutGamma p.tree U K (p.embed c) p.mark*
    actualHighWallSecondLowCanonicalObservedFreshLowDifferenceAtom n a M T star U c bslot fslot G forms q p)).sum

private theorem second_low_fresh_expect_neg (n : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n) as) (q : ℕ→RestCoordinate n→ℝ) (F : T.Assignment→ℝ) :
    T.disorderExpect (restWeight n) (restFeature n) 0 q (fun τ=>-F τ) 0=
      -T.disorderExpect (restWeight n) (restFeature n) 0 q F 0 := by
  unfold ClockTree.disorderExpect
  simp only [mul_neg,Finset.sum_neg_distrib]

theorem actual_high_wall_second_low_canonical_observed_fresh_low_difference_atom_eq_negative_affine
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c bslot fslot : T.Slot)
    (hstar : star<U) (Hcf : T.splitIndex c fslot<U)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (p : MarkedPlacement T) (hp : p∈T.markedAttach 0) :
    actualHighWallSecondLowCanonicalObservedFreshLowDifferenceAtom n a M T star U c bslot fslot G forms q p=
      -actualHighWallOriginalFreshAffineResidual n M p.tree (p.embed c) p.mark (p.embed bslot) star q
        (fun σ=>ActualNaturalBoundaryShape.actualHighWallLowRestFactor M (p.embed c) (p.embed fslot) σ*
          (G.canonicalHighWallSource M forms).restProduct (p.restRestrict σ)) := by
  let g:=nativeFreshAtSlot p.tree 0 (p.embed bslot) star
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have Hcfp : p.tree.splitIndex (p.embed c) (p.embed fslot)<U:=by
    rw [(T.markedAttach_embed_preserves 0 p hp).2]
    exact Hcf
  have Hgc : g.tree.splitIndex g.mark (g.embed (p.embed c))<U:=
    nativeFreshAtSlot_outside_old_blocks p.tree 0 (p.embed bslot) hstar (p.embed c)
  have Hge : g.tree.splitIndex g.mark (g.embed p.mark)<U:=
    nativeFreshAtSlot_outside_old_blocks p.tree 0 (p.embed bslot) hstar p.mark
  unfold actualHighWallSecondLowCanonicalObservedFreshLowDifferenceAtom actualHighWallOriginalFreshAffineResidual
  dsimp only
  rw [←second_low_fresh_expect_neg]
  congr 1
  funext τ
  rw [actual_high_wall_low_rest_factor_eq_restLowKernel n M p.tree U (p.embed c) (p.embed fslot) Hcfp,
    actual_high_wall_low_rest_factor_eq_restLowKernel n M g.tree U g.mark (g.embed (p.embed c)) Hgc,
    actual_high_wall_low_rest_factor_eq_restLowKernel n M g.tree U g.mark (g.embed p.mark) Hge]
  simp only [←g.restRestrict_at,MarkedPlacement.restSpin]
  ring

private theorem second_low_fresh_sum_neg {α : Type} (L : List α) (F : α→ℝ) :
    (L.map (fun x=>-F x)).sum=-(L.map F).sum := by
  induction L with
  | nil=>simp
  | cons x L ih=>simp only [List.map_cons,List.sum_cons,ih,neg_add]

theorem actual_high_wall_second_low_canonical_observed_fresh_low_difference_eq_negative_affine_row
    (n a : ℕ) {as : List PositiveMass} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (T : ClockTree (Spin n×Bool) as) (star U : ℕ) (c bslot fslot : T.Slot)
    (hstar : star<U) (Hcf : T.splitIndex c fslot<U)
    (G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
    (q : ℕ→RestCoordinate n→ℝ) (K : ℕ→ℝ) :
    actualHighWallSecondLowCanonicalObservedFreshLowDifferenceRow n a M T star U c bslot fslot G forms q K=
      -actualHighWallCanonicalObservedFreshAffineRow n a M T star U c bslot fslot false G forms q K := by
  unfold actualHighWallSecondLowCanonicalObservedFreshLowDifferenceRow actualHighWallCanonicalObservedFreshAffineRow
  rw [←second_low_fresh_sum_neg]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rw [actual_high_wall_second_low_canonical_observed_fresh_low_difference_atom_eq_negative_affine n a M T
    star U c bslot fslot hstar Hcf G forms q p hp]
  simp only [nativeObservedRemainingTarget,Bool.false_eq_true,ite_false]
  ring

theorem eventually_actual_high_wall_second_low_fresh_low_difference_saved_rate
    (a : ℕ) (Bclock Cmass : ℝ)
    (hCmass : 0 ≤ Cmass)
    {m delta eta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp C : ℝ,0<Cp ∧ 0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=M.data.d
        ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
          partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W →
        ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (c b fslot : T.Slot)
          (U : ℕ),0 < mid.length → pre.length+mid.length<U → U ≤ as.length →
          NativePersistentLowForks pre.length (pre.length+mid.length) U T →
          (T.splitIndex c b=pre.length ∨ T.splitIndex c b=pre.length+mid.length) →
          T.splitIndex c fslot ≤ pre.length+mid.length →
          W ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U) →
          M.data.wallRadius M.alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U)/2 →
          M.z ≤ M.data.wallRadius M.alpha (partitionPoint 0 as U)/2 →
        ∀(G : ActualNaturalBoundaryShape n a T) (forms : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          |actualHighWallSecondLowCanonicalObservedFreshLowDifferenceRow n a M T (pre.length+mid.length) U c b fslot
            G forms q (nativeContinuumMixedClock n M.bf M.hf as)| ≤ 
            (2*(T.leaves:ℝ))*C*(n:ℝ)^(-eta)*(W*M.xs^2*(Cp^a*sourceMonomialScale x W initial)) := by
  obtain ⟨Cp,C,hCp,hC,H⟩:=eventually_actual_high_wall_second_low_observed_affine_saved_rate
    (D:=D) a Bclock Cmass hCmass
    hm hdelta hroom hgap hcl hcu hAz hC0 hCt
  refine ⟨Cp,C,hCp,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hfixed L us hus hret hmesh
  filter_upwards [hn M hfixed L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hmass T c b fslot U hmid hU hlen hT hcb hcf hWU hstar hz
    G forms initial x hxsx hxW hmassG
  rw [actual_high_wall_second_low_canonical_observed_fresh_low_difference_eq_negative_affine_row n a M T
    (pre.length+mid.length) U c b fslot hU (by omega) G forms,abs_neg]
  exact hk pre mid tail hcut hmass T c b fslot false U hmid hU hlen hT hcb hcf hWU hstar hz
    G forms initial x hxsx hxW hmassG

end OAI.SKFluctuations.Cavity
