module

public import ComparisonSignedCavityActualSpineGAllCubic
public import ComparisonSignedCavityActualGProjectedRowLaw
public import ComparisonSignedCavityProjectionSpineLeafBudget
public import ComparisonSignedCavityProjectionSpineScales

@[expose] public section

noncomputable section
set_option maxHeartbeats 30000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualCurrentGProjectedCubicOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → U≤(pre++(mid++tail)).length → P.live.test.teeth.length=d →
      P.live.test.exterior.length=a → P.live.test.edges.length=b+d →
    T.leaves≤rBound →
    ∀V : ℝ,W n ≤ V → V ≤ 1 → V≤(M n).R (partitionPoint 0 as U) →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
    |nativeActualDecoupledGProjectedResampling T P.live.test (pre.length+mid.length) U (M n) q| ≤
      2*(n:ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length))

theorem actual_current_G_projected_cubic_from_spine
    {m delta cl cu Az C0 Ct D Bclock eta Cmass : ℝ} {a b d rBound : ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (HI : ActualSpineGIncomingCubicOnEveryFinalNet a b d rBound eta Cmass M W w)
    (HS : ActualSpineGStarIncomingCubicOnEveryFinalNet a b d rBound eta Cmass M W w)
    (HP : ActualSpineGPowerCubicOnEveryFinalNet b d rBound eta Cmass M W w) :
    ActualCurrentGProjectedCubicOnEveryFinalNet a b d rBound eta Cmass M W w := by
  filter_upwards [HI,HS,HP] with n hnI hnS hnP
  intro L us hus hret hmesh hstar
  filter_upwards [hnI L us hus hret hmesh hstar,hnS L us hus hret hmesh hstar,
    hnP L us hus hret hmesh hstar] with r hrI hrS hrP
  dsimp only at hrI hrS hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU hUlen ht ha hb hleaf V hWV hV1 hVU hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hi : pre.length < pre.length+mid.length:=by omega
  obtain ⟨A,base,seed₀,k₀,hBase,hBaseTeeth,⟨spine⟩⟩:=hP.projectionDecomposition
  have hd : spine.toothCount=d:=by
    have H:=spine.teeth_length
    simp only [hBaseTeeth,List.length_nil,Nat.zero_add,ht] at H
    exact H.symm
  have haBase : base.live.test.exterior.length=a:=spine.exterior_length.symm.trans ha
  have hbBase : base.live.test.edges.length=b:=by
    have H:=spine.edges_length
    rw [hb,hd] at H
    omega
  have hleafBase : A.leaves≤rBound:=by have H:=spine.leaves_eq;omega
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  change |nativeActualDecoupledGProjectedResampling T P.live.test (pre.length+mid.length) U (M n) q|≤_
  rw [native_actual_decoupled_G_projected_resampling_eq_spine_row spine (M n) ho U hU hUlen
      V (by simpa only [hcut] using hVU),native_projection_spine_source_scale spine hi,hd]
  have hInDegree:=base.live.ancestry.incoming_degree
  cases hIn : base.live.test.incoming with
  | nil=>
    exact hrP pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth
      hbBase hIn hleafBase T P.live.test spine hd V hWV hV1 hlow hz
  | cons e es=>
    cases es with
    | nil=>
      rcases base.live.ancestry.incoming_cuts e (by simp [hIn]) with he|he
      · exact hrI pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth
          haBase hbBase e hIn he hleafBase T P.live.test spine hd V hWV hV1 hlow hz
      · exact hrS pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth
          haBase hbBase e hIn he hleafBase T P.live.test spine hd V hWV hV1 hlow hz
    | cons e' es=>simp [hIn] at hInDegree

end OAI.SKFluctuations.LaplaceWindowFormalization
