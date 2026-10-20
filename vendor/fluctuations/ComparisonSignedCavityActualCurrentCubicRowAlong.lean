module

public import ComparisonSignedCavityActualCurrentCubicRow
public import ComparisonSignedCavityActualResetIncomingCubicRowAlong
public import ComparisonSignedCavityActualResetStarCubicRowAlong
public import ComparisonSignedCavityActualResetPowerCubicRowAlong

@[expose] public section

noncomputable section
set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualCurrentProjectedCubicRowOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta Cmass : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠr : ℕ in atTop,
    let as:=finiteCutMasses us r
    let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
      (fun _=>((M n).bf (partitionPoint 0 as j):ℝ)) (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
    ∀(T : ClockTree (Spin (dim n)×Bool) (pre++(mid++tail))) (U depth : ℕ) (seed : List NativeResourceMark)
      (P : NativeResourceTerm pre.length (pre.length+mid.length) T),
      NativeActualResourceGenerated pre.length (pre.length+mid.length) U seed depth T P →
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth.length=d →
      P.live.test.exterior.length=a → P.live.test.edges.length=b+d →
    ∀V : ℝ,W n ≤ V → V ≤ 1 →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
    |nativeResetProjectedGammaRow (dim n) T P.live.test (M n) U V q
      (nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as) 0
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      2*((dim n):ℝ)^(-eta)*(W n*(M n).xs^2)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length))

theorem actual_current_projected_cubic_row_from_reset_along
    {m delta cl cu Az C0 Ct D Bclock eta Cmass : ℝ} {a b d : ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (HI : ActualResetIncomingCubicRowOnEveryFinalNetAlong a b d eta Cmass M W w)
    (HS : ActualResetStarIncomingCubicRowOnEveryFinalNetAlong a b d eta Cmass M W w)
    (HP : ActualResetPowerCubicRowOnEveryFinalNetAlong b d eta Cmass M W w) :
    ActualCurrentProjectedCubicRowOnEveryFinalNetAlong a b d eta Cmass M W w := by
  filter_upwards [HI,HS,HP] with n hnI hnS hnP
  intro L us hus hret hmesh hstar
  filter_upwards [hnI L us hus hret hmesh hstar,hnS L us hus hret hmesh hstar,
    hnP L us hus hret hmesh hstar] with r hrI hrS hrP
  dsimp only at hrI hrS hrP ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb V hWV hV1 hlow hz
  have ho:MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hi:pre.length < pre.length+mid.length:=by omega
  obtain ⟨A,base,seed₀,k₀,hBase,hBaseTeeth,⟨spine⟩⟩:=hP.projectionDecomposition
  have hd:spine.toothCount=d:=by have H:=spine.teeth_length;simp only [hBaseTeeth,List.length_nil,Nat.zero_add,ht] at H;exact H.symm
  have haBase:base.live.test.exterior.length=a:=spine.exterior_length.symm.trans ha
  have hbBase:base.live.test.edges.length=b:=by have H:=spine.edges_length;rw [hb,hd] at H;omega
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let K:=nativeContinuumMixedClock (dim n) (M n).bf (M n).hf (finiteCutMasses us r)
  have hNode:partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length)=(w n).star.val:=by
    rw [hcut,hindex]
    exact nativeRetainedCut_partitionPoint _ (finiteCutMasses_ordered us hus r) (w n).star
      (finiteCutMasses_nodes us r hstar)
  have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk
    (M n).context.hkc (M n).context.hm (M n).context.hM (M n).b (M n).h
    (M n).context.hd.ne' (M n).hlam.le (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
  have hCenter:pathPairMoment (uniformWeight ((dim n)+1)) (finiteFeature ((dim n)+1))
      (completedPathClock ((dim n)+1) (M n).bf (M n).hf) (orderedOverlap ((dim n)+1))
      (partitionPoint 0 (pre++(mid++tail)) (pre.length+mid.length))=
      orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val:=by
    rw [hNode]
    exact (orderedPathPair_eq_completed ((dim n)+1) (by omega) (M n).bf (M n).hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1) (orderedOverlap ((dim n)+1))
      ⟨(w n).star.property,by rw [←hNode];exact (partitionPoint_mem _ ho _).2⟩).symm
  have Hrow:=native_projected_gamma_row_spine (dim n) spine (hBase.targetStarSingleton hi.le)
    (hP.targetStarSingleton hi.le) (M n) U V q K ho hU
  dsimp only at Hrow
  rw [hCenter,hd] at Hrow
  change |nativeResetProjectedGammaRow (dim n) T P.live.test (M n) U V q K 0 _| ≤ _
  rw [Hrow,native_projection_spine_source_scale spine hi,hd]
  have hInDegree:=base.live.ancestry.incoming_degree
  cases hIn:base.live.test.incoming with
  | nil=>exact hrP pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth hbBase hIn V hWV hV1 hlow hz
  | cons e es=>
    cases es with
    | nil=>
      rcases base.live.ancestry.incoming_cuts e (by simp [hIn]) with he|he
      · exact hrI pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth haBase hbBase e hIn he V hWV hV1 hlow hz
      · exact hrS pre mid tail hcut hindex hmass A U k₀ seed₀ base hBase hmid hU hBaseTeeth haBase hbBase e hIn he V hWV hV1 hlow hz
    | cons e' es=>simp [hIn] at hInDegree

end OAI.SKFluctuations.LaplaceWindowFormalization
