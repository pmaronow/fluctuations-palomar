module

public import ComparisonSignedCavityActualResetPowerNormalizedRate
public import ComparisonSignedCavityActualSpineGStarIncomingRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualNormalizedSpineGStarIncomingOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d rBound : ℕ) (eta Cmass Temp Cg Ai Ap : ℝ)
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
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length+mid.length →
    ∀(V : ClockTree (Spin n×Bool) (pre++(mid++tail))) (Q : NativeGeneratedTest V)
      (spine : NativeProjectionSpine P.live.test (pre.length+mid.length) Q),spine.toothCount=d →
    ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
    ∀(rr : MarkedPlacement p.tree),rr∈p.tree.markedAttach 0 →
    ∀(zz : MarkedPlacement rr.tree),zz∈rr.tree.markedAttach 0 →
      U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark →
      U ≤ rr.tree.splitIndex (rr.embed (p.embed P.live.test.target)) rr.mark →
      U ≤ zz.tree.splitIndex (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark →
      zz.embed rr.mark ≠ zz.mark → p.embed P.live.test.target ≠ p.mark →
      (spine.graftDiagram ((((NativeObservedDiagram.identity T).observe p).observe rr).observe zz)).tree.leaves ≤ rBound →
    ∀v : ℝ,W n ≤ v →
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeActualTripleSpineGValue spine (M n) U p rr zz q| ≤
      Temp*Cg*v*(
      ((n:ℝ)^(-eta))^2*
        (Ai*nativeSavedIncomingScale (M n).xs (W n) (W n) v+
          Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d))

theorem actual_normalized_spine_G_star_incoming_from_actual
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Temp Cg Cp Ch : ℝ} {a b d rBound : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hTemp : 0 ≤ Temp) (hCg : 0 ≤ Cg) (hsaving : 0 ≤ saving) (hCmass : 1 ≤ Cmass)
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (H : ActualGeneratedSpineGStarIncomingOnEveryFinalNet a b d rBound eta saving Cmass Temp Cg Cp Ch Cpower Cbase M W w) :
    ActualNormalizedSpineGStarIncomingOnEveryFinalNet a b d rBound eta Cmass Temp Cg (Cp*Ch^a*Real.sqrt (1+Cmass))
      (∑j∈Finset.range d,Cpower j*(Cbase j)^b) M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
  have ho:MassOrdered 0 (finiteCutMasses us r):=finiteCutMasses_ordered us hus r
  have hu:0 ≤ partitionPoint 0 (finiteCutMasses us r) pre.length:=(partitionPoint_mem _ ho _).1
  have huW:partitionPoint 0 (finiteCutMasses us r) pre.length ≤ Cmass*W n:=
    (partitionPoint_mono _ ho (Nat.le_add_right _ _)).trans hmass
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs hu
  obtain ⟨hx,hxW,hmassx⟩:=native_capped_incoming_mass (M n).hxs.le (hxsW n) hu hCmass huW
  have Hraw:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    (min s (W n)) hx hxW hmassx V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
  have hscale:=native_generated_reset_incoming_star_source_scale P.live.test P.live.ancestry
    (by omega) ht e₀ hIn hi s (W n)
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hv:0<v:=hW.trans_le hWv
  have hx0:0 ≤ min s (W n):=(M n).hxs.le.trans hx
  have Hnorm:=native_reset_paired_budget_normalize n a b d eta hsaving hCp hCh (Real.sqrt_nonneg (1+Cmass)) hC
    (M n).hxs.le hW hv hW
    (show 0 ≤ sourceMonomialScale (min s (W n)) (W n) (nativeGeneratedExteriorInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (show 0 ≤ sourceMonomialScale (min s (W n)) (W n) (nativeGeneratedCompleteInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (show 0 ≤ sourceMonomialScale s (W n) (nativeGeneratedExteriorInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le)
    (by rw [←hscale];exact sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le)
    (savedWeightedExteriorScale_star_band (M n).hxs.le hW hv (by linarith : 0 ≤ Cmass) (hxsW n) hmass)
  have Hfinal:=Hraw.trans (mul_le_mul_of_nonneg_left Hnorm (show 0 ≤ Temp*Cg*v by positivity))
  simpa only [←hscale] using Hfinal

end OAI.SKFluctuations.LaplaceWindowFormalization
