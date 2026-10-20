module

public import ComparisonSignedCavityActualResetNormalizedRate
public import ComparisonActualHighWallGammaPairedProductsAlong
public import ComparisonActualHighWallResetPairedRateAlong
public import ComparisonActualHighWallResetStarPairedRateAlong
public import ComparisonActualHighWallResetPowerRateAlong
public import ComparisonActualGeneralResetIncomingAllocation
public import ComparisonActualGeneralResetStarIncomingAllocation
public import ComparisonActualGeneralResetPowerAllocation
public import ComparisonActualGeneralResetPairedValue

@[expose] public section

noncomputable section
set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualHighWallNormalizedResetIncomingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta Cmass Ai Ap : ℝ)
    (M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length →
    ∀(r₀ : ℝ) (p : MarkedPlacement T),p∈T.markedAttach r₀ →
      U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target) →
    ∀v : ℝ,W n ≤ v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |actualGeneralResetPairedProjectionValue (dim n) T P.live.test (M n).bf (M n).hf p q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      (((dim n):ℝ)^(-eta))^2*
        (Ai*nativeSavedIncomingScale (M n).xs (W n) ((M n).xs+partitionPoint 0 as pre.length) v+
          Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v)*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

theorem actual_high_wall_normalized_reset_incoming_from_actual_along
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hsaving : 0 ≤ saving) (hCmass : 1 ≤ Cmass)
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (H : ActualHighWallGeneratedResetPairedIncomingOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ActualHighWallNormalizedResetIncomingOnEveryFinalNetAlong a b d eta Cmass (Cp*Ch^a)
      (∑j∈Finset.range d,Cpower j*(Cbase j)^b) M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    r₀ p hp hh v hWv hvr hlow hz
  have ho:MassOrdered 0 (finiteCutMasses us r):=finiteCutMasses_ordered us hus r
  have hu:0 ≤ partitionPoint 0 (finiteCutMasses us r) pre.length:=(partitionPoint_mem _ ho _).1
  have huW:partitionPoint 0 (finiteCutMasses us r) pre.length ≤ Cmass*W n:=
    (partitionPoint_mono _ ho (Nat.le_add_right _ _)).trans hmass
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs hu
  obtain ⟨hx,hxW,hmassx⟩:=native_capped_incoming_mass (M n).hxs.le (hxsW n) hu hCmass huW
  have Hraw:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    (min s (W n)) hx hxW hmassx r₀ p hp hh v hWv hvr hlow hz
  have hscale:=native_generated_reset_incoming_i_source_scale P.live.test P.live.ancestry
    (by omega) ht e₀ hIn hi s (W n)
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hv:0<v:=hW.trans_le hWv
  have hx0:0 ≤ min s (W n):=(M n).hxs.le.trans hx
  have Hnorm:=native_reset_paired_budget_normalize (dim n) a b d eta hsaving hCp hCh zero_le_one hC
    (M n).hxs.le hW hv hs
    (show 0 ≤ sourceMonomialScale (min s (W n)) (W n) (nativeGeneratedExteriorInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (show 0 ≤ sourceMonomialScale (min s (W n)) (W n) (nativeGeneratedCompleteInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (show 0 ≤ sourceMonomialScale s (W n) (nativeGeneratedExteriorInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le)
    (by rw [←hscale];exact sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le)
    (show savedWeightedExteriorScale (M n).xs (W n) v s ≤ 1*savedWeightedExteriorScale (M n).xs (W n) v s by simp)
  have Hfinal:=Hraw.trans Hnorm
  simpa only [mul_one,←hscale] using Hfinal

end OAI.SKFluctuations.LaplaceWindowFormalization
