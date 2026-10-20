module

public import ComparisonSignedCavityActualResetStarNormalizedRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

theorem native_reset_power_budget_normalize (n b d : ℕ) (eta : ℝ)
    {saving xs W v B Bbar : ℝ} {Cpower Cbase : ℕ→ℝ}
    (hsaving : 0 ≤ saving) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (hW : 0 < W) (hv : 0 < v) (hBbar : 0 ≤ Bbar) (hBB : B ≤ Bbar) :
    (∑j∈Finset.range d,Cpower j*((n:ℝ)^(-eta))^2*(savedProjectedScale xs W v)^2*
      ((Cbase j)^b*B)*(((n+1:ℕ):ℝ)^(-saving)*W)^(d-1)) ≤
      ((n:ℝ)^(-eta))^2*(∑j∈Finset.range d,Cpower j*(Cbase j)^b)*
        nativeSavedIncomingScale xs W W v*(Bbar*W^d) := by
  have hρ : 0 ≤ ((n+1:ℕ):ℝ)^(-saving)*W:=by positivity
  have hρW : ((n+1:ℕ):ℝ)^(-saving)*W ≤ W := by
    apply mul_le_of_le_one_left hW.le
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast;omega) (by linarith)
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have h1:0 ≤ Cpower j:=(hC j).1
  have h2:0 ≤ Cbase j:=(hC j).2
  have hd:0<d:=by have:=Finset.mem_range.mp hj;omega
  calc
    _ ≤ Cpower j*((n:ℝ)^(-eta))^2*(savedProjectedScale xs W v)^2*((Cbase j)^b*Bbar)*W^(d-1) := by gcongr
    _ = _ := by
      have HH:=native_saved_power_product_normalize d hd xs W v Bbar hW hv
      calc
        _=Cpower j*((n:ℝ)^(-eta))^2*(Cbase j)^b*
            ((savedProjectedScale xs W v)^2*Bbar*W^(d-1)):=by ring
        _=_:=by rw [HH];ring

def ActualNormalizedResetPowerOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d : ℕ) (eta Cmass Ap : ℝ)
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
      P.live.test.edges.length=b → P.live.test.incoming=[] →
    ∀(r₀ : ℝ) (p : MarkedPlacement T),p∈T.markedAttach r₀ →
      U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target) →
    ∀v : ℝ,W n ≤ v →
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeResetPairedProjectionValue n T P.live.test (M n) p q d
      (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val)| ≤
      ((n:ℝ)^(-eta))^2*Ap*nativeSavedIncomingScale (M n).xs (W n) (W n) v*
        (sourceMonomialScale ((M n).xs+partitionPoint 0 as pre.length) (W n)
          (nativeGeneratedCompleteInitial P.live.test pre.length)*(W n)^d)

theorem actual_normalized_reset_power_from_actual
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass : ℝ} {b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hsaving : 0 ≤ saving) (hCmass : 1 ≤ Cmass)
    (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (H : ActualGeneratedResetPowerOnEveryFinalNet b d eta saving Cmass Cpower Cbase M W w) :
    ActualNormalizedResetPowerOnEveryFinalNet b d eta Cmass
      (∑j∈Finset.range d,Cpower j*(Cbase j)^b) M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hb hIn
    r₀ p hp hh v hWv hvr hlow hz
  have ho:MassOrdered 0 (finiteCutMasses us r):=finiteCutMasses_ordered us hus r
  have hu:0 ≤ partitionPoint 0 (finiteCutMasses us r) pre.length:=(partitionPoint_mem _ ho _).1
  have huW:partitionPoint 0 (finiteCutMasses us r) pre.length ≤ Cmass*W n:=
    (partitionPoint_mono _ ho (Nat.le_add_right _ _)).trans hmass
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs hu
  obtain ⟨hx,hxW,hmassx⟩:=native_capped_incoming_mass (M n).hxs.le (hxsW n) hu hCmass huW
  have Hraw:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hb hIn
    (min s (W n)) hx hxW hmassx r₀ p hp hh v hWv hvr hlow hz
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hv:0<v:=hW.trans_le hWv
  have hx0:0 ≤ min s (W n):=(M n).hxs.le.trans hx
  exact Hraw.trans (native_reset_power_budget_normalize n b d eta hsaving hC hW hv
    (show 0 ≤ sourceMonomialScale s (W n) (nativeGeneratedCompleteInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le))

end OAI.SKFluctuations.LaplaceWindowFormalization
