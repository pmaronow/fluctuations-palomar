module

public import ComparisonSignedCavityActualResetPairedRate
public import ComparisonSignedCavityInheritedGammaAlongPairedProducts

@[expose] public section

noncomputable section
set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualGeneratedResetPairedIncomingOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (Cpower Cbase : ℕ→ℝ)
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
      0 < mid.length → pre.length+mid.length < U → P.live.test.teeth=[] →
      P.live.test.exterior.length=a → P.live.test.edges.length=b →
    ∀e₀ : T.Slot,P.live.test.incoming=[e₀] → T.splitIndex P.live.test.target e₀=pre.length →
    ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
    ∀(r₀ : ℝ) (p : MarkedPlacement T),p∈T.markedAttach r₀ →
      U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target) →
    ∀v : ℝ,W n ≤ v →
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeResetPairedProjectionValue (dim n) T P.live.test (M n) p q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      nativeResetPairedBudget (dim n) a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as pre.length)
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))

theorem actual_generated_reset_paired_incoming_from_canonical_along
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ActualCanonicalPairedIncomingOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ActualGeneratedResetPairedIncomingOnEveryFinalNetAlong a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi x hxsx hxW hmi
    r₀ p hp hh v hWv hvr hlow hz
  subst a
  subst b
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hlen : pre.length+mid.length<(pre++(mid++tail)).length:=
    hU.trans_le (hh.trans (p.tree.splitIndex_le_clockLength _ _))
  let G:=(nativeGeneratedExteriorShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r₀ p hp
  let G₀:=(nativeGeneratedCompleteShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r₀ p hp
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  obtain ⟨E,t,e,htRead,heRead,hsplit,Hlaw⟩:=native_actual_reset_incoming_i_paired_source
    (dim n) pre mid tail hP hmid hU ht e₀ hIn hi r₀ p hp hh ho (M n) 0 q 0 d center
  have hG (j) : G.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedExteriorInitial P.live.test pre.length) j :=
    native_actual_observed_exterior_source_mass (dim n) P (by omega) hlen r₀ p hp Cmass x (W n)
      (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have hG₀ (j) : G₀.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedCompleteInitial P.live.test pre.length) j := by
    rw [ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass (dim n) P.live.test P.live.ancestry (by omega) hlen
      Cmass x (W n) (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  by_cases hst : E.target=t
  · rw [←hst] at Hlaw
    simp only [native_two_level_incoming_product_self,native_two_level_power_product_self,
      integral_zero,Finset.sum_const_zero,add_zero] at Hlaw
    have hzero : nativeResetPairedProjectionValue (dim n) T P.live.test (M n) p q d center=0 := by
      simp only [native_generated_marked_canonical_rest_product] at Hlaw
      unfold nativeResetPairedProjectionValue
      convert Hlaw using 1
      congr 1
    rw [hzero,abs_zero]
    have hx:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW:0 ≤ W n:=hx.trans hxW
    have hs : 0 ≤ (M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length := by
      apply add_nonneg (M n).hxs.le
      exact (partitionPoint_mem (finiteCutMasses us r) (finiteCutMasses_ordered us hus r) pre.length).1
    apply native_reset_paired_budget_nonneg (dim n) _ _ d eta saving hCp hCh hC (M n).hxs.le hW
      (hW.trans hWv) hs <;> unfold sourceMonomialScale <;> positivity
  · have hc : ∀η ζ δ,p.tree.cavityLeft.atSlot (E.read η ζ δ) (p.tree.cavityLeftSlot p.mark)=E.D.atSlot δ t:=htRead
    have he : ∀η ζ δ,p.tree.cavityLeft.atSlot (E.read η ζ δ)
        (p.tree.cavityLeftSlot (p.embed e₀))=E.Ei.atSlot η e:=by
      simpa only [p.restRestrict_at] using heRead
    have Hbound:=hr pre mid tail hcut hindex hmass p.tree G (fun _=>NativeSourceFactorForm.centered)
      (nativeGeneratedExteriorInitial P.live.test pre.length) x hxsx hxW hG
      G₀ (fun _=>NativeSourceFactorForm.centered) (nativeGeneratedCompleteInitial P.live.test pre.length) hG₀
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) E e t hst
      (p.tree.cavityLeftSlot p.mark) (p.tree.cavityLeftSlot (p.embed e₀)) hc he _
      (fun σ=>native_generated_marked_reset_change (dim n) P.live.test P.live.ancestry ht (by omega) hlen
        e₀ hIn (M n) r₀ p hp σ) v hWv (by simpa only [hsplit] using hvr) hlow hz
    dsimp only [G₀] at Hbound
    simpa only [nativeResetPairedProjectionValue,nativeResetPairedBudget,
      native_generated_marked_canonical_rest_product,p.restRestrict_at,MarkedPlacement.restSpin] using Hbound

end OAI.SKFluctuations.LaplaceWindowFormalization
