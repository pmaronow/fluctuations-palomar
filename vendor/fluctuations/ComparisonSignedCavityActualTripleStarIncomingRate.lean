module

public import ComparisonSignedCavityTriplePairedValue
public import ComparisonSignedCavityActualPairedStarIncomingSourceErrorRate
public import ComparisonSignedCavityCanonicalLowFactor

@[expose] public section

noncomputable section
set_option maxHeartbeats 28000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualGeneratedTripleStarIncomingErrorOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a b d : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (Cpower Cbase : ℕ→ℝ)
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
    ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
    ∀(p : MarkedPlacement T),p∈T.markedAttach 0 →
    ∀(rr : MarkedPlacement p.tree),rr∈p.tree.markedAttach 0 →
    ∀(zz : MarkedPlacement rr.tree),zz∈rr.tree.markedAttach 0 →
      U ≤ p.tree.splitIndex (p.embed P.live.test.target) p.mark →
      U ≤ rr.tree.splitIndex (rr.embed (p.embed P.live.test.target)) rr.mark →
      U ≤ zz.tree.splitIndex (zz.embed (rr.embed (p.embed P.live.test.target))) zz.mark →
      zz.embed rr.mark ≠ zz.mark →
    ∀v : ℝ,W n ≤ v →
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeTripleResetPairedErrorValue n T P.live.test (M n) p rr zz q d
      (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val)| ≤
      (nativeResetPairedBudget n a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as (pre.length+mid.length))
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length)))*
        ((M n).xs+partitionPoint 0 as (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))

theorem actual_generated_triple_star_incoming_error_from_canonical
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ActualCanonicalPairedStarIncomingSourceErrorOnEveryFinalNet a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ActualGeneratedTripleStarIncomingErrorOnEveryFinalNet a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi x hxsx hxW hmi
    p hp rr hrr zz hzz hpH hrH hzH hef v hWv hvr hlow hz
  subst a
  subst b
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hlen : pre.length+mid.length<(pre++(mid++tail)).length:=
    hU.trans_le (hpH.trans (p.tree.splitIndex_le_clockLength _ _))
  let G:=(((nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 rr hrr).retainOnMarked 0 zz hzz
  let G₀:=(((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 rr hrr).retainOnMarked 0 zz hzz
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let center:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
  obtain ⟨E,t,e,f,i₀,htRead,heRead,hfRead,hiRead,hsplit,Hlaw⟩:=
    native_actual_triple_reset_incoming_star_error_source n pre mid tail hP hmid hU ht e₀ hIn hi
      p hp rr hrr zz hzz hpH hrH hzH ho (M n) 0 q 0 d center
  have hG (j) : G.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedExteriorInitial P.live.test pre.length) j := by
    simp only [G,ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_exterior_source_mass n P.live.test P.live.ancestry (by omega) hlen Cmass x (W n)
      (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have hG₀ (j) : G₀.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedCompleteInitial P.live.test pre.length) j := by
    simp only [G₀,ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass n P.live.test P.live.ancestry (by omega) hlen
      Cmass x (W n) (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have hraw : 0 ≤ (M n).xs+partitionPoint 0 (finiteCutMasses us r)
      (zz.tree.splitIndex (zz.embed rr.mark) zz.mark) :=
    add_nonneg (M n).hxs.le (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
  by_cases hst : E.target=t
  · rw [←hst] at Hlaw
    simp only [native_two_level_star_incoming_error_product_self,native_two_level_power_error_product_self,
      integral_zero,Finset.sum_const_zero,add_zero] at Hlaw
    have hzero : nativeTripleResetPairedErrorValue n T P.live.test (M n) p rr zz q d center=0 := by
      simp only [native_generated_triple_canonical_rest_product] at Hlaw
      unfold nativeTripleResetPairedErrorValue nativeStarSuffixClock
      simpa only [MarkedPlacement.restRestrict_at,MarkedPlacement.restSpin] using Hlaw
    rw [hzero,abs_zero]
    apply mul_nonneg _ hraw
    have hx:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW:0 ≤ W n:=hx.trans hxW
    have hs : 0 ≤ (M n).xs+partitionPoint 0 (finiteCutMasses us r) (pre.length+mid.length) :=
      add_nonneg (M n).hxs.le (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
    apply native_reset_paired_budget_nonneg n _ _ d eta saving hCp hCh hC (M n).hxs.le hW
      (hW.trans hWv) hs <;> unfold sourceMonomialScale <;> positivity
  · have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk (M n).context.hkc
      (M n).context.hm (M n).context.hM (M n).b (M n).h (M n).context.hd.ne' (M n).hlam.le
      (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
    have Hcenter:=native_ordered_source_center_eq_completed n (M n).bf (M n).hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
      (partitionPoint_mem (pre++(mid++tail)) ho (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))
    have Hbound:=hr pre mid tail hcut hindex hmass zz.tree G (fun _=>NativeSourceFactorForm.centered)
      (nativeGeneratedExteriorInitial P.live.test pre.length) x hxsx hxW hG
      G₀ (fun _=>NativeSourceFactorForm.centered) (nativeGeneratedCompleteInitial P.live.test pre.length) hG₀
      (zz.tree.cavityLeftSlot (zz.embed (rr.embed (p.embed P.live.test.target)))) E i₀ t hst
      (zz.tree.cavityLeftSlot (zz.embed (rr.embed p.mark)))
      (zz.tree.cavityLeftSlot (zz.embed (rr.embed (p.embed e₀)))) htRead hiRead _
      (fun σ=>native_generated_triple_reset_change n P.live.test P.live.ancestry ht (by omega) hlen
        e₀ hIn (M n) p hp rr hrr zz hzz σ) v hWv
      (by simpa only [hsplit,(rr.tree.markedAttach_embed_preserves 0 zz hzz).2,
        (p.tree.markedAttach_embed_preserves 0 rr hrr).2] using hvr) hlow hz
      (zz.tree.cavityLeftSlot (zz.embed rr.mark)) (zz.tree.cavityLeftSlot zz.mark)
      (fun H=>hef (zz.tree.cavityLeftSlot.injective H))
      (fun δ=>deletedOverlap n (joinSpin (E.D.atSlot δ e,false)) (joinSpin (E.D.atSlot δ f,false))-
        pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) (M n).bf (M n).hf) (orderedOverlap (n+1))
          (partitionPoint 0 (pre++(mid++tail)) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)))
      (fun η ζ δ=>by simp only [heRead,hfRead,cavityLeft_splitIndex,←hcut,Hcenter])
      (fun σ=>deletedOverlap n
        (joinSpin (zz.tree.cavityLeft.atSlot σ (zz.tree.cavityLeftSlot (zz.embed rr.mark)),false))
        (joinSpin (zz.restSpin σ,false))-
        pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
          (completedPathClock (n+1) (M n).bf (M n).hf) (orderedOverlap (n+1))
          (partitionPoint 0 (pre++(mid++tail)) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark)))
      (fun η ζ δ=>by simp only [MarkedPlacement.restSpin,heRead,hfRead])
    dsimp only [G₀] at Hbound
    unfold nativeStarSuffixClock at Hbound
    unfold nativeTripleResetPairedErrorValue nativeResetPairedBudget nativeStarSuffixClock
    simpa only [
      native_generated_triple_canonical_rest_product,MarkedPlacement.restRestrict_at,
      MarkedPlacement.restSpin,cavityLeft_splitIndex] using Hbound

end OAI.SKFluctuations.LaplaceWindowFormalization
