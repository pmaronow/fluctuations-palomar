module

public import ComparisonSignedCavityActualTripleStarIncomingRate
public import ComparisonSignedCavityActualPowerSourceErrorProductRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualGeneratedTriplePowerErrorOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d : ℕ) (eta saving Cmass : ℝ)
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
      P.live.test.edges.length=b → P.live.test.incoming=[] →
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
      (∑j∈Finset.range d,Cpower j*((n:ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
        ((Cbase j)^b*sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))*
        (((n+1:ℕ):ℝ)^(-saving)*W n)^(d-1))*
        ((M n).xs+partitionPoint 0 as (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))

theorem actual_generated_triple_power_error_from_canonical
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass : ℝ} {b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ∀j,ActualCanonicalPowerSourceErrorProductOnEveryFinalNet b j (d-1-j) eta saving Cmass
      (Cpower j) (Cbase j) M W w) :
    ActualGeneratedTriplePowerErrorOnEveryFinalNet b d eta saving Cmass Cpower Cbase M W w := by
  have Hfin:=Filter.eventually_all.mpr (fun j : Fin d=>H j.val)
  filter_upwards [Hfin] with n hn
  intro L us hus hret hmesh hstar
  have Hgrid:=Filter.eventually_all.mpr (fun j : Fin d=>hn j L us hus hret hmesh hstar)
  filter_upwards [Hgrid] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hb hIn x hxsx hxW hmi
    p hp rr hrr zz hzz hpH hrH hzH hef v hWv hvr hlow hz
  subst b
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hlen : pre.length+mid.length < (pre++(mid++tail)).length:=
    hU.trans_le (hpH.trans (p.tree.splitIndex_le_clockLength _ _))
  let G₀:=(((nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked 0 p hp).retainOnMarked 0 rr hrr).retainOnMarked 0 zz hzz
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let center:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
  obtain ⟨E,t,e,f,htRead,heRead,hfRead,hsplit,Hlaw⟩:=native_actual_triple_reset_power_error_source
    n pre mid tail hP hmid hU ht hIn p hp rr hrr zz hzz hpH hrH hzH ho (M n) 0 q 0 d center
  have hG₀ (j) : G₀.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedCompleteInitial P.live.test pre.length) j := by
    simp only [G₀,ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass n P.live.test P.live.ancestry (by omega) hlen
      Cmass x (W n) (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  let error:=fun δ=>deletedOverlap n (joinSpin (E.D.atSlot δ e,false)) (joinSpin (E.D.atSlot δ f,false))-
    pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) (M n).bf (M n).hf) (orderedOverlap (n+1))
      (partitionPoint 0 (pre++(mid++tail)) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))
  have HE : nativeTripleResetPairedErrorValue n T P.live.test (M n) p rr zz q d center=
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerErrorProduct n j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>(G₀.canonicalMinimumSource (M n) (fun _=>NativeSourceFactorForm.centered)).restProduct
          (E.read η ζ δ)) E.target t
        (fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+l))
        (nativeStarSuffixClock n pre mid q) center error (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0 := by
    simp only [native_generated_triple_canonical_rest_product] at Hlaw
    dsimp only [G₀]
    simp only [native_generated_triple_canonical_rest_product]
    unfold nativeTripleResetPairedErrorValue nativeStarSuffixClock
    simpa only [MarkedPlacement.restRestrict_at,MarkedPlacement.restSpin,error] using Hlaw
  rw [HE,Finset.sum_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  by_cases hst : E.target=t
  · rw [←hst]
    simp only [native_two_level_power_error_product_self,integral_zero,abs_zero]
    have h1:0 ≤ Cpower j:=(hC j).1
    have h2:0 ≤ Cbase j:=(hC j).2
    have hx:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW:0 ≤ W n:=hx.trans hxW
    have hu:0 ≤ partitionPoint 0 (finiteCutMasses us r) (zz.tree.splitIndex (zz.embed rr.mark) zz.mark):=
      (partitionPoint_mem _ (finiteCutMasses_ordered us hus r) _).1
    have hxs:0 ≤ (M n).xs:=(M n).hxs.le
    unfold sourceMonomialScale
    positivity
  · have had:=comparisonVariableEndpoint_clocks_admissible (M n).context.hc (M n).context.hk (M n).context.hkc
      (M n).context.hm (M n).context.hM (M n).b (M n).h (M n).context.hd.ne' (M n).hlam.le
      (M n).hlb (M n).hb (M n).hh (M n).hh0 (M n).alpha
    have Hcenter:=native_ordered_source_center_eq_completed n (M n).bf (M n).hf
      (toNNReal_monotoneOn had.1) (toNNReal_monotoneOn had.2.1)
      (partitionPoint_mem (pre++(mid++tail)) ho (zz.tree.splitIndex (zz.embed rr.mark) zz.mark))
    have HJ:=hr ⟨j,Finset.mem_range.mp hj⟩ pre mid tail hcut hindex hmass zz.tree G₀
      (fun _=>NativeSourceFactorForm.centered) (nativeGeneratedCompleteInitial P.live.test pre.length)
      x hxsx hxW hG₀ _ _ (zz.tree.cavityLeftSlot (zz.embed (rr.embed (p.embed P.live.test.target))))
      E.toNativeCanonicalExteriorSource t hst v hWv
      (by simpa only [hsplit,(rr.tree.markedAttach_embed_preserves 0 zz hzz).2,
        (p.tree.markedAttach_embed_preserves 0 rr hrr).2] using hvr) hlow hz
      (zz.tree.cavityLeftSlot (zz.embed rr.mark)) (zz.tree.cavityLeftSlot zz.mark)
      (fun H=>hef (zz.tree.cavityLeftSlot.injective H)) error
      (fun η ζ δ=>by simp only [error,heRead,hfRead,cavityLeft_splitIndex,←hcut,Hcenter])
    have hpow:j+(d-1-j)=d-1:=by have:=Finset.mem_range.mp hj;omega
    rw [hpow] at HJ
    simpa only [cavityLeft_splitIndex] using HJ

end OAI.SKFluctuations.LaplaceWindowFormalization
