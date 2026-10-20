module

public import ComparisonSignedCavityActualResetPowerRate
public import ComparisonActualHighWallGammaPairedProductsAlong
public import ComparisonActualHighWallResetPairedRateAlong
public import ComparisonActualHighWallResetStarPairedRateAlong
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

def ActualHighWallGeneratedResetPowerOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (b d : ℕ) (eta saving Cmass : ℝ)
    (Cpower Cbase : ℕ→ℝ)
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
      P.live.test.edges.length=b → P.live.test.incoming=[] →
    ∀x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
    ∀(r₀ : ℝ) (p : MarkedPlacement T),p∈T.markedAttach r₀ →
      U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target) →
    ∀v : ℝ,W n ≤ v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).data.wallRadius (M n).alpha (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |actualGeneralResetPairedProjectionValue (dim n) T P.live.test (M n).bf (M n).hf p q d
      (orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val)| ≤
      ∑j∈Finset.range d,Cpower j*(((dim n):ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
        ((Cbase j)^b*sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))*
        ((((dim n)+1:ℕ):ℝ)^(-saving)*W n)^(d-1)

theorem actual_high_wall_generated_reset_power_from_canonical_along
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass : ℝ} {b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualHighWallOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ∀j,ActualHighWallCanonicalPowerProductOnEveryFinalNetAlong b j (d-1-j) eta saving Cmass
      (Cpower j) (Cbase j) M W w) :
    ActualHighWallGeneratedResetPowerOnEveryFinalNetAlong b d eta saving Cmass Cpower Cbase M W w := by
  have Hfin:=Filter.eventually_all.mpr (fun j : Fin d=>H j.val)
  filter_upwards [Hfin] with n hn
  intro L us hus hret hmesh hstar
  have Hgrid:=Filter.eventually_all.mpr (fun j : Fin d=>hn j L us hus hret hmesh hstar)
  filter_upwards [Hgrid] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hb hIn x hxsx hxW hmi
    r₀ p hp hh v hWv hvr hlow hz
  subst b
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  have hlen : pre.length+mid.length < (pre++(mid++tail)).length:=
    hU.trans_le (hh.trans (p.tree.splitIndex_le_clockLength _ _))
  let G₀:=(nativeGeneratedCompleteShape (dim n) P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r₀ p hp
  let q : ℕ→RestCoordinate (dim n)→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let center:=orderedPathS ((dim n)+1) (M n).bf (M n).hf (w n).star.val
  obtain ⟨E,t,htRead,hsplit,Hlaw⟩:=actual_general_reset_power_paired_source
    (dim n) pre mid tail hP hmid hU ht hIn r₀ p hp hh ho (M n).bf (M n).hf 0 q 0 d center
  have hG₀ (j) : G₀.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedCompleteInitial P.live.test pre.length) j := by
    rw [ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass (dim n) P.live.test P.live.ancestry (by omega) hlen
      Cmass x (W n) (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have HE : actualGeneralResetPairedProjectionValue (dim n) T P.live.test (M n).bf (M n).hf p q d center=
      ∑j∈Finset.range d,∫z,nativeTwoLevelPowerProduct (dim n) j (d-1-j) E.Ei E.Es E.D
        (fun η ζ δ=>(G₀.canonicalHighWallSource (M n) (fun _=>NativeSourceFactorForm.centered)).restProduct
          (E.read η ζ δ)) E.target t
        (fun l=>cumulativeIncrements (q 0) (fun l=>q (l+1)) (pre.length+l))
        (nativeStarSuffixClock (dim n) pre mid q) center (exteriorForestIRoot z) (exteriorForestStarRoot z)
        ∂nativeExteriorForestDisorderRootLaw (restWeight (dim n)) (restFeature (dim n)) pre mid tail 0 q 0 := by
    simp only [actual_general_generated_marked_canonical_rest_product] at Hlaw
    dsimp only [G₀]
    simp only [actual_general_generated_marked_canonical_rest_product]
    unfold actualGeneralResetPairedProjectionValue
    convert Hlaw using 1 <;> congr 3
  rw [HE]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  by_cases hst : E.target=t
  · rw [←hst]
    simp only [native_two_level_power_product_self,integral_zero,abs_zero]
    have h1:0 ≤ Cpower j:=(hC j).1
    have h2:0 ≤ Cbase j:=(hC j).2
    have hx:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW:0 ≤ W n:=hx.trans hxW
    unfold sourceMonomialScale
    positivity
  · have HJ:=hr ⟨j,Finset.mem_range.mp hj⟩ pre mid tail hcut hindex hmass p.tree G₀
      (fun _=>NativeSourceFactorForm.centered) (nativeGeneratedCompleteInitial P.live.test pre.length)
      x hxsx hxW hG₀ _ _ (p.tree.cavityLeftSlot (p.embed P.live.test.target))
      E.toNativeCanonicalExteriorSource t hst v hWv (by simpa only [hsplit] using hvr) hlow hz
    have hpow:j+(d-1-j)=d-1:=by have:=Finset.mem_range.mp hj;omega
    rw [hpow] at HJ
    convert HJ using 1

end OAI.SKFluctuations.LaplaceWindowFormalization
