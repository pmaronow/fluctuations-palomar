module

public import ComparisonSignedCavityActualResetPairedRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualGeneratedResetPairedStarIncomingOnEveryFinalNet
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
    ∀(r₀ : ℝ) (p : MarkedPlacement T),p∈T.markedAttach r₀ →
      U ≤ p.tree.splitIndex p.mark (p.embed P.live.test.target) →
    ∀v : ℝ,W n ≤ v →
      (M n).R (partitionPoint 0 as (p.tree.splitIndex (p.embed P.live.test.target) p.mark))=v →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
    |nativeResetPairedProjectionValue n T P.live.test (M n) p q d
      (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val)| ≤
      nativeResetPairedBudget n a b d eta saving Cp Ch Cpower Cbase (M n).xs (W n) v
        ((M n).xs+partitionPoint 0 as (pre.length+mid.length))
        (sourceMonomialScale x (W n) (nativeGeneratedExteriorInitial P.live.test pre.length))
        (sourceMonomialScale x (W n) (nativeGeneratedCompleteInitial P.live.test pre.length))

theorem actual_generated_reset_paired_star_incoming_from_canonical
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a b d : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (H : ActualCanonicalPairedStarIncomingOnEveryFinalNet a b d eta saving Cmass Cp Ch Cpower Cbase M W w) :
    ActualGeneratedResetPairedStarIncomingOnEveryFinalNet a b d eta saving Cmass Cp Ch Cpower Cbase M W w := by
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
  let G:=(nativeGeneratedExteriorShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r₀ p hp
  let G₀:=(nativeGeneratedCompleteShape n P.live.test P.live.ancestry (by omega) hlen).retainOnMarked r₀ p hp
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) j):ℝ))
  let center:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
  obtain ⟨E,t,e,htRead,heRead,hsplit,Hlaw⟩:=native_actual_reset_incoming_star_paired_source
    n pre mid tail hP hmid hU ht e₀ hIn hi r₀ p hp hh ho (M n) 0 q 0 d center
  have hG (j) : G.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedExteriorInitial P.live.test pre.length) j :=
    native_actual_observed_exterior_source_mass n P (by omega) hlen r₀ p hp Cmass x (W n)
      (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  have hG₀ (j) : G₀.sourceLowMass j ≤ Cmass*sourceFactorScale x (W n)
      (nativeGeneratedCompleteInitial P.live.test pre.length) j := by
    rw [ActualNaturalBoundaryShape.retained_source_mass]
    exact native_generated_complete_source_mass n P.live.test P.live.ancestry (by omega) hlen
      Cmass x (W n) (by simpa only [hcut] using hmi) (by simpa only [hcut] using hmass) j
  by_cases hst : E.target=t
  · rw [←hst] at Hlaw
    simp only [native_two_level_star_incoming_product_self,native_two_level_power_product_self,
      integral_zero,Finset.sum_const_zero,add_zero] at Hlaw
    have hzero : nativeResetPairedProjectionValue n T P.live.test (M n) p q d center=0 := by
      simp only [native_generated_marked_canonical_rest_product] at Hlaw
      unfold nativeResetPairedProjectionValue
      convert Hlaw using 1
      congr 1
    rw [hzero,abs_zero]
    have hx:0 ≤ x:=(M n).hxs.le.trans hxsx
    have hW:0 ≤ W n:=hx.trans hxW
    have hs : 0 ≤ (M n).xs+partitionPoint 0 (finiteCutMasses us r) (pre.length+mid.length) := by
      apply add_nonneg (M n).hxs.le
      exact (partitionPoint_mem (finiteCutMasses us r) (finiteCutMasses_ordered us hus r) (pre.length+mid.length)).1
    apply native_reset_paired_budget_nonneg n _ _ d eta saving hCp hCh hC (M n).hxs.le hW
      (hW.trans hWv) hs <;> unfold sourceMonomialScale <;> positivity
  · have hc : ∀η ζ δ,p.tree.cavityLeft.atSlot (E.read η ζ δ) (p.tree.cavityLeftSlot p.mark)=E.D.atSlot δ t:=htRead
    have he : ∀η ζ δ,p.tree.cavityLeft.atSlot (E.read η ζ δ)
        (p.tree.cavityLeftSlot (p.embed e₀))=E.Es.atSlot ζ e:=by
      simpa only [p.restRestrict_at] using heRead
    have Hbound:=hr pre mid tail hcut hindex hmass p.tree G (fun _=>NativeSourceFactorForm.centered)
      (nativeGeneratedExteriorInitial P.live.test pre.length) x hxsx hxW hG
      G₀ (fun _=>NativeSourceFactorForm.centered) (nativeGeneratedCompleteInitial P.live.test pre.length) hG₀
      (p.tree.cavityLeftSlot (p.embed P.live.test.target)) E e t hst
      (p.tree.cavityLeftSlot p.mark) (p.tree.cavityLeftSlot (p.embed e₀)) hc he _
      (fun σ=>native_generated_marked_reset_change n P.live.test P.live.ancestry ht (by omega) hlen
        e₀ hIn (M n) r₀ p hp σ) v hWv (by simpa only [hsplit] using hvr) hlow hz
    dsimp only [G₀] at Hbound
    simpa only [nativeResetPairedProjectionValue,nativeResetPairedBudget,
      native_generated_marked_canonical_rest_product,p.restRestrict_at,MarkedPlacement.restSpin] using Hbound

theorem exists_actual_bare_sharp_generated_reset_paired_bounds
    {m delta eta cl cu Az C0 Ct D Bclock Temp L Ccal : ℝ}
    (Cmass : ℝ) (hCm : 0 ≤ Cmass)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 < Temp) (hL : 0 < L) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=Temp) (hh : ∀n u,(M n).h u=0) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Temp L Cs (w n)) ∧
      (∀p : ℕ,ActualOriginalRestStarMomentOnEveryFinalNet p saving M W w) ∧
      (∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNet p saving M W w) ∧
      (∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNet j k saving M W w) ∧
      ∀a b d : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ∃Cstar : ℝ,0 < Cstar ∧ ∃Chstar : ℝ,0 < Chstar ∧
        ∃Cpower Cbase : ℕ→ℝ,(∀j,0 < Cpower j ∧ 0 < Cbase j) ∧
        ActualGeneratedResetPairedIncomingOnEveryFinalNet a b d eta saving Cmass Cp Ch Cpower Cbase M W w ∧
        ActualGeneratedResetPairedStarIncomingOnEveryFinalNet a b d eta saving Cmass Cstar Chstar Cpower Cbase M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,H⟩:=
    exists_actual_bare_sharp_all_paired_original_bounds Cmass hCm hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hL hCcal M W hcanonical hWlim hcompare hb hh
  refine ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,?_⟩
  intro a b d
  obtain ⟨Cp,hCp,Ch,hCh,Cstar,hCstar,Chstar,hChstar,Cpower,Cbase,hC,HI,HS⟩:=H a b d
  exact ⟨Cp,hCp,Ch,hCh,Cstar,hCstar,Chstar,hChstar,Cpower,Cbase,hC,
    actual_generated_reset_paired_incoming_from_canonical hCp.le hCh.le (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) HI,
    actual_generated_reset_paired_star_incoming_from_canonical hCstar.le hChstar.le
      (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) HS⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
