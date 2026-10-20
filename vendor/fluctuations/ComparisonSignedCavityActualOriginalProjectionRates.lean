module

public import ComparisonSignedCavityDynamicProjectionAllocation
public import ComparisonSignedCavityActualPowerProductRate

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity NativeOverlapMinimum

def ActualOriginalIncomingProjectionOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a j k : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
    ∀ᶠr : ℕ in atTop,
      let as:=finiteCutMasses us r
      let q : ℕ → RestCoordinate n → ℝ:=fun l=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as l):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
      let center:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
        partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
        (G : ActualNaturalBoundaryShape n a T) (f : Fin a → NativeSourceFactorForm)
        (initial : Finset (Fin a)) (x : ℝ),
        (M n).xs ≤ x → x ≤ W n → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
      ∀(s : T.cavityLeft.Slot)
        (E : NativeDynamicCanonicalExteriorSource n a pre mid tail T s (G.canonicalMinimumSource (M n) f) 0 q 0)
        (e : E.Ei.Slot) (t : E.D.Slot),E.target ≠ t →
      ∀(c e₀ : T.cavityLeft.Slot),
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t) →
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) e₀=E.Ei.atSlot η e) →
      ∀v : ℝ,W n ≤ v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
        let qs:=nativeStarSuffixClock n pre mid q
        |nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
          (pre.length+mid.length) 0 q
          (fun y σ=>
            let Y:=nativeStarCenteredProjection n tail qs center y
            (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))*
              (G.canonicalMinimumSource (M n) f).restProduct σ*
              (deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ c,false))
                  (joinSpin (T.cavityLeft.atSlot σ e₀,false))-
                deletedOverlap n (joinSpin (T.cavityLeft.atSlot σ s,false))
                  (joinSpin (T.cavityLeft.atSlot σ e₀,false)))*
              (Y (T.cavityLeft.atSlot σ s)^j*Y (T.cavityLeft.atSlot σ c)^k)) 0| ≤
          Cp*((n:ℝ)^(-eta))^2*savedProjectedScale (M n).xs (W n) v*
            savedWeightedExteriorScale (M n).xs (W n) v ((M n).xs+partitionPoint 0 as pre.length)*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            (((n+1:ℕ):ℝ)^(-saving)*W n)^(j+k)

def ActualOriginalPowerProjectionOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (a j k : ℕ) (eta saving Cmass Cp Ch : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
    ∀ᶠr : ℕ in atTop,
      let as:=finiteCutMasses us r
      let q : ℕ → RestCoordinate n → ℝ:=fun l=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as l):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
      let center:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
        partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n →
      ∀(T : ClockTree (Spin n×Bool) (pre++(mid++tail)))
        (G : ActualNaturalBoundaryShape n a T) (forms : Fin a → NativeSourceFactorForm)
        (initial : Finset (Fin a)) (x : ℝ),
        (M n).xs ≤ x → x ≤ W n → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x (W n) initial e) →
      ∀(b : ℕ) (GH : ActualNaturalBoundaryShape n b T) (s : T.cavityLeft.Slot)
        (E : NativeDynamicCanonicalExteriorSource n b pre mid tail T s GH 0 q 0)
        (t : E.D.Slot),E.target ≠ t →
      ∀c : T.cavityLeft.Slot,
        (∀η ζ δ,T.cavityLeft.atSlot (E.read η ζ δ) c=E.D.atSlot δ t) →
      ∀v : ℝ,W n ≤ v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length+E.D.splitIndex E.target t))=v →
        (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ v/2 → (M n).z ≤ v/2 →
        let qs:=nativeStarSuffixClock n pre mid q
        |nativeStarFieldDisorderMean (restWeight n) (restFeature n) T.cavityLeft s
          (pre.length+mid.length) 0 q
          (fun y σ=>
            let Y:=nativeStarCenteredProjection n tail qs center y
            (Y (T.cavityLeft.atSlot σ c)-Y (T.cavityLeft.atSlot σ s))^2*
              (G.canonicalMinimumSource (M n) forms).restProduct σ*
              (Y (T.cavityLeft.atSlot σ s)^j*Y (T.cavityLeft.atSlot σ c)^k)) 0| ≤
          Cp*((n:ℝ)^(-eta))^2*(savedProjectedScale (M n).xs (W n) v)^2*
            (Ch^a*sourceMonomialScale x (W n) initial)*
            (((n+1:ℕ):ℝ)^(-saving)*W n)^(j+k)

theorem actual_original_incoming_projection_of_canonical
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a j k : ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualCanonicalIncomingProductOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w) :
    ActualOriginalIncomingProjectionOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG s E e t hst c e₀ hc he
    v hWv hvr hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  apply (congrArg abs (E.incoming_i_projection_law ho c e₀ t e hc he j k
    (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val))).le.trans
  exact hr pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG s
    E.toNativeCanonicalExteriorSource e t hst v hWv hvr hlow hz

theorem actual_original_power_projection_of_canonical
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Cp Ch : ℝ} {a j k : ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualCanonicalPowerProductOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w) :
    ActualOriginalPowerProjectionOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG b GH s E t hst c hc
    v hWv hvr hlow hz
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  apply (congrArg abs (E.power_projection_law ho c t hc
    (G.canonicalMinimumSource (M n) forms).restProduct j k
    (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val))).le.trans
  exact hr pre mid tail hcut hindex hmass T G forms initial x hxsx hxW hG b GH s
    E.toNativeCanonicalExteriorSource t hst v hWv hvr hlow hz

theorem exists_actual_bare_sharp_original_projected_allocations
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
      (∀a j k : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ActualOriginalIncomingProjectionOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w) ∧
      ∀a j k : ℕ,∃Cp : ℝ,0 < Cp ∧ ∃Ch : ℝ,0 < Ch ∧
        ActualOriginalPowerProjectionOnEveryFinalNet a j k eta saving Cmass Cp Ch M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,HI,HP⟩:=
    exists_actual_bare_sharp_canonical_polarized_products Cmass hCm hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hL hCcal M W hcanonical hWlim hcompare hb hh
  refine ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,Hmixed,?_,?_⟩
  · intro a j k
    obtain ⟨Cp,hCp,Ch,hCh,H⟩:=HI a j k
    exact ⟨Cp,hCp,Ch,hCh,actual_original_incoming_projection_of_canonical H⟩
  · intro a j k
    obtain ⟨Cp,hCp,Ch,hCh,H⟩:=HP a j k
    exact ⟨Cp,hCp,Ch,hCh,actual_original_power_projection_of_canonical H⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
