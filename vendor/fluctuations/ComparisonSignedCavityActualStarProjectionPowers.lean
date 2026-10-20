module

public import ComparisonSignedCavityStarProjectionPowerMoments
public import ComparisonSignedCavityActualSharpStarAllOrder

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum

def ActualOriginalStarProjectionPowerOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (p : ℕ) (saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠk : ℕ in atTop,
      let as:=finiteCutMasses us k
      let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as j):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as j):ℝ))
      let center:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      ∀(T : ClockTree (Spin n) tail) (s : T.Slot),
        let qs:=fun j=>cumulativeIncrements (q 0) (fun k=>q (k+1)) (pre.length+(mid.length+j))
        (∫z,T.expect (restWeight n) (restFeature n) qs
          (fun σ=>|nativeStarCenteredProjection n tail qs center (exteriorForestStarRoot z) (T.atSlot σ s)|^(2*(p+1)))
          (exteriorForestStarRoot z)
          ∂nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0) ≤
          (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1))

theorem actual_rest_star_to_projection_powers
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (p : ℕ) (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice)
    (H : ActualOriginalRestStarMomentOnEveryFinalNet p saving M W w) :
    ActualOriginalStarProjectionPowerOnEveryFinalNet p saving M W w := by
  filter_upwards [H] with n hn
  intro us hus hstar
  filter_upwards [hn us hus hstar] with k hk
  dsimp only at hk ⊢
  intro pre mid tail hcut hindex T s
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus k
  apply (native_common_star_projection_power_le_original_pair n (2*(p+1)) pre mid tail ho T s
    0 _ (orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val) 0).trans
  have HK (bs : List PositiveMass) (hbs : bs=finiteCutMasses us k) (j : ℕ)
      (hj : j=retainedMassPrefixIndex (w n).star.val (finiteCutMasses us k)) :
      (ClockTree.pairClock bs j).disorderExpect (restWeight n) (restFeature n) 0
        (fun j=>Sum.elim (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ))
          (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)))
        (fun σ=>|deletedOverlap n (joinSpin ((ClockTree.pairSpin bs j σ).1,false))
          (joinSpin ((ClockTree.pairSpin bs j σ).2,false))-
            orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val|^(2*(p+1))) 0 ≤
        (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*(p+1)) := by
    subst bs j
    exact hk
  exact HK _ hcut _ hindex

theorem exists_actual_bare_sharp_star_projection_powers_on_every_final_net
    {m delta cl cu Az C0 Ct D Bclock T L Ccal : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hT : 0 < T) (hL : 0 < L) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hb : ∀n u,(M n).b u=T) (hh : ∀n u,(M n).h u=0) :
    let saving:=actualSlowWindowExponent m delta/256
    0 < saving ∧ ∃Cs : ℝ,0 < Cs ∧ ∃w : ℕ→ActualSlowWindowChoice,
      (∀ᶠn : ℕ in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) T L Cs (w n)) ∧
      (∀p : ℕ,ActualOriginalRestStarMomentOnEveryFinalNet p saving M W w) ∧
      ∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNet p saving M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,H,Hfinite⟩:=exists_actual_bare_sharp_native_star_on_every_final_net
    hm hdelta hroom hcl hcu hAz hC0 hCt hT hL hCcal M W hcanonical hWlim hcompare hb hh
  have hxs n : (M n).xs ≤ W n := by
    rw [hcanonical]
    exact le_max_left _ _
  have hsite : actualSlowWindowExponent m delta/128 < (5:ℝ)/6+m := by
    have Hc:=(actualSlowWindowExponent_bounds hm hdelta).2.2
    linarith
  have Hrest (p : ℕ) : ActualOriginalRestStarMomentOnEveryFinalNet p
      (actualSlowWindowExponent m delta/256) M W w := by
    have HG:=actual_native_star_every_final_net_to_rest p hcl hAz hC0 hs hsite M W hxs hWlim hb hh w (H p)
    simpa only [show (actualSlowWindowExponent m delta/128)/2=actualSlowWindowExponent m delta/256 by ring] using HG
  refine ⟨by linarith,Cs,hCs,w,hw,Hrest,?_⟩
  intro p
  exact actual_rest_star_to_projection_powers p M W w (Hrest p)

end OAI.SKFluctuations.LaplaceWindowFormalization
