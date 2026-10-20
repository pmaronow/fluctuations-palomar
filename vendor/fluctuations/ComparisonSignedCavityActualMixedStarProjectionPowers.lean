module

public import ComparisonSignedCavityMixedStarProjectionPowers

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Cavity NativeOverlapMinimum

def ActualMixedStarProjectionPowersOnEveryFinalNet
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (j k : ℕ) (saving : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀us : List PositiveMass,(∀u∈us,u.val ≤ 1) → (w n).star∈us →
    ∀ᶠr : ℕ in atTop,
      let as:=finiteCutMasses us r
      let q : ℕ → RestCoordinate n → ℝ:=fun l=>Sum.elim
        (fun _=>((M n).bf (partitionPoint 0 as l):ℝ))
        (fun _=>((M n).hf (partitionPoint 0 as l):ℝ))
      let center:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
      ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
        pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      ∀(T : ClockTree (Spin n) tail) (s t : T.Slot),
        let qs:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+(mid.length+l))
        nativeRootTestExpect n T qs
          (nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0)
          exteriorForestStarRoot
          (fun z σ=>(nativeStarCenteredProjection n tail qs center (exteriorForestStarRoot z) (T.atSlot σ s)^j*
            nativeStarCenteredProjection n tail qs center (exteriorForestStarRoot z) (T.atSlot σ t)^k)^2) ≤
          (((n+1:ℕ):ℝ)^(-saving)*W n)^(2*(j+k))

theorem actual_star_projection_powers_to_mixed
    {m delta cl cu Az C0 Ct D Bclock saving : ℝ}
    (j k : ℕ) (M : (n:ℕ)→NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hW : ∀n,0 ≤ W n) (w : ℕ→ActualSlowWindowChoice)
    (H : ∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNet p saving M W w) :
    ActualMixedStarProjectionPowersOnEveryFinalNet j k saving M W w := by
  filter_upwards [H (2*j-1),H (2*k-1)] with n hnJ hnK
  intro us hus hstar
  filter_upwards [hnJ us hus hstar,hnK us hus hstar] with r hrJ hrK
  dsimp only at hrJ hrK ⊢
  intro pre mid tail hcut hindex T s t
  let q : ℕ → RestCoordinate n → ℝ:=fun l=>Sum.elim
    (fun _=>((M n).bf (partitionPoint 0 (finiteCutMasses us r) l):ℝ))
    (fun _=>((M n).hf (partitionPoint 0 (finiteCutMasses us r) l):ℝ))
  let qs:=fun l=>cumulativeIncrements (q 0) (fun r=>q (r+1)) (pre.length+(mid.length+l))
  let center:=orderedPathS (n+1) (M n).bf (M n).hf (w n).star.val
  let μ:=nativeExteriorForestDisorderRootLaw (restWeight n) (restFeature n) pre mid tail 0 q 0
  have ho : MassOrdered 0 (pre++(mid++tail)):=hcut.symm ▸ finiteCutMasses_ordered us hus r
  let := nativeExteriorForestDisorderRootLaw_probability (restWeight_pos n) (restFeature n)
    pre mid tail ho 0 q 0
  apply native_star_projection_mixed_power_second_le n j k T ho.suffix_end.suffix_end qs μ
    exteriorForestStarRoot departedAnchorExteriorRoot_measurable center s t
    (((n+1:ℕ):ℝ)^(-saving)*W n) (mul_nonneg (Real.rpow_nonneg (by positivity) _) (hW n))
  · by_cases hj : j=0
    · subst j
      simp only [mul_zero,pow_zero,nativeRootTestExpect]
      simp only [T.expect_const (restWeight_pos n) (restFeature n) ho.suffix_end.suffix_end]
      simp
    · have he : 2*(2*j-1+1)=4*j := by omega
      simpa only [he,nativeRootTestExpect,qs,μ,q,center] using hrJ pre mid tail hcut hindex T s
  · by_cases hk : k=0
    · subst k
      simp only [mul_zero,pow_zero,nativeRootTestExpect]
      simp only [T.expect_const (restWeight_pos n) (restFeature n) ho.suffix_end.suffix_end]
      simp
    · have he : 2*(2*k-1+1)=4*k := by omega
      simpa only [he,nativeRootTestExpect,qs,μ,q,center] using hrK pre mid tail hcut hindex T t

theorem exists_actual_bare_sharp_star_all_mixed_projection_powers
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
      (∀p : ℕ,ActualOriginalStarProjectionPowerOnEveryFinalNet p saving M W w) ∧
      ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNet j k saving M W w := by
  obtain ⟨hs,Cs,hCs,w,hw,Hrest,Hpow⟩:=exists_actual_bare_sharp_star_projection_powers_on_every_final_net
    hm hdelta hroom hcl hcu hAz hC0 hCt hT hL hCcal M W hcanonical hWlim hcompare hb hh
  have hW n : 0 ≤ W n := by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_pos.le
  exact ⟨hs,Cs,hCs,w,hw,Hrest,Hpow,fun j k=>actual_star_projection_powers_to_mixed j k M W hW w Hpow⟩

end OAI.SKFluctuations.LaplaceWindowFormalization
