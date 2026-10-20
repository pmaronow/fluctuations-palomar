module

public import SKProof.Port.ComparisonActualOriginalQActualCurrentGaAlongContracts
public import ComparisonSignedCavityInheritedCurrentGaAlongNormalized
public import SKProof.Port.ComparisonActualOriginalQAnalyticBasics
public import SKProof.Port.ComparisonActualOriginalQResourcePhysicalFactories
public import SKProof.Port.ComparisonActualOriginalQPullbackFourInterfaces
public import SKProof.Port.ComparisonActualOriginalQSourceProjectionAlong
public import SKProof.Port.ComparisonActualOriginalQGaCurrentPrerequisites
public import SKProof.Port.ComparisonActualOriginalQInheritedCurrentGaAlongSpine

@[expose] public section

noncomputable section
set_option linter.unusedVariables false
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.SKFluctuations.LaplaceWindowFormalization.NativeOverlapMinimum
set_option maxHeartbeats 30000000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
open Classical
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Hierarchy Hierarchy.ClockTree Cavity LaplaceWindowFormalization NativeOverlapMinimum ActualThetaZeroOverlapMinimum
variable {dim : ℕ→ℕ}

theorem actual_normalized_spine_G_incoming_from_actual_along_original_q
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Temp Cg Cp Ch : ℝ} {a b d rBound : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hTemp : 0 ≤ Temp) (hCg : 0 ≤ Cg) (hsaving : 0 ≤ saving) (hCmass : 1 ≤ Cmass)
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (H : ActualGeneratedSpineGIncomingOnEveryFinalNetAlong_original_q a b d rBound eta saving Cmass Temp Cg Cp Ch Cpower Cbase M W w) :
    ActualNormalizedSpineGIncomingOnEveryFinalNetAlong_original_q a b d rBound eta Cmass Temp Cg (Cp*Ch^a)
      (∑j∈Finset.range d,Cpower j*(Cbase j)^b) M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
  have ho:MassOrdered 0 (finiteCutMasses us r):=finiteCutMasses_ordered us hus r
  have hu:0 ≤ partitionPoint 0 (finiteCutMasses us r) pre.length:=(partitionPoint_mem _ ho _).1
  have huW:partitionPoint 0 (finiteCutMasses us r) pre.length ≤ Cmass*W n:=
    (partitionPoint_mono _ ho (Nat.le_add_right _ _)).trans hmass
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs hu
  obtain ⟨hx,hxW,hmassx⟩:=native_capped_incoming_mass (M n).hxs.le (hxsW n) hu hCmass huW
  have Hraw:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    (min s (W n)) hx hxW hmassx V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
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
  have Hfinal:=Hraw.trans (mul_le_mul_of_nonneg_left Hnorm (show 0 ≤ Temp*Cg*v by positivity))
  simpa only [mul_one,←hscale] using Hfinal

theorem actual_normalized_spine_G_star_incoming_from_actual_along_original_q
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Temp Cg Cp Ch : ℝ} {a b d rBound : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hTemp : 0 ≤ Temp) (hCg : 0 ≤ Cg) (hsaving : 0 ≤ saving) (hCmass : 1 ≤ Cmass)
    (hCp : 0 ≤ Cp) (hCh : 0 ≤ Ch) (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (H : ActualGeneratedSpineGStarIncomingOnEveryFinalNetAlong_original_q a b d rBound eta saving Cmass Temp Cg Cp Ch Cpower Cbase M W w) :
    ActualNormalizedSpineGStarIncomingOnEveryFinalNetAlong_original_q a b d rBound eta Cmass Temp Cg (Cp*Ch^a*Real.sqrt (1+Cmass))
      (∑j∈Finset.range d,Cpower j*(Cbase j)^b) M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
  have ho:MassOrdered 0 (finiteCutMasses us r):=finiteCutMasses_ordered us hus r
  have hu:0 ≤ partitionPoint 0 (finiteCutMasses us r) pre.length:=(partitionPoint_mem _ ho _).1
  have huW:partitionPoint 0 (finiteCutMasses us r) pre.length ≤ Cmass*W n:=
    (partitionPoint_mono _ ho (Nat.le_add_right _ _)).trans hmass
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs hu
  obtain ⟨hx,hxW,hmassx⟩:=native_capped_incoming_mass (M n).hxs.le (hxsW n) hu hCmass huW
  have Hraw:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht ha hb e₀ hIn hi
    (min s (W n)) hx hxW hmassx V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
  have hscale:=native_generated_reset_incoming_star_source_scale P.live.test P.live.ancestry
    (by omega) ht e₀ hIn hi s (W n)
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hv:0<v:=hW.trans_le hWv
  have hx0:0 ≤ min s (W n):=(M n).hxs.le.trans hx
  have Hnorm:=native_reset_paired_budget_normalize (dim n) a b d eta hsaving hCp hCh (Real.sqrt_nonneg (1+Cmass)) hC
    (M n).hxs.le hW hv hW
    (show 0 ≤ sourceMonomialScale (min s (W n)) (W n) (nativeGeneratedExteriorInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (show 0 ≤ sourceMonomialScale (min s (W n)) (W n) (nativeGeneratedCompleteInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (show 0 ≤ sourceMonomialScale s (W n) (nativeGeneratedExteriorInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le)
    (by rw [←hscale];exact sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le)
    (savedWeightedExteriorScale_star_band (M n).hxs.le hW hv (by linarith : 0 ≤ Cmass) (hxsW n) hmass)
  have Hfinal:=Hraw.trans (mul_le_mul_of_nonneg_left Hnorm (show 0 ≤ Temp*Cg*v by positivity))
  simpa only [←hscale] using Hfinal

theorem actual_normalized_spine_G_power_from_actual_along_original_q
    {m delta cl cu Az C0 Ct D Bclock eta saving Cmass Temp Cg : ℝ} {b d rBound : ℕ}
    {Cpower Cbase : ℕ→ℝ}
    {M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (hTemp : 0 ≤ Temp) (hCg : 0 ≤ Cg) (hsaving : 0 ≤ saving) (hCmass : 1 ≤ Cmass)
    (hC : ∀j,0 ≤ Cpower j ∧ 0 ≤ Cbase j)
    (hxsW : ∀n,(M n).xs ≤ W n)
    (H : ActualGeneratedSpineGPowerOnEveryFinalNetAlong_original_q b d rBound eta saving Cmass Temp Cg Cpower Cbase M W w) :
    ActualNormalizedSpineGPowerOnEveryFinalNetAlong_original_q b d rBound eta Cmass Temp Cg
      (∑j∈Finset.range d,Cpower j*(Cbase j)^b) M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with r hr
  dsimp only at hr ⊢
  intro pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hb hIn
    V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
  have ho:MassOrdered 0 (finiteCutMasses us r):=finiteCutMasses_ordered us hus r
  have hu:0 ≤ partitionPoint 0 (finiteCutMasses us r) pre.length:=(partitionPoint_mem _ ho _).1
  have huW:partitionPoint 0 (finiteCutMasses us r) pre.length ≤ Cmass*W n:=
    (partitionPoint_mono _ ho (Nat.le_add_right _ _)).trans hmass
  let s:=(M n).xs+partitionPoint 0 (finiteCutMasses us r) pre.length
  have hs:0<s:=add_pos_of_pos_of_nonneg (M n).hxs hu
  obtain ⟨hx,hxW,hmassx⟩:=native_capped_incoming_mass (M n).hxs.le (hxsW n) hu hCmass huW
  have Hraw:=hr pre mid tail hcut hindex hmass T U depth seed P hP hmid hU ht hb hIn
    (min s (W n)) hx hxW hmassx V Q spine hcount p hp rr hrr zz hzz hpH hrH hzH hef hac hleaves v hWv hvr hlow hz
  have hW:0<W n:=(M n).hxs.trans_le (hxsW n)
  have hv:0<v:=hW.trans_le hWv
  have hx0:0 ≤ min s (W n):=(M n).hxs.le.trans hx
  apply Hraw.trans
  apply mul_le_mul_of_nonneg_left _ (show 0 ≤ Temp*Cg*v by positivity)
  exact native_reset_power_budget_normalize (dim n) b d eta hsaving hC hW hv
    (show 0 ≤ sourceMonomialScale s (W n) (nativeGeneratedCompleteInitial P.live.test pre.length) by
      unfold sourceMonomialScale;positivity)
    (sourceMonomialScale_mono_initial _ hx0 (min_le_left _ _) hW.le)

theorem eventually_inherited_same_star_spine_G_normalized_bounds_along_original_q (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (Cmass : ℝ) (hCm : 1 ≤ Cmass)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→ActualThetaZeroOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).directTestWorkingScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).data.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,ActualOriginalQSmallSourceClocks (M n) Temp Cf)
    (hcutoff : ∀ᶠn : ℕ in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_original_q j k saving M W w) :
      (∀a b d rBound : ℕ,∃Cg Ai Ap : ℝ,0<Cg ∧ 0≤Ai ∧ 0≤Ap ∧
        ActualNormalizedSpineGIncomingOnEveryFinalNetAlong_original_q a b d rBound eta Cmass Temp Cg Ai Ap M W w) ∧
      (∀a b d rBound : ℕ,∃Cg Ai Ap : ℝ,0<Cg ∧ 0≤Ai ∧ 0≤Ap ∧
        ActualNormalizedSpineGStarIncomingOnEveryFinalNetAlong_original_q a b d rBound eta Cmass Temp Cg Ai Ap M W w) ∧
      ∀b d rBound : ℕ,∃Cg Ap : ℝ,0<Cg ∧ 0≤Ap ∧
        ActualNormalizedSpineGPowerOnEveryFinalNetAlong_original_q b d rBound eta Cmass Temp Cg Ap M W w := by
  obtain ⟨HI,HS,HP⟩:=
    eventually_inherited_same_star_spine_G_word_bounds_along_original_q hdim Cmass (by linarith) hm hdelta hroom hgap
      hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare hsource hcutoff saving w Hmixed
  have hxW (n) : (M n).xs ≤ W n := by
    rw [hcanonical n]
    exact le_max_left _ _
  refine ⟨?_,?_,?_⟩
  · intro a b d rBound
    obtain ⟨Cg,hCg,Cp,hCp,Ch,hCh,Cpower,Cbase,hC,H⟩:=HI a b d rBound
    refine ⟨Cg,Cp*Ch^a,∑j∈Finset.range d,Cpower j*(Cbase j)^b,hCg,by positivity,?_,?_⟩
    · exact Finset.sum_nonneg (fun j _=>mul_nonneg (hC j).1.le (pow_nonneg (hC j).2.le _))
    · exact actual_normalized_spine_G_incoming_from_actual_along_original_q hTemp hCg.le hsaving hCm
        hCp.le hCh.le (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) hxW H
  · intro a b d rBound
    obtain ⟨Cg,hCg,Cp,hCp,Ch,hCh,Cpower,Cbase,hC,H⟩:=HS a b d rBound
    refine ⟨Cg,Cp*Ch^a*Real.sqrt (1+Cmass),∑j∈Finset.range d,Cpower j*(Cbase j)^b,hCg,by positivity,?_,?_⟩
    · exact Finset.sum_nonneg (fun j _=>mul_nonneg (hC j).1.le (pow_nonneg (hC j).2.le _))
    · exact actual_normalized_spine_G_star_incoming_from_actual_along_original_q hTemp hCg.le hsaving hCm
        hCp.le hCh.le (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) hxW H
  · intro b d rBound
    obtain ⟨Cg,hCg,Cpower,Cbase,hC,H⟩:=HP b d rBound
    refine ⟨Cg,∑j∈Finset.range d,Cpower j*(Cbase j)^b,hCg,?_,?_⟩
    · exact Finset.sum_nonneg (fun j _=>mul_nonneg (hC j).1.le (pow_nonneg (hC j).2.le _))
    · exact actual_normalized_spine_G_power_from_actual_along_original_q hTemp hCg.le hsaving hCm
        (fun j=>⟨(hC j).1.le,(hC j).2.le⟩) hxW H

end OAI.SKFluctuations.LaplaceWindowFormalization
