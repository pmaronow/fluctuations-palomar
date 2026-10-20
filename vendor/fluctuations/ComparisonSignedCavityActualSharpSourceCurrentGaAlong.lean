module

public import ComparisonSignedCavityInheritedFourGaCurrentRootsAlong
public import ComparisonSignedCavityActualSharpSourceCutReadout

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 24000000
variable {dim : ℕ→ℕ}

def ActualSharpSourceGaInitialOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta Cmass C : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
  ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let U:=retainedMassPrefixIndex (high n).val as
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as → 0 < mid.length →
      ∃hs : pre.length+mid.length<U,∃hU : U≤(pre++(mid++tail)).length,
      ∀a x : ℝ,(M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
      ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
        [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) a (by omega)]).map
        (fun Q=>|nativeActualOriginalFourGaCurrentError (M n) U (W n) Q|)).sum ≤
        C*(dim n:ℝ)^(-eta)*(M n).xs^2*x

def ActualSharpSourceGaConstantOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta C : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) (high outer : ℕ→PositiveMass) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs →
    (w n).star∈us → high n∈us → outer n∈us →
  ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let U:=retainedMassPrefixIndex (high n).val as
    ∀(mid tail : List PositiveMass),mid++tail=as →
      mid.length=retainedMassPrefixIndex (w n).star.val as →
      ∃hs : mid.length<U,∃hU : U≤(mid++tail).length,
      ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
        [(nativeActualConstantState (mid++tail) 0 mid.length).projection (hs.le.trans hU)]).map
        (fun Q=>|nativeActualOriginalFourGaCurrentError (M n) U (W n) Q|)).sum ≤
        C*(dim n:ℝ)^(-eta)*(M n).xs^2

theorem ActualFourGaCurrentInitialOnEveryFinalNetAlong.on_sharp_source_cuts
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C cFirst A : ℝ} {depth : ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W radius : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice} {high outer : ℕ→PositiveMass}
    (H : ActualFourGaCurrentInitialOnEveryFinalNetAlong depth eta Cmass cK C M W w)
    (hxs : ∀n,(M n).xs ≤ W n) (hA : A ≤ Cmass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ActualSharpSourceGaInitialOnEveryFinalNetAlong depth eta Cmass C M W w high outer := by
  filter_upwards [H,Hcuts] with n hn hnCuts
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,Hrad,Hrad1,HRU,HRstar,Hrz,HK,_⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter j
  intro pre mid tail hcut hindex hmid
  have hs : pre.length+mid.length<retainedMassPrefixIndex (high n).val (finiteCutMasses us j):=by
    rw [hindex]
    exact Hs
  have hU : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤(pre++(mid++tail)).length:=by
    rw [hcut]
    exact HUV.le.trans HV
  refine ⟨hs,hU,?_⟩
  intro a x hx hxW hmi
  have HW : 0≤W n:=((M n).hxs.trans_le (hxs n)).le
  have Hmass' : partitionPoint 0 (finiteCutMasses us j) (pre.length+mid.length) ≤ Cmass*W n:=by
    rw [hindex]
    exact Hmass.trans (mul_le_mul_of_nonneg_right hA HW)
  exact hj pre mid tail hcut hindex Hmass' hmid _ hs hU a x (radius n) hx hxW hmi
    Hrad Hrad1 HRU (by simpa only [hindex] using HRstar) Hrz
    (by simpa only [hindex] using HK)

theorem ActualFourGaCurrentProjectedConstantOnEveryFinalNetAlong.on_sharp_source_cuts
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C cFirst A : ℝ} {depth : ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W radius : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice} {high outer : ℕ→PositiveMass}
    (H : ActualFourGaCurrentProjectedConstantOnEveryFinalNetAlong depth eta Cmass cK C M W w)
    (hxs : ∀n,(M n).xs ≤ W n) (hA : A ≤ Cmass)
    (Hcuts : ∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (radius n) cFirst cK A) :
    ActualSharpSourceGaConstantOnEveryFinalNetAlong depth eta C M W w high outer := by
  filter_upwards [H,Hcuts] with n hn hnCuts
  intro L us hus hret hmesh hstar hhigh houter
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  obtain ⟨Hs,HUV,HV,Hfirst,Hmass,_,Hrad,Hrad1,HRU,HRstar,Hrz,HK,_⟩:=
    hnCuts.finite_net_readout us hus hstar hhigh houter j
  intro mid tail hcut hindex
  have hs : mid.length<retainedMassPrefixIndex (high n).val (finiteCutMasses us j):=by
    rw [hindex]
    exact Hs
  have hU : retainedMassPrefixIndex (high n).val (finiteCutMasses us j)≤(mid++tail).length:=by
    rw [hcut]
    exact HUV.le.trans HV
  refine ⟨hs,hU,?_⟩
  have HW : 0≤W n:=((M n).hxs.trans_le (hxs n)).le
  have Hmass' : partitionPoint 0 (finiteCutMasses us j) mid.length ≤ Cmass*W n:=by
    rw [hindex]
    exact Hmass.trans (mul_le_mul_of_nonneg_right hA HW)
  exact hj mid tail hcut hindex Hmass' _ hs hU (radius n)
    Hrad Hrad1 HRU (by simpa only [hindex] using HRstar) Hrz
    (by simpa only [hindex] using HK)

def ActualSharpSourceCurrentGaAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (eta : ℝ)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∃Ku Kv cFirst cK : ℝ,1 < Ku ∧ 1 ≤ Kv ∧ 0 < cFirst ∧
    2*cu*(Az+1) ≤ cFirst ∧ 0 < cK ∧ ∃high outer : ℕ→PositiveMass,
    (∀n,(high n).val=Ku*W n ∧ (outer n).val=(Ku+1)*W n) ∧
    (∀ᶠn in atTop,ActualSharpSourceCutGeometry (M n) (W n) (w n)
      (high n) (outer n) (Kv*W n) cFirst cK (Ku+1)) ∧
    ∀depth : ℕ,∃Ci Cc : ℝ,0<Ci ∧ 0<Cc ∧
      ActualSharpSourceGaInitialOnEveryFinalNetAlong depth eta (Ku+1) Ci M W w high outer ∧
      ActualSharpSourceGaConstantOnEveryFinalNetAlong depth eta Cc M W w high outer

theorem actual_inherited_same_star_sharp_source_current_Ga_along
    (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal Tstar L Cs : ℝ}
    (heta : 0 < eta) (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hgap : 2*eta < 6*m) (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az)
    (hC0 : 0 < C0) (hCt : 0 ≤ Ct) (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf)
    (hCcal : 1 ≤ Ccal) (hTstar : 0 < Tstar) (hL : 0 < L)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w)
    (hw : ∀ᶠn in atTop,IsActualSharpCalibratedSlowWindow (M n) (W n) Tstar L Cs (w n)) :
    ActualSharpSourceCurrentGaAlong eta M W w := by
  have hxs n : (M n).xs ≤ W n:=by
    rw [hcanonical]
    exact (M n).canonical_direct_test_band_ge_scale
  obtain ⟨Ku,Kv,cFirst,cK,hKu,hKv,hFirst,hFirstLower,hcK,high,outer,Hvalues,Hcuts⟩:=
    exists_actual_sharp_source_cuts_along hcl hcu hAz hTstar hL M W hxs hWlim w hw
  refine ⟨Ku,Kv,cFirst,cK,hKu,hKv,hFirst,hFirstLower,hcK,high,outer,Hvalues,Hcuts,?_⟩
  intro depth
  have hCm : 1≤Ku+1:=by linarith
  obtain ⟨Ci,hCi,HI⟩:=eventually_inherited_same_star_four_Ga_current_initial_along hdim
    depth (Ku+1) cK hCm hcK heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hTemp hCf hCcal M W hcanonical hWlim hcompare hsource saving hsaving w Hmixed
  obtain ⟨Cc,hCc,HC⟩:=eventually_inherited_same_star_four_Ga_current_projected_constant_along hdim
    depth (Ku+1) cK hCm hcK heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hTemp hCf hCcal M W hcanonical hWlim hcompare hsource saving hsaving w Hmixed
  exact ⟨Ci,Cc,hCi,hCc,HI.on_sharp_source_cuts hxs le_rfl Hcuts,
    HC.on_sharp_source_cuts hxs le_rfl Hcuts⟩

end OAI.SKFluctuations.Cavity
