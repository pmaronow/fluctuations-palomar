module

public import ComparisonActualHighOnlyActualFourGaCurrent
public import ComparisonSignedCavityInheritedFourGaCurrentRootsAlong
public import ComparisonActualHighOnlyAnalyticBasics
public import ComparisonActualHighOnlyResourcePhysicalFactories
public import ComparisonActualHighOnlyPullbackFourInterfaces
public import ComparisonActualHighOnlySourceProjectionAlong
public import ComparisonActualHighOnlyGaCurrentPrerequisites
public import ComparisonActualHighOnlyInheritedFourGaCurrentForestAlong

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
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree Cavity LaplaceWindowFormalization NativeOverlapMinimum ActualHighOnlyOverlapMinimum
variable {dim : ℕ→ℕ}

def ActualFourGaCurrentInitialOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta Cmass cK C : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠj : ℕ in atTop,
    let as:=finiteCutMasses us j
    ∀(pre mid tail : List PositiveMass),pre++(mid++tail)=as →
      pre.length+mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as (pre.length+mid.length) ≤ Cmass*W n → 0 < mid.length →
    ∀(U : ℕ) (hs : pre.length+mid.length<U) (hU : U≤(pre++(mid++tail)).length) (a x V : ℝ),
      (M n).xs ≤ x → x ≤ W n → partitionPoint 0 as pre.length ≤ Cmass*x →
      W n ≤ V → V ≤ 1 → V≤(M n).R (partitionPoint 0 as U) →
      (M n).R (partitionPoint 0 as (pre.length+mid.length)) ≤ V/2 → (M n).z ≤ V/2 →
      cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as (pre.length+mid.length) →
      ((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
        [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) a (by omega)]).map
        (fun Q=>|nativeActualOriginalFourGaCurrentError_high_only (M n) U (W n) Q|)).sum ≤
        C*((dim n):ℝ)^(-eta)*(M n).xs^2*x

theorem ActualFourGaCurrentForestOnEveryFinalNetAlong_high_only.initial
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C : ℝ} {depth : ℕ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualFourGaCurrentForestOnEveryFinalNetAlong_high_only 1 0 2 depth eta Cmass cK C M W w) :
    ActualFourGaCurrentInitialOnEveryFinalNetAlong_high_only depth eta Cmass cK C M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  intro pre mid tail hcut hindex hmass hmid U hs hU a x V hx hxW hmi hWV hV1 hVU hlow hz hstarK
  let as:=pre++(mid++tail)
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as pre.length (pre.length+mid.length) a (by dsimp only [as];simp)
  have Hleaf:=nativeActualInitialState_leaves_le (S:=Spin (dim n)×Bool) as pre.length
    (pre.length+mid.length) a (by dsimp only [as];simp)
  have Hvalid : NativeActualResourceGenerated pre.length (pre.length+mid.length) U [.initial]
      st.generation st.tree st.term:=
    .physical (.seed as hU a .initial (Or.inl rfl) (by change pre.length ≤ as.length;dsimp only [as];simp))
  have HH:=hj pre mid tail hcut hindex hmass U [.initial] st (by simp) rfl Hleaf Hvalid hmid hs hU
    x V hx hxW hmi hWV hV1 hVU hlow hz hstarK
  simpa only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one] using HH

def ActualFourGaCurrentProjectedConstantOnEveryFinalNetAlong_high_only
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta Cmass cK C : ℝ)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn : ℕ in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs → (w n).star∈us →
  ∀ᶠj : ℕ in atTop,
    let as:=finiteCutMasses us j
    ∀(mid tail : List PositiveMass),mid++tail=as →
      mid.length=retainedMassPrefixIndex (w n).star.val as →
      partitionPoint 0 as mid.length ≤ Cmass*W n →
    ∀(U : ℕ) (hs : mid.length<U) (hU : U≤(mid++tail).length),
    ∀V : ℝ,W n ≤ V → V ≤ 1 → V≤(M n).R (partitionPoint 0 as U) →
      (M n).R (partitionPoint 0 as mid.length) ≤ V/2 → (M n).z ≤ V/2 →
      cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as mid.length →
      ((nativeActualMinimumFourCenteredForest_high_only (M n) hs hU (W n) depth
        [(nativeActualConstantState (mid++tail) 0 mid.length).projection (hs.le.trans hU)]).map
        (fun Q=>|nativeActualOriginalFourGaCurrentError_high_only (M n) U (W n) Q|)).sum ≤
        C*((dim n):ℝ)^(-eta)*(M n).xs^2

theorem ActualFourGaCurrentForestOnEveryFinalNetAlong_high_only.projected_constant
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C : ℝ} {depth : ℕ}
    {M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualFourGaCurrentForestOnEveryFinalNetAlong_high_only 0 1 2 depth eta Cmass cK C M W w)
    (hCm : 0≤Cmass) (hxsW : ∀n,(M n).xs ≤ W n) :
    ActualFourGaCurrentProjectedConstantOnEveryFinalNetAlong_high_only depth eta Cmass cK C M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  intro mid tail hcut hindex hmass U hs hU V hWV hV1 hVU hlow hz hstarK
  let as:=mid++tail
  have hsl : 0+mid.length ≤ as.length:=by dsimp only [as];simp
  let st:=(nativeActualConstantState (S:=Spin (dim n)×Bool) as 0 (0+mid.length)).projection hsl
  have hmid : 0 < mid.length:=by
    have HP:=nativeRetainedCut_partitionPoint (finiteCutMasses us j)
      (finiteCutMasses_ordered us hus j) (w n).star (finiteCutMasses_nodes us j hstar)
    rw [←hindex] at HP
    by_contra hh
    have hm0 : mid.length=0:=by omega
    rw [hm0] at HP
    have hpos:0<(w n).star.val:=(w n).star.property
    simp only [partitionPoint,partitionValues_zero,id_eq] at HP
    linarith
  have Hleaf : st.tree.leaves ≤ 2:=by
    have Hle:=(single (S:=Spin (dim n)×Bool) as).markedAttach_leaves 0
      (nativeFreshAtSlot (single as) 0 (singleSlot as) (0+mid.length))
      (nativeFreshAtSlot_mem (single as) 0 (singleSlot as) (0+mid.length))
    simpa only [st,NativeActualResourceState.projection,nativeActualConstantState,
      NativeResourceTerm.ofLive,nativeResourceConstant,single_leaves_exact] using Hle
  have Hvalid : NativeActualResourceGenerated 0 (0+mid.length) U [] st.generation st.tree st.term:=
    (show NativeActualResourceGenerated 0 (0+mid.length) U []
      (nativeActualConstantState (S:=Spin (dim n)×Bool) as 0 (0+mid.length)).generation
      (nativeActualConstantState (S:=Spin (dim n)×Bool) as 0 (0+mid.length)).tree
      (nativeActualConstantState (S:=Spin (dim n)×Bool) as 0 (0+mid.length)).term from
        .physical (.constant as hU)).projection hsl
  have Hmi : partitionPoint 0 (finiteCutMasses us j) 0 ≤ Cmass*(M n).xs:=by
    simpa only [partitionPoint,partitionValues_zero,id_eq] using mul_nonneg hCm (M n).hxs.le
  have Hj:=hj [] mid tail
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at Hj
  have HH:=Hj hcut hindex hmass U [] st (by simp) rfl Hleaf Hvalid hmid hs hU (M n).xs V le_rfl (hxsW n) Hmi
    hWV hV1 hVU hlow hz hstarK
  let Qstar : ℕ→Prop:=fun star=>∀(hs' : star<U) (hl' : star ≤ as.length),
    ((nativeActualMinimumFourCenteredForest_high_only (M n) hs' hU (W n) depth
      [(nativeActualConstantState (S:=Spin (dim n)×Bool) as 0 star).projection hl']).map
      (fun Q=>|nativeActualOriginalFourGaCurrentError_high_only (M n) U (W n) Q|)).sum ≤
      C*((dim n):ℝ)^(-eta)*(M n).xs^2
  have HQ : Qstar (0+mid.length):=by
    intro hs' hl'
    simpa only [st,NativeActualResourceState.projection,nativeActualConstantState,
      NativeResourceTerm.projection,NativeResourceTerm.ofLive,abs_one,one_mul,
      nativeResourceScale,List.map_nil,List.prod_nil,mul_one] using HH
  have HQ' : Qstar mid.length:=(Nat.zero_add mid.length) ▸ HQ
  exact HQ' hs (hs.le.trans hU)

theorem eventually_inherited_same_star_four_Ga_current_initial_along_high_only (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (depth : ℕ) (Cmass cK : ℝ) (hCm : 1 ≤ Cmass) (hcK : 0<cK) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→ActualHighOnlyOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀n,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,ActualHighOnlySmallSourceClocks (M n) Temp Cf)
    (hcutoff : ∀ᶠn : ℕ in atTop,(M n).data.s ≤ 1/4 ∧ (M n).data.s ≤ (M n).xs)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong_high_only j k saving M W w) :
    ∃C : ℝ,0<C ∧ ActualFourGaCurrentInitialOnEveryFinalNetAlong_high_only depth eta Cmass cK C M W w := by
  obtain ⟨C,hC,HC⟩:=eventually_inherited_same_star_four_Ga_current_forest_along_high_only hdim
    1 0 2 depth Cmass cK hCm hcK heta hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare hsource hcutoff saving hsaving w Hmixed
  exact ⟨C,hC,HC.initial⟩

end OAI.SKFluctuations.Cavity
