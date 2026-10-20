module

public import ComparisonSignedCavityActualConstantSourceChildrenTerminalAlong
public import ComparisonSignedCavityInheritedFourRetainedGammaAlong
public import ComparisonSignedCavityActualConstantSourceGaCurrentAlong

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization NativeOverlapMinimum
set_option maxHeartbeats 26000000
set_option backward.isDefEq.respectTransparency false

theorem nativeActualConstantSourceChildren_coefficient_variation_unconditional
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ} {as : List PositiveMass} {star U : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ho : MassOrdered 0 as) (hs : star<U) (hU : U≤as.length) :
    ((nativeActualConstantSourceChildren M as star U hs hU).map
      (fun Q=>|Q.term.coefficient|)).sum≤6 := by
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
  let base:=nativeActualConstantState (S:=Spin n×Bool) as 0 star
  have hK:=native_continuum_mixed_clock_nonneg n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have hKm:=native_continuum_mixed_clock_monotone n M.bf M.hf M.inherited_bf_monotone M.inherited_hf_monotone as ho
  have Hbounds:=native_full_gamma_row_uniform_bounds n (single (S:=Spin n×Bool) as) ho 0 ho U
    (by omega) hU K hKm hK (B:=K as.length) le_rfl (singleSlot as)
  rw [native_full_gamma_row_hessian n _ ho 0 ho U (by omega) K] at Hbounds
  have Hchi : 0 ≤ chi ∧ chi ≤ 1:=⟨(Real.exp_pos _).le.trans Hbounds.1,Hbounds.2⟩
  have Hrow:=nativeActualResourceStep_coefficient_variation_le ho (nativeOriginalHighRowGamma U K)
    (fun st p _=>nativeOriginalHighRowGamma_abs_le_one ho U K st p)
    hs (hs.le.trans hU) .highRow base
    (show base.tree.leaves≤1 by simp only [base,nativeActualConstantState,single_leaves_exact,le_refl])
  have Hcoef : base.term.coefficient=1:=rfl
  rw [Hcoef] at Hrow
  norm_num only [abs_one,NativeActualExpansionOp.coefficientCost,Nat.cast_one,mul_one,one_mul] at Hrow
  unfold nativeActualConstantSourceChildren
  simp only [List.map_cons,List.sum_cons,NativeActualResourceState.reweight,
    NativeResourceTerm.reweight,NativeActualResourceState.projection,NativeResourceTerm.projection,
    nativeActualConstantState,NativeResourceTerm.ofLive,mul_one]
  change |chi|+_≤6
  rw [abs_of_nonneg Hchi.1]
  have Hchi1 : chi≤1:=Hchi.2
  change chi+((nativeActualResourceStep (nativeOriginalHighRowGamma U K) hs (hs.le.trans hU)
    .highRow base).map (fun Q=>|Q.term.coefficient|)).sum≤6
  linarith

theorem actual_constant_source_children_forest_abs_sum_le_unconditional
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock B : ℝ}
    {as : List PositiveMass} {star U : ℕ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (ho : MassOrdered 0 as) (hs : star < U) (hU : U ≤ as.length)
    (W : ℝ) (depth : ℕ) (F : NativeActualResourceState (Spin n×Bool) as 0 star→ℝ) (hB : 0 ≤ B)
    (H : ∀Q∈nativeActualConstantSourceChildren M as star U hs hU,
      ((nativeActualMinimumFourCenteredForest M hs hU W depth [Q]).map (fun R=>|F R|)).sum ≤ |Q.term.coefficient| *B) :
    ((nativeActualMinimumFourCenteredForest M hs hU W depth
      (nativeActualConstantSourceChildren M as star U hs hU)).map (fun R=>|F R|)).sum ≤ 6*B := by
  unfold nativeActualMinimumFourCenteredForest at H ⊢
  rw [nativeActualFourCenteredForest_eq_flatMap_singletons,List.map_flatMap,native_sum_flatMap]
  apply (List.sum_le_sum H).trans
  rw [List.sum_map_mul_right]
  exact mul_le_mul_of_nonneg_right
    (nativeActualConstantSourceChildren_coefficient_variation_unconditional M ho hs hU) hB

def ActualConstantSourceRetainedGammaOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta Cmass cK C : ℝ) {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (w : ℕ→ActualSlowWindowChoice) : Prop :=
  ∀ᶠn in atTop,∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹ ≤ (M n).xs→(w n).star∈us→
  ∀ᶠj in atTop,
    let as:=finiteCutMasses us j
    let star:=retainedMassPrefixIndex (w n).star.val as
    ∀(U : ℕ) (hs : star < U) (hU : U ≤ as.length) (V : ℝ),
      partitionPoint 0 as star ≤ Cmass*W n→W n ≤ V→V ≤ 1→V ≤ (M n).R (partitionPoint 0 as U)→
      (M n).R (partitionPoint 0 as star) ≤ V/2→(M n).z ≤ V/2→
      cK*W n ≤ nativeContinuumMixedClock (dim n) (M n).bf (M n).hf as star→
    ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
      (nativeActualConstantSourceChildren (M n) as star U hs hU)).map
      (fun Q=>|nativeActualOriginalFourRetainedGammaError (M n) U (W n) Q|)).sum ≤ C*(dim n:ℝ)^(-eta)*(M n).xs^2

theorem ActualFourRetainedGammaForestOnEveryFinalNetAlong.constant_source_children
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C : ℝ} {depth : ℕ} {dim : ℕ→ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualFourRetainedGammaForestOnEveryFinalNetAlong 0 1 3 depth eta Cmass cK C M W w)
    (hC : 0 ≤ C) (hCm : 0 ≤ Cmass) (hxs : ∀n,(M n).xs ≤ W n)
    :
    ActualConstantSourceRetainedGammaOnEveryFinalNetAlong depth eta Cmass cK (6*C) M W w := by
  filter_upwards [H] with n hn
  intro L us hus hret hmesh hstar
  filter_upwards [hn L us hus hret hmesh hstar] with j hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us j
  let star:=retainedMassPrefixIndex (w n).star.val as
  let mid:=retainedMassBefore (w n).star.val as
  let tail:=retainedMassAfter (w n).star.val as
  have Hcut : mid++tail=as:=retainedMass_append (w n).star.val as
  have Hmid : 0 < mid.length:=by
    have HP:=nativeRetainedCut_partitionPoint as (finiteCutMasses_ordered us hus j)
      (w n).star (finiteCutMasses_nodes us j hstar)
    by_contra Hm
    have Hz : star=0:=by change mid.length=0;omega
    change partitionPoint 0 as star=(w n).star.val at HP
    rw [Hz] at HP
    simp only [partitionPoint,partitionValues_zero,id_eq] at HP
    linarith [(w n).star.property]
  intro U hs hU V hmass hWV hV1 hVU hlow hz hstarK
  let B:=C*(dim n:ℝ)^(-eta)*(M n).xs^2
  have hB : 0 ≤ B:=by dsimp only [B];positivity
  let P : ℕ→List PositiveMass→Prop:=fun ss bs=>
    ∀(hs' : ss < U) (hU' : U ≤ bs.length) (st : NativeActualResourceState (Spin (dim n)×Bool) bs 0 ss),
      NativeActualResourceGenerated 0 ss U [] st.generation st.tree st.term→
      st.generation=1→st.tree.leaves ≤ 3→
      ((nativeActualMinimumFourCenteredForest (M n) hs' hU' (W n) depth [st]).map
        (fun Q=>|nativeActualOriginalFourRetainedGammaError (M n) U (W n) Q|)).sum ≤ |st.term.coefficient| *B
  have HP : P (0+mid.length) (mid++tail):=by
    intro hs' hU' st hgen hdepth hleaf
    have Hj:=hj [] mid tail
    simp only [List.nil_append,List.length_nil,Nat.zero_add] at Hj
    have Hmi : partitionPoint 0 as 0 ≤ Cmass*(M n).xs:=by
      simpa only [partitionPoint,partitionValues_zero,id_eq] using mul_nonneg hCm (M n).hxs.le
    have HH:=Hj Hcut rfl hmass U [] st (by simp) hdepth hleaf hgen Hmid (by simpa only [Nat.zero_add] using hs') hU'
      (M n).xs V le_rfl (hxs n) Hmi hWV hV1 hVU hlow hz hstarK
    simpa only [nativeResourceScale,List.map_nil,List.prod_nil,mul_one,B,mul_assoc] using HH
  have HP0 : P mid.length (mid++tail):=(Nat.zero_add mid.length) ▸ HP
  have HP' : P star as:=Hcut ▸ HP0
  have HB:=actual_constant_source_children_forest_abs_sum_le_unconditional (M n)
    (finiteCutMasses_ordered us hus j) hs hU (W n) depth
    (nativeActualOriginalFourRetainedGammaError (M n) U (W n)) hB (by
      intro Q hQ
      exact HP' hs hU Q (nativeActualConstantSourceChildren_valid (M n) hs hU Q hQ)
        (nativeActualConstantSourceChildren_generation (M n) hs hU Q hQ)
        (nativeActualConstantSourceChildren_leaves (M n) hs hU Q hQ))
  exact HB.trans_eq (by dsimp only [B];ring)

theorem eventually_inherited_same_star_constant_source_retained_Gamma_along
    {dim : ℕ→ℕ} (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (depth : ℕ) (Cmass cK : ℝ) (hCm : 1 ≤ Cmass) (hcK : 0 < cK) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
    ∃C : ℝ,0 < C ∧ ActualConstantSourceRetainedGammaOnEveryFinalNetAlong depth eta Cmass cK C M W w := by
  obtain ⟨C,hC,H⟩:=eventually_inherited_same_star_four_retained_Gamma_forest_along hdim
    0 1 3 depth Cmass cK hCm hcK heta hm hdelta hroom hgap hcl hcu hAz hC0 hCt
    hTemp hCf hCcal M W hcanonical hWlim hcompare hsource saving hsaving w Hmixed
  exact ⟨6*C,by positivity,H.constant_source_children hC.le (zero_le_one.trans hCm)
    (fun n=>(M n).canonical_direct_test_band_ge_scale.trans_eq (hcanonical n).symm)⟩

def ActualFourRetainedGammaInitialOnEveryFinalNetAlong
    {m delta cl cu Az C0 Ct D Bclock : ℝ} (depth : ℕ) (eta Cmass cK C : ℝ) {dim : ℕ→ℕ}
    (M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
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
      ((nativeActualMinimumFourCenteredForest (M n) hs hU (W n) depth
        [nativeActualInitialState (pre++(mid++tail)) pre.length (pre.length+mid.length) a (by omega)]).map
        (fun Q=>|nativeActualOriginalFourRetainedGammaError (M n) U (W n) Q|)).sum ≤
        C*((dim n):ℝ)^(-eta)*(M n).xs^2*x

theorem ActualFourRetainedGammaForestOnEveryFinalNetAlong.initial
    {m delta cl cu Az C0 Ct D Bclock eta Cmass cK C : ℝ} {depth : ℕ} {dim : ℕ→ℕ}
    {M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock}
    {W : ℕ→ℝ} {w : ℕ→ActualSlowWindowChoice}
    (H : ActualFourRetainedGammaForestOnEveryFinalNetAlong 1 0 2 depth eta Cmass cK C M W w) :
    ActualFourRetainedGammaInitialOnEveryFinalNetAlong depth eta Cmass cK C M W w := by
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

theorem eventually_inherited_same_star_four_retained_Gamma_initial_along {dim : ℕ→ℕ} (hdim : Tendsto dim atTop atTop)
    {m delta eta cl cu Az C0 Ct D Bclock Temp Cf Ccal : ℝ}
    (depth : ℕ) (Cmass cK : ℝ) (hCm : 1 ≤ Cmass) (hcK : 0<cK) (heta : 0 < eta)
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m) (hgap : 2*eta < 6*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCcal : 1 ≤ Ccal)
    (M : (n:ℕ)→NativeOverlapMinimum ((dim n)+1) m delta cl cu Az C0 Ct D Bclock)
    (W : ℕ→ℝ) (hcanonical : ∀n,W n=(M n).canonicalDirectTestBandScale)
    (hWlim : Tendsto W atTop (𝓝 0))
    (hcompare : ∀ᶠn in atTop,(M n).xs^2 ≤ Ccal^2*
      laplaceComparisonStrength (M n).context.d (M n).lam (M n).xs)
    (hsource : ∀ᶠn : ℕ in atTop,NativeActualSmallSourceClocks (M n) Temp Cf)
    (saving : ℝ) (hsaving : 0 ≤ saving) (w : ℕ→ActualSlowWindowChoice)
    (Hmixed : ∀j k : ℕ,ActualMixedStarProjectionPowersOnEveryFinalNetAlong j k saving M W w) :
    ∃C : ℝ,0<C ∧ ActualFourRetainedGammaInitialOnEveryFinalNetAlong depth eta Cmass cK C M W w := by
  obtain ⟨C,hC,HC⟩:=eventually_inherited_same_star_four_retained_Gamma_forest_along hdim
    1 0 2 depth Cmass cK hCm hcK heta hm hdelta hroom hgap
    hcl hcu hAz hC0 hCt hTemp hCf hCcal M W hcanonical hWlim hcompare hsource saving hsaving w Hmixed
  exact ⟨C,hC,HC.initial⟩

end OAI.SKFluctuations.Cavity
