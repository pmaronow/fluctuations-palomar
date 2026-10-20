module

public import ComparisonSignedCavityInheritedFourFirstHighForest

@[expose] public section

noncomputable section
set_option maxHeartbeats 26000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_shell_history_four_first_high_initial_rate
    (depth : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F cK : ℝ)
    (hTemp : 0  ≤  Temp) (hCf : 0  ≤  Cf) (hCm : 0  ≤  Cmass) (hcK : 0<cK)
    {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hCcal : 1  ≤  Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro  ≤  1/2)
    (hFmass : 1+2*cu  ≤  F) (hFradius : 1+1/Rmacro  ≤  F)
    (hc : 0<c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        NativeActualSmallSourceClocks M Temp Cf →
        M.xs^2  ≤  Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale  ≤  Rmacro/2 →
        (Az+1/cl)*(1+Cmass)*M.canonicalDirectTestBandScale  ≤  Rmacro/4 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val  ≤  1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹  ≤  M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length) (a : ℝ),
          2*c*W ≤ partitionPoint 0 as U →
          partitionPoint 0 as i ≤ Cmass*M.xs → partitionPoint 0 as star ≤ Cmass*W →
          cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        ((nativeActualMinimumFourCenteredForest M hs hU W depth
          [nativeActualInitialState as i star a (by omega)]).map
          (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^3 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_four_first_high_forest_rate
    (D:=D) depth 0 1 2 Bclock Temp Cf Cmass Ccal Rmacro F cK hTemp hCf hCm hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M Tbase epsilon shell ts hb hh hsource hcompare hmacroW hsmall L us hus hret hmesh
  filter_upwards [hn M Tbase epsilon shell ts hb hh hsource hcompare hmacroW hsmall L us hus hret hmesh]
    with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  intro i star U hi hs hU a hcutlo hmi hms hstarK
  change U ≤ as.length at hU
  let st:=nativeActualInitialState (S:=Spin n×Bool) as i star a (by omega)
  have Hleaf:=nativeActualInitialState_leaves_le (S:=Spin n×Bool) as i star a (by omega)
  have Hvalid : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU a .initial (Or.inl rfl) (by change i ≤ as.length;omega))
  have Hfork f hf:=nativeActualInitialState_high_forkCost_zero (S:=Spin n×Bool)
    as i star U hi hs (by omega) a f hf
  have HH:=hj i star U hi hs hU [.initial] st (by simp) rfl Hleaf Hvalid Hfork hcutlo hmi hms hstarK
  simpa only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one,mul_assoc,←pow_succ',Nat.reduceAdd] using HH

theorem eventually_actual_shell_history_four_first_high_projected_constant_rate
    (depth : ℕ) (Bclock Temp Cf Cmass Ccal Rmacro F cK : ℝ)
    (hTemp : 0  ≤  Temp) (hCf : 0  ≤  Cf) (hCm : 0  ≤  Cmass) (hcK : 0<cK)
    {m delta cl cu Az C0 Ct D c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0  ≤  Az) (hC0 : 0 < C0) (hCt : 0  ≤  Ct)
    (hCcal : 1  ≤  Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro  ≤  1/2)
    (hFmass : 1+2*cu  ≤  F) (hFradius : 1+1/Rmacro  ≤  F)
    (hc : 0<c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        NativeActualSmallSourceClocks M Temp Cf →
        M.xs^2  ≤  Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale  ≤  Rmacro/2 →
        (Az+1/cl)*(1+Cmass)*M.canonicalDirectTestBandScale  ≤  Rmacro/4 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val  ≤  1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹  ≤  M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(star U : ℕ) (hs : star<U) (hU : U ≤ as.length),
          2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as star ≤ Cmass*W →
          cK*W ≤ nativeContinuumMixedClock n M.bf M.hf as star →
        ((nativeActualMinimumFourCenteredForest M hs hU W depth
          [(nativeActualConstantState as 0 star).projection (hs.le.trans hU)]).map
          (fun Q=>|nativeActualOriginalFourFirstHighError M U W Q|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_four_first_high_forest_rate
    (D:=D) depth 1 0 2 Bclock Temp Cf Cmass Ccal Rmacro F cK hTemp hCf hCm hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M Tbase epsilon shell ts hb hh hsource hcompare hmacroW hsmall L us hus hret hmesh
  filter_upwards [hn M Tbase epsilon shell ts hb hh hsource hcompare hmacroW hsmall L us hus hret hmesh]
    with jGrid hj
  dsimp only at hj ⊢
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  intro star U hs hU hcutlo hms hstarK
  let st:=(nativeActualConstantState (S:=Spin n×Bool) as 0 star).projection (hs.le.trans hU)
  have Hleaf : st.tree.leaves ≤ 2:=by
    have H:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0
      (nativeFreshAtSlot (single as) 0 (singleSlot as) star)
      (nativeFreshAtSlot_mem (single as) 0 (singleSlot as) star)
    simpa only [st,NativeActualResourceState.projection,nativeActualConstantState,
      NativeResourceTerm.ofLive,nativeResourceConstant,single_leaves_exact] using H
  have Hvalid : NativeActualResourceGenerated 0 star U [] st.generation st.tree st.term:=
    (show NativeActualResourceGenerated 0 star U []
      (nativeActualConstantState (S:=Spin n×Bool) as 0 star).generation
      (nativeActualConstantState (S:=Spin n×Bool) as 0 star).tree
      (nativeActualConstantState (S:=Spin n×Bool) as 0 star).term from
        .physical (.constant as hU)).projection (hs.le.trans hU)
  have Hfork (f : ℕ→ℝ) (hf : ∀j,j<U→f j=0) : st.tree.forkCost f=0:=by
    change (nativeFreshAtSlot (single as) 0 (singleSlot as) star).tree.forkCost f=0
    rw [nativeFreshAtSlot_high_forkCost _ _ _ hs f hf,single_forkCost]
  have Hmi : partitionPoint 0 as 0 ≤ Cmass*M.xs:=by
    simpa [partitionPoint,partitionValues] using mul_nonneg hCm M.hxs.le
  have HH:=hj 0 star U (Nat.zero_le _) hs hU [] st (by simp) rfl Hleaf Hvalid Hfork hcutlo Hmi hms hstarK
  simpa only [st,NativeActualResourceState.projection,nativeActualConstantState,
    NativeResourceTerm.projection,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_nil,List.prod_nil,mul_one] using HH

end OAI.SKFluctuations.Cavity
