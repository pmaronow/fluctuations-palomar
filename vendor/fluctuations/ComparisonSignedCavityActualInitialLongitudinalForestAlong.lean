module

public import ComparisonSignedCavityActualFourLongitudinalRestorationSeedAtoms
public import ComparisonSignedCavityActualConstantSourceCategoryReduction
public import ComparisonSignedCavityActualLongitudinalCategorySum
public import ComparisonSignedCavityActualFourRestorationSeedGeometry

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open NativeOverlapMinimum
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_shell_history_initial_longitudinal_forest_rate_along
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star →
        ∀x : ℝ,M.xs ≤ x → x ≤ W → partitionPoint 0 as i ≤ Cmass*x → ∀right : Bool,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
        ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
          (fun Q=>|nativeActualOriginalFourLongitudinalError M U W Q right|)).sum ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2*x := by
  obtain ⟨p,hp,_,_,_,C,hC,H⟩:=eventually_actual_shell_history_resource_longitudinal_restoration_forest_with_seed_atoms
    1 0 2 depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [hdim.eventually H] with n hn
  intro M Tbase epsilon shell ts hsource hb hh hsmall hW1 L us hus hret hmesh
  filter_upwards [hn M Tbase epsilon shell ts hsource hb hh hsmall hW1 L us hus hret hmesh]
    with jGrid hj
  dsimp only at hj ⊢
  intro i star U hi hs hU hlo hup hstarKmass hstarK x hx hxW hmi right
  let as:=finiteCutMasses us jGrid
  let W:=M.canonicalDirectTestBandScale
  let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
  have hP : NativeActualResourceGenerated i star U [.initial] st.generation st.tree st.term:=
    .physical (.seed as hU 0 .initial (Or.inl rfl) (hi.trans (hs.le.trans hU)))
  have HR:=hj i star U [.initial] st (by simp) rfl
    (nativeActualInitialState_leaves_le as i star 0 (hi.trans (hs.le.trans hU)))
    hP hi hs hU hlo hup hstarKmass hstarK x hx hxW hmi right
  let R:=nativeOriginalHighErrorEnvelope (dim n) U M.bf M.hf as (4*Cf+2*Temp) Temp
  have hRlo j (hj : j<U) : R j=0:=by simp only [R,nativeOriginalHighErrorEnvelope,hj,ite_true]
  have hflo j (hj : j<U) : ((R j)^(2/p))^2=0:=by
    rw [hRlo j hj,Real.zero_rpow (by positivity : 2/p ≠ 0)]
    ring
  have HF:=actual_initial_four_seed_high_fork_free (S:=Spin (dim n)×Bool) i star U hi hs hU 0
    (fun j=>((R j)^(2/p))^2) hflo
  have HR0:=actual_initial_four_seed_high_fork_free (S:=Spin (dim n)×Bool) i star U hi hs hU 0 R hRlo
  change ((nativeActualMinimumFourCenteredForest M hs hU W depth [st]).map
      (fun Q=>|nativeActualOriginalFourLongitudinalError M U W Q right|)).sum ≤
      |st.term.coefficient| *C*nativeResourceScale x W 1 [.initial]*
        (st.tree.forkCost (fun j=>((R j)^(2/p))^2)+W*st.tree.forkCost R+
          M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2) at HR
  rw [HF,HR0] at HR
  simpa only [st,nativeActualInitialState,NativeResourceTerm.ofLive,abs_one,one_mul,
    nativeResourceScale,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
    NativeResourceMark.savedScale,mul_one,mul_zero,zero_mul,zero_add,mul_assoc,mul_left_comm,mul_comm] using HR

theorem eventually_actual_shell_history_initial_longitudinal_category_rate_along
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (depth : ℕ) (Bclock Temp Cf Cmass Ccut cK : ℝ)
    (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut) (hcK : 0 < cK)
    {m delta cl cu Az C0 Ct D Cs c : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCs : 0 ≤ Cs) (hc : 0 < c) (hcouter : 2*cu*(Az+1) ≤ c) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀(M : NativeOverlapMinimum (dim n+1) m delta cl cu Az C0 Ct D Bclock)
        (Tbase epsilon shell : ℝ) (ts : List ComparisonHistoryTerm),
        NativeActualSmallSourceClocks M Temp Cf →
        (∀u,M.b u=historyMatrixClock Tbase epsilon shell ts u) →
        (∀u,M.h u=historyFieldClock ts u) →
        M.xs^2 ≤ Cs*laplaceComparisonStrength M.context.d M.lam M.xs →
        M.canonicalDirectTestBandScale ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let W:=M.canonicalDirectTestBandScale
        ∀(i star U : ℕ) (hi : i ≤ star) (hs : star<U) (hU : U ≤ as.length),
        2*c*W ≤ partitionPoint 0 as U → partitionPoint 0 as U ≤ Ccut*W →
        partitionPoint 0 as star ≤ Cmass*W →
        cK*W ≤ nativeContinuumMixedClock (dim n) M.bf M.hf as star →
        ∀x : ℝ,M.xs ≤ x → x ≤ W → partitionPoint 0 as i ≤ Cmass*x → ∀right : Bool,
        let st:=nativeActualInitialState (S:=Spin (dim n)×Bool) as i star 0 (hi.trans (hs.le.trans hU))
        let K:=nativeContinuumMixedClock (dim n) M.bf M.hf as
        let chi:=(scalarTerminal.schedule (scalarBoundaryClocks as (relocatedClock U 0 K))).H 0 0
        |nativeActualFourOtherCategorySum M U W
          (nativeActualMinimumFourCenteredForest M hs hU W depth [st])
          (nativeActualLongitudinalCategory right)|/(chi*K star) ≤
          C*M.context.N^(-(actualMassSavingExponent m delta/256))*M.xs^2*x := by
  obtain ⟨C,hC,H⟩:=eventually_actual_shell_history_initial_longitudinal_forest_rate_along
    dim hdim depth Bclock Temp Cf Cmass Ccut cK hTemp hCf hCmass hCcut hcK
    hm hdelta hroom hcl hcu hAz hC0 hCt hCs hc hcouter
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M Tbase epsilon shell ts hsource hb hh hsmall hW1 L us hus hret hmesh
  filter_upwards [hn M Tbase epsilon shell ts hsource hb hh hsmall hW1 L us hus hret hmesh]
    with jGrid hj
  dsimp only at hj ⊢
  intro i star U hi hs hU hlo hup hmassstar hstarK x hx hxW hmi right
  have hW:=M.hxs.trans_le M.canonical_direct_test_band_ge_scale
  have HR:=actual_longitudinal_category_signed_sum_abs_le_error_sum M hCf hsource
    (M.canonical_direct_test_band_ge_scale.trans hW1) (finiteCutMasses_ordered us hus jGrid)
    hs hU hW hcK hstarK
    (nativeActualMinimumFourCenteredForest M hs hU M.canonicalDirectTestBandScale depth
      [nativeActualInitialState (S:=Spin (dim n)×Bool) (finiteCutMasses us jGrid) i star 0
        (hi.trans (hs.le.trans hU))]) right
  exact HR.trans (hj i star U hi hs hU hlo hup hmassstar hstarK x hx hxW hmi right)

end OAI.SKFluctuations.Cavity
