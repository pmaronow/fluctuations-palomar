module

public import ComparisonSignedCavityActualConstantTransientLowProfile
public import ComparisonSignedCavityTransientLowMovingDensity
public import ComparisonSignedCavityActualHighTaylorParts
public import ComparisonSignedCavityInheritedErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

theorem eventually_actual_minimum_inherited_canonical_third_LOW_profile
  (aDegree rBound : ℕ) (Bclock Temp Cf Cmass Ccut : ℝ)
  (hTemp : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCmass : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
  {m delta cl cu Az C0 Ct D : ℝ}
  (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
  (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
  ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
   ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
    NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
   ∀(L : ℕ) (us : List PositiveMass),
    (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
   ∀ᶠjGrid : ℕ in atTop,
    let as:=finiteCutMasses us jGrid
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    let K:=nativeContinuumMixedClock n M.bf M.hf as
    let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
    ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (W l t : ℝ),U ≤ as.length →
     T.leaves ≤ rBound → M.xs ≤ W → W ≤ 1 → partitionPoint 0 as U ≤ Ccut*W →
     l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀(G : ActualNaturalBoundaryShape n aDegree T) (forms : Fin aDegree→NativeSourceFactorForm)
      (initial : Finset (Fin aDegree)),
     (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) → ∀a z : T.Slot,
     let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
     |nativeActualCenteredThirdLowPart n q U b h K T (G.canonicalMinimumSource M forms).restProduct a z l t| ≤
      C*W^2*sourceMonomialScale M.xs W initial*(T.forkCost R+edgeBudget 0 as R) := by
 obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_centered_transient_LOW_part_budget
  (D:=D) aDegree rBound Bclock Temp Cf Cmass Ccut hTemp hCf hCmass hCcut
  hm hdelta hroom hcl hcu hAz hC0 hCt
 refine ⟨3*C,by positivity,?_⟩
 filter_upwards [H] with n hn
 intro M hsource hxs L us hus hret hmesh
 filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
 dsimp only at hj ⊢
 intro U T W l t hU hT hxW hW1 hcut hl ht G forms initial hmass a z
 let as:=finiteCutMasses us jGrid
 let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
 let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
 let K:=nativeContinuumMixedClock n M.bf M.hf as
 let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
 let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
 have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
 have HE (part : NativeTransientLowErrorPart) :
   |nativeTransientCenteredLowErrorPart n q 0 0 U b h K T (G.canonicalMinimumSource M forms).restProduct (sitePair T a z) 0 part l t| ≤
    C*W^2*sourceMonomialScale M.xs W initial*(T.forkCost R+edgeBudget 0 as R):=by
  have HH:=hj 0 0 U part T l t hU hl ht hT G forms initial W hxW hW1 hcut hmass a z
  have HR j (_hj : j ≤ as.length):=native_transient_low_part_radius_le n U 0 0 b h K as
   (cutFullVariance n q U l t b h K) part j
  have HC:=add_le_add (native_forkCost_mono_on_clock T HR) (actual_low_edgeBudget_mono ho HR)
  have hZ : 0 ≤ sourceMonomialScale M.xs W initial:=by
   rw [←source_factor_scale_product]
   exact Finset.prod_nonneg fun e _=>(source_factor_scale_pos M.hxs (M.hxs.trans_le hxW) initial e).le
  exact HH.trans (mul_le_mul_of_nonneg_left HC (by positivity))
 rw [native_actual_centered_third_LOW_part_eq_sum n q 0 0]
 have Habs:=((abs_add_le _ _).trans (add_le_add
  ((abs_add_le _ _).trans (add_le_add (HE .initial) (HE .star))) (HE .moving)))
 convert Habs using 1; ring

end OAI.SKFluctuations.Cavity
