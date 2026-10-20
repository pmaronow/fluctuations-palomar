module

public import ComparisonSignedCavityInheritedCenteredTransientLowPart
public import ComparisonSignedCavityTransientLowMovingDensity
public import ComparisonSignedCavityActualHighTaylorParts
public import ComparisonSignedCavityInheritedErrorTransport

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 18000000

def nativeActualCenteredThirdLowPart (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (l t : ℝ) : ℝ :=
  let g:=fun j : Fin 4=>cutLowJet n q U b h K T
    (fun σ=>sitePair T a z (T.cavityAssignment σ).2) 0 j l 0
  let D:=fun J k=>nativeTransientLowErrorJet n q U b h K T J 0 k l t
  let J:=fun σ=>P (T.cavityAssignment σ).1*sitePair T a z (T.cavityAssignment σ).2
  let A:=fun σ=>P (T.cavityAssignment σ).1
  l*(D J 3-productJet3 g (fun j=>D A j) 3)+3*(D J 2-productJet3 g (fun j=>D A j) 2)

theorem native_actual_centered_third_LOW_part_eq_sum (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (i star U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as)
    (P : T.cavityLeft.Assignment→ℝ) (a z : T.Slot) (l t : ℝ) :
    nativeActualCenteredThirdLowPart n q U b h K T P a z l t=
      nativeTransientCenteredLowErrorPart n q i star U b h K T P (sitePair T a z) 0 .initial l t+
      nativeTransientCenteredLowErrorPart n q i star U b h K T P (sitePair T a z) 0 .star l t+
      nativeTransientCenteredLowErrorPart n q i star U b h K T P (sitePair T a z) 0 .moving l t := by
  simpa only [nativeActualCenteredThirdLowPart,map_zero] using
    native_transient_centered_low_error_parts n q i star U b h K T P (sitePair T a z) 0 l t

theorem eventually_actual_minimum_inherited_constant_centered_third_LOW_profile
    (rBound : ℕ) (Bclock Temp Cf Ccut : ℝ)
    (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCcut : 0≤Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠjGrid : ℕ in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (W l t : ℝ),U≤as.length →
          T.leaves≤rBound → M.xs≤W → W≤1 → partitionPoint 0 as U≤Ccut*W →
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → ∀a z : T.Slot,
          let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
          |nativeActualCenteredThirdLowPart n q U b h K T (fun _=>1) a z l t|≤
            C*W^2*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_canonical_centered_transient_LOW_part_budget
    (D:=D) 0 rBound Bclock Temp Cf 0 Ccut hTemp hCf (by norm_num) hCcut
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨3*C,by positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hsource hxs L us hus hret hmesh
  filter_upwards [hn M hsource hxs L us hus hret hmesh] with jGrid hj
  dsimp only at hj ⊢
  intro U T W l t hU hT hxW hW1 hcut hl ht a z
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
  let G : ActualNaturalBoundaryShape n 0 T:=
    ⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,(fun e=>Fin.elim0 e),(fun e=>Fin.elim0 e)⟩
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  have HP : (G.canonicalMinimumSource M forms).restProduct=(fun _=>1):=by
    funext σ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus jGrid
  have HE (part : NativeTransientLowErrorPart) :
      |nativeTransientCenteredLowErrorPart n q 0 0 U b h K T (fun _=>1) (sitePair T a z) 0 part l t|≤
        C*W^2*(T.forkCost R+edgeBudget 0 as R):=by
    have HH:=hj 0 0 U part T l t hU hl ht hT G forms ∅ W hxW hW1 hcut (fun e=>Fin.elim0 e) a z
    rw [HP] at HH
    simp only [sourceMonomialScale,Finset.card_empty,pow_zero,Nat.sub_zero,mul_one] at HH
    have HR j (_hj : j≤as.length):=native_transient_low_part_radius_le n U 0 0 b h K as
      (cutFullVariance n q U l t b h K) part j
    have HC:=add_le_add (native_forkCost_mono_on_clock T HR) (actual_low_edgeBudget_mono ho HR)
    exact HH.trans (mul_le_mul_of_nonneg_left HC (mul_nonneg hC.le (sq_nonneg W)))
  rw [native_actual_centered_third_LOW_part_eq_sum n q 0 0]
  have Habs:=((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (HE .initial) (HE .star))) (HE .moving)))
  convert Habs using 1; ring

end OAI.SKFluctuations.Cavity
