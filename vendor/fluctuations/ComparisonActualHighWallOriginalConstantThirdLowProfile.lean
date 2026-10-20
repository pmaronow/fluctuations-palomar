module

public import ComparisonActualHighWallCenteredTransientLowPart
public import ComparisonSignedCavityTransientLowMovingDensity
public import ComparisonSignedCavityActualConstantTransientLowProfile

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal BigOperators
set_option maxHeartbeats 24000000
set_option autoImplicit false
set_option linter.unusedVariables false

theorem eventually_actual_high_wall_original_constant_third_low_profile
    (rBound : ℕ) (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠj : ℕ in atTop,
        let as:=finiteCutMasses us j
        let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
        let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
        let K:=nativeContinuumMixedClock n M.bf M.hf as
        let q : ℕ→RestCoordinate n→ℝ:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length → T.leaves ≤ rBound →
        partitionPoint 0 as U ≤ Ccut*M.data.d →
        ∀(a z : T.Slot) (l t : ℝ),l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
          |nativeActualCenteredThirdLowPart n q U b h K T (fun _=>1) a z l t| ≤
            C*M.data.d^2*(T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_canonical_centered_transient_LOW_part_budget
    (D:=D) 0 rBound Bclock 0 Ccut (by norm_num) hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨3*Cp,by positivity,?_⟩
  filter_upwards [HP] with n hnP
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork M.data.hd1 L us hus hret hmesh] with j hjP
  dsimp only at hjP ⊢
  intro U T hU hT hcut a z l t hl ht
  let as:=finiteCutMasses us j
  let b:=fun k=>(M.bf (partitionPoint 0 as k):ℝ)
  let h:=fun k=>(M.hf (partitionPoint 0 as k):ℝ)
  let K:=nativeContinuumMixedClock n M.bf M.hf as
  let q : ℕ→RestCoordinate n→ℝ:=fun k=>Sum.elim (fun _=>b k) (fun _=>h k)
  let R:=nativeWholeLawErrorRadius n as (cutFullVariance n q U l t b h K) (cutLowError n U b h K)
  have ho:=finiteCutMasses_ordered us hus j
  let G : ActualNaturalBoundaryShape n 0 T:=
    ⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,(fun e=>Fin.elim0 e),(fun e=>Fin.elim0 e)⟩
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  have HE (part : NativeTransientLowErrorPart) :
      |nativeTransientCenteredLowErrorPart n q 0 0 U b h K T (fun _=>1)
        (sitePair T a z) 0 part l t| ≤ Cp*M.data.d^2*(T.forkCost R+edgeBudget 0 as R):=by
    have HB:=hjP 0 0 U part T l t hU hl ht hT G forms hcut (fun e=>Fin.elim0 e) a z
    have Hproduct : (G.canonicalHighWallSource M forms).restProduct=(fun _=>1):=by
      funext σ
      simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
    rw [Hproduct] at HB
    simp only [pow_zero,mul_one] at HB
    have HR k (_hk : k≤as.length):=native_transient_low_part_radius_le n U 0 0 b h K as
      (cutFullVariance n q U l t b h K) part k
    have HC:=add_le_add (native_forkCost_mono_on_clock T HR) (actual_low_edgeBudget_mono ho HR)
    exact HB.trans (mul_le_mul_of_nonneg_left HC (mul_nonneg hCp.le (sq_nonneg M.data.d)))
  rw [native_actual_centered_third_LOW_part_eq_sum n q 0 0]
  apply ((abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (HE .initial) (HE .star))) (HE .moving))).trans_eq
  ring

end OAI.SKFluctuations.Cavity
