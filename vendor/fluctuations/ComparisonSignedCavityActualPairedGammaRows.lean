module

public import ComparisonSignedCavityActualPairedHighResampling
public import ComparisonSignedCavityActualPairedNearHigh
public import ComparisonSignedCavityActualContinuumGammaUpper

@[expose] public section

noncomputable section
set_option maxHeartbeats 18000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization

theorem eventually_actual_minimum_canonical_paired_far_gamma_row
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cmass Ccal Rmacro F : ℝ)
    (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct)
    (hCcal : 1 ≤ Ccal) (hmacro : 0 < Rmacro) (hRhalf : Rmacro ≤ 1/2)
    (hFmass : 1+2*cu ≤ F) (hFradius : 1+1/Rmacro ≤ F) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp)  →  (∀u,M.h u=0)  →  M.xs ≤ 1  →
        M.xs^2 ≤ Ccal^2*laplaceComparisonStrength M.context.d M.lam M.xs  →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1)  →  (∀u∈uniformMasses L,u∈us)  →  ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs  →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
        let bclock:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let hclock:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>hclock j+bclock j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        ∀(U rBound : ℕ),0 < U →
        let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
          (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (v : ℝ),
          T.leaves ≤ rBound → M.xs ≤ v → W ≤ Rmacro/2 →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e)  →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e))  →
          (∀e,G.j e≠j' e  →
            let rh:=M.R (partitionPoint 0 as (T.splitIndex (G.j e) (j' e)))
            4*W ≤ rh ∧ M.z ≤ min (rh/8) (Rmacro/4) ∧
            M.R (G.sourceLowMass e) ≤ min (rh/8) (Rmacro/4) ∧
            v ≤ partitionPoint 0 as (T.splitIndex (G.j e) (j' e)))  →
        ∀(b s e : T.Slot),s≠e  →
          T.splitIndex b s=T.splitIndex b e  →  T.splitIndex b s < T.splitIndex s e  →
          (let rh:=M.R (partitionPoint 0 as (T.splitIndex s e));
            4*W ≤ rh ∧ M.z ≤ min (rh/8) (Rmacro/4) ∧
            M.R (partitionPoint 0 as (T.splitIndex b s)) ≤ min (rh/8) (Rmacro/4) ∧
            v ≤ partitionPoint 0 as (T.splitIndex s e))  →
        partitionPoint 0 as (T.splitIndex s e) ≤ v →
        |fullScalarCutGamma T U K s e*
          retainedSignedJets n q U bclock hclock K [restHighKernel n U bclock hclock K] T
            (fun σ=>nativeRestEndpointDifference n T b s e σ*
              ((G.canonicalMinimumSource M f).restProduct σ-
                ((G.retarget j' hne).canonicalMinimumSource M f).restProduct σ)) []| ≤
          C*sourceMonomialScale M.xs W initial*W^2*pairForkVariation rBound*
            (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_minimum_canonical_paired_first_high_resampling
    (D:=D) (eta:=0) a ha Bclock Temp Cmass Ccal Rmacro F hTemp hCm hm hdelta hroom
    (by linarith) hcl hcu hAz hC0 hCt hCcal hmacro hRhalf hFmass hFradius
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_bare_continuum_scalar_gamma_mass_bound
    (D:=D) Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=8*Cg*(a:ℝ)*(1+Temp)*(2*C0)^6*Cp^a
  have hC : 0 < C:=by
    have ha' : (0:ℝ) < a:=by exact_mod_cast ha
    have hCp' : 0 < Cp:=zero_lt_one.trans_le hCp
    dsimp only [C]
    positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HP,HG] with n hnP hnG
  intro M hb hh hxs hcompare L us hus hret hmesh
  filter_upwards [hnP M hb hh hxs hcompare L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U rBound hU T G f initial v hT hxv hWmacro hmass j' hne hlow hgeometry b s e hse hblow hbgap hgeom huv
  let as:=finiteCutMasses us k
  let W:=max M.xs (Real.sqrt (laplaceComparisonStrength M.context.d M.lam M.xs))
  let r:=2*savedExteriorScale ((2*C0)*M.xs) W v
  let scale:=sourceMonomialScale M.xs W initial
  let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
    (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp
  let K:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)+
    (M.bf (partitionPoint 0 as j):ℝ)*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hx:=M.hxs
  have hxW : M.xs ≤ W:=le_max_left _ _
  have hW : 0 < W:=hx.trans_le hxW
  have hv : 0 < v:=hx.trans_le hxv
  have hscale : 0 ≤ scale:=by dsimp only [scale,sourceMonomialScale];positivity
  have hr : 0 ≤ r:=by dsimp only [r,savedExteriorScale];positivity
  have hR j : 0 ≤ R j:=by
    dsimp only [R,nativeOriginalHighErrorEnvelope]
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (actualLowErrorComparisonConstant_nonneg _ hTemp)
        (add_nonneg (Real.sqrt_nonneg _) (by positivity))
  have hcost : 0 ≤ T.forkCost R+edgeBudget 0 as R:=
    add_nonneg (T.forkCost_nonneg hR) (edgeBudget_nonneg ho hR)
  have HG:=hnG M hb hh as ho T U hU s e hse
  have HG' : |fullScalarCutGamma T U K s e| ≤ 2*Cg*v := by
    apply HG.trans
    nlinarith only [hxv,huv,hCg]
  have HB:=hk U rBound T G f initial v hT hv hWmacro hmass j' hne hlow hgeometry
    b s e hse hblow hbgap hgeom
  simp only [neg_zero,Real.rpow_zero,mul_one] at HB
  have Hnorm : v*r^2/M.xs ≤ 4*(2*C0)^6*W^2 := by
    simpa only [r,show (2:ℝ)^2=4 by norm_num] using
      paired_raw_resampling_gamma_norm_scale (B:=2*C0) (rho:=2) hx hxW hv
  have Hmult:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left Hnorm
      (show 0 ≤ 2*Cg*(a:ℝ)*(1+Temp)*(Cp^a*scale) by positivity))
    (mul_nonneg (pairForkVariation_nonneg rBound) hcost)
  rw [abs_mul]
  apply (mul_le_mul HG' HB (abs_nonneg _) (by positivity : 0 ≤ 2*Cg*v)).trans
  dsimp only [C,r,scale,R,as] at Hmult ⊢
  convert Hmult using 1 <;> ring

theorem eventually_actual_minimum_canonical_paired_near_gamma_row
    (a : ℕ) (ha : 0 < a) (Bclock Temp Cmass Cnear : ℝ)
    (hTemp : 0 ≤ Temp) (hCm : 0 ≤ Cmass) (hCnear : 0 ≤ Cnear)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp) → (∀u,M.h u=0) → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a → NativeSourceFactorForm) (initial : Finset (Fin a)) (W : ℝ),
          M.xs ≤ W → (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale M.xs W initial e) →
        ∀(j' : Fin a → T.Slot) (hne : ∀e,G.i e≠j' e),
          (∀e,T.splitIndex (G.i e) (G.j e)=T.splitIndex (G.i e) (j' e)) →
        ∀(G₀ : ActualNaturalBoundaryShape n 1 T) (j₀' : Fin 1 → T.Slot)
          (hne₀ : ∀e,G₀.i e≠j₀' e),
          (∀e,T.splitIndex (G₀.i e) (G₀.j e)=T.splitIndex (G₀.i e) (j₀' e)) →
          G₀.sourceLowMass 0 ≤ Cmass*W →
        let H:=G₀.canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)
        let H':=(G₀.retarget j₀' hne₀).canonicalMinimumSource M (fun _=>NativeSourceFactorForm.centered)
        let P:=G.canonicalMinimumSource M f
        let P':=(G.retarget j' hne).canonicalMinimumSource M f
        let paired:=fun σ=>(H.restProduct σ-H'.restProduct σ)*(P.restProduct σ-P'.restProduct σ)
        ∀(U rBound : ℕ),0 < U → T.leaves ≤ rBound →
        ∀(s e : T.Slot),s≠e → partitionPoint 0 as (T.splitIndex s e) ≤ Cnear*W →
          let R:=nativeOriginalHighErrorEnvelope n U M.bf M.hf as
            (4*NativeOverlapMinimum.bareSourceClockConstant cl Az D+2*Temp) Temp
          |fullScalarCutGamma T U K s e*
            retainedSignedJets n q U b h K [restHighKernel n U b h K] T paired []| ≤
            C*sourceMonomialScale M.xs W initial*W^2*pairForkVariation rBound*
              (T.forkCost R+edgeBudget 0 as R) := by
  obtain ⟨Cs,Cp,hCs,hCp,HP⟩:=eventually_actual_minimum_canonical_paired_near_high
    (D:=D) a ha Bclock Temp Cmass hTemp hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cg,hCg,HG⟩:=eventually_actual_minimum_bare_continuum_scalar_gamma_mass_bound
    (D:=D) Bclock Temp hTemp hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=Cg*(1+Cnear)*4*Cs*Cp^a
  have hC : 0 < C:=by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [HP,HG] with n hnP hnG
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hnP M hb hh hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T G f initial W hxW hmass j' hne hlow G₀ j₀' hne₀ hlow₀ hmass₀ U rBound hU hT s e hse hnear
  have hW : 0 < W:=M.hxs.trans_le hxW
  let K:=fun j=>(M.hf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)+
    (M.bf (partitionPoint 0 (finiteCutMasses us k) j):ℝ)*
      orderedPathS (n+1) M.bf M.hf (partitionPoint 0 (finiteCutMasses us k) j)
  have HG:=hnG M hb hh (finiteCutMasses us k) (finiteCutMasses_ordered us hus k) T U hU s e hse
  have HG' : |fullScalarCutGamma T U K s e| ≤ Cg*(1+Cnear)*W := by
    apply HG.trans
    nlinarith only [hxW,hnear,hCg]
  have HB:=(hk T G f initial W hxW hmass j' hne hlow G₀ j₀' hne₀ hlow₀ hmass₀).2 U rBound hT
  rw [abs_mul]
  apply (mul_le_mul HG' HB (abs_nonneg _) (by positivity : 0 ≤ Cg*(1+Cnear)*W)).trans_eq
  dsimp only [C]
  ring

end OAI.SKFluctuations.Cavity
