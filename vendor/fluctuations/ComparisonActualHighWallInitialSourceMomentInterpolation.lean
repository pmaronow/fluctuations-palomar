module

public import ComparisonActualHighWallInitialPairMomentInterpolation
public import ComparisonActualHighWallDistinguishedInitialSourceFactor

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 18000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem eventually_actual_high_wall_distinguished_initial_source_moment_interpolate
    (a p rBound : ℕ) (hp : 0 < p) (Bclock Cmass : ℝ) (hCmass : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃Cp Cr : ℝ,0 < Cp ∧ 0 < Cr ∧ ∀ᶠn in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠjGrid in atTop,
        let as:=finiteCutMasses us jGrid
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let K:=fun j=>h j+b j*S j
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n (a+1) T) (forms : Fin (a+1)→NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) →
        ∀(e0 : Fin (a+1)) (i : ℕ),forms e0=.centered → T.splitIndex (G.i e0) (G.j e0)=i →
          let payload:=Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Cp^a*M.data.d^a
          let error:=originalHighWallInitialPairErrorScale M as i
          let eta:=originalInitialLowMomentModulus error (Cr*M.data.d) (4*p)
          T.disorderExpect (fullWeight n) (fullFeature n) 0 (cutFullVariance n q U l t b h K)
            (fun σ=>|(G.canonicalHighWallSource M forms).product σ|^(2*p)) 0 ≤
              (payload*(Cr*M.data.d)*eta)^(2*p) := by
  obtain ⟨Cp,hCp,HP⟩:=eventually_actual_high_wall_canonical_continuum_all_degree_even_moment
    (D:=D) a (2*p) rBound (by omega) Bclock Cmass hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cr,hCr,HI⟩:=eventually_actual_high_wall_initial_pair_moment_interpolate
    (D:=D) (2*p) (by omega) Bclock Cmass hCmass hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨Cp,Cr,hCp,hCr,?_⟩
  filter_upwards [HP,HI] with n hnP hnI
  intro M hwork L us hus hret hmesh
  filter_upwards [hnP M hwork L us hus hret hmesh,hnI M hwork L us hus hret hmesh] with jGrid hjP hjI
  dsimp only at hjP hjI ⊢
  intro U T l t hl ht hT G forms hmass e0 i hform hcut
  let as:=finiteCutMasses us jGrid
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun j=>orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let K:=fun j=>h j+b j*S j
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let law:=cutFullVariance n q U l t b h K
  let G0:=G.withoutDistinguishedInitialFactor e0
  let P:=fun σ : T.Assignment=>(G0.canonicalHighWallSource M (fun e=>forms (e0.succAbove e))).product σ
  let F:=fun σ : T.Assignment=>deletedOverlap n (joinSpin (T.atSlot σ (G.j e0)))
    (joinSpin (T.atSlot σ (G.i e0)))-S i
  let payload:=Real.exp (wholeLawRowComparisonConstant rBound*(2*max Bclock 0))*Cp^a*M.data.d^a
  let error:=originalHighWallInitialPairErrorScale M as i
  let eta:=originalInitialLowMomentModulus error (Cr*M.data.d) (4*p)
  have ho:=finiteCutMasses_ordered us hus jGrid
  have herror : 0 ≤ error:=original_high_wall_initial_pair_error_scale_nonneg M as i
  have hR : 0 < Cr*M.data.d:=mul_pos hCr M.data.hd
  have heta : 0 ≤ eta:=original_initial_low_moment_modulus_nonneg herror hR.le _
  have hpay : 0 ≤ payload:=by dsimp only [payload];positivity [M.data.hd]
  have hi : i ≤ as.length:=by rw [←hcut];exact G.lowInGrid e0
  have hmi : partitionPoint 0 as i ≤ Cmass*M.data.d:=by
    simpa only [ActualNaturalBoundaryShape.sourceLowMass,hcut] using hmass e0
  have hsplit : T.splitIndex (G.j e0) (G.i e0)=i:=by rw [T.splitIndex_symm,hcut]
  have hne : G.j e0 ≠ G.i e0:=Ne.symm (G.distinct e0)
  have Hinitial : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|F σ|^(4*p)) 0 ≤ (Cr*M.data.d*eta)^(4*p):=by
    dsimp only [F]
    rw [T.disorderExpect_pairAtSlot_actual (fullWeight_pos n) (fullFeature n) ho 0 law 0
      (G.j e0) (G.i e0) hne (fun σ τ=>|deletedOverlap n (joinSpin σ) (joinSpin τ)-S i|^(4*p))]
    rw [hsplit]
    simpa only [show 2*(2*p)=4*p by omega,eta,error,law,q,K,S,b,h,as] using
      hjI U l t hl ht i hi hmi
  have Hpayload : T.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (fun σ=>|P σ|^(4*p)) 0 ≤ payload^(4*p):=by
    have H:=hjP U T l t hl ht hT G0 (fun e=>forms (e0.succAbove e))
      (fun e=>by exact hmass (e0.succAbove e))
    simpa only [show 2*(2*p)=4*p by omega,P,payload,law,q,K,S,b,h,as] using H
  have he : (2:ℝ)*((2*p:ℕ):ℝ)=((4*p:ℕ):ℝ):=by push_cast;ring
  have Hjoint:=T.disorderExpect_product_wholeLaw_rpow_le (fullWeight_pos n) (fullFeature n)
    ho 0 law 0 F P (mul_nonneg hR.le heta) hpay (p:=((2*p:ℕ):ℝ))
    (by simpa only [he,Real.rpow_natCast] using Hinitial)
    (by simpa only [he,Real.rpow_natCast] using Hpayload)
  have HC:=native_ordered_source_center_eq_completed n M.bf M.hf
    (M.data.bf_monotone M.alpha) (M.data.hf_monotone M.alpha) (partitionPoint_mem as ho i)
  have Hproduct (σ : T.Assignment) : (G.canonicalHighWallSource M forms).product σ=F σ*P σ:=by
    rw [G.canonical_high_wall_product_distinguished_initial_factor M forms e0 hform i hcut σ]
    dsimp only [F,P,G0,S,nativePhysicalResourceCenter]
    rw [HC]
  simp_rw [Hproduct]
  simpa only [Real.rpow_natCast,eta,error,payload,mul_assoc,mul_left_comm,mul_comm] using Hjoint

end OAI.SKFluctuations.Cavity
