module

public import ComparisonSignedCavityCanonicalSourceMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def NativeActualSmallSourceClocks {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock) (Temp Cf : ℝ) : Prop :=
  ∀u∈Icc (0:ℝ) 1,(M.bf u:ℝ) ≤ Temp ∧ (M.hf u:ℝ) ≤ Cf*(M.xs+u)

theorem native_small_source_clock_full_square_budget
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum n m delta cl cu Az C0 Ct D Bclock)
    (Temp Cf : ℝ) (hCf : 0 ≤ Cf) (hsource : NativeActualSmallSourceClocks M Temp Cf)
    (hxs : M.xs ≤ 1) (as : List PositiveMass) (ho : MassOrdered 0 as) :
    let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
    let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
    finitePhysicalMixedClock n as b h as.length+b as.length+h as.length ≤ 4*Cf+2*Temp := by
  dsimp only
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  have hu:=partitionPoint_mem as ho as.length
  have HC:=hsource _ hu
  have Hfield : h as.length ≤ 2*Cf:=by
    have H:=mul_le_mul_of_nonneg_left
      (show M.xs+partitionPoint 0 as as.length ≤ 2 by linarith [hu.2]) hCf
    exact HC.2.trans (by linarith only [H])
  have Hmean:=finitePhysicalMean_le_one n ho b h as.length
  have Hmul:=mul_le_mul_of_nonneg_left Hmean (NNReal.coe_nonneg (M.bf (partitionPoint 0 as as.length)))
  change h as.length+b as.length*finitePhysicalMean n as b h as.length+b as.length+h as.length ≤ _
  nlinarith [HC.1]

theorem eventually_actual_minimum_inherited_canonical_square_even_moment
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (Bclock Temp Cf Cmass : ℝ)
    (hT : 0 ≤ Temp) (hCf : 0 ≤ Cf) (hCm : 0 ≤ Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs ≤ 1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
        ∀(G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x W : ℝ),M.xs ≤ x → x ≤ W →
          (∀e,G.sourceLowMass e ≤ Cmass*sourceFactorScale x W initial e) →
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h l t)
            (fun σ=>|(G.canonicalMinimumSource M f).product σ|^(2*d)) 0 ≤
            (C^a*sourceMonomialScale x W initial)^(2*d) := by
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_continuum_center_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ch:=(Cf+Temp*Cs)*(1+Cmass)
  have hCh : 0 ≤ Ch:=by dsimp only [Ch];positivity
  obtain ⟨C,hC,HB⟩:=eventually_actual_minimum_source_centered_square_repeated_forest_product
    a d ha hd Bclock (4*Cf+2*Temp) Temp Cmass Ch (1+Temp) hCm hCh (by linarith)
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HB,(tendsto_add_atTop_nat 1).eventually HS] with n hn hs
  intro M hsource hxs1 L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T l t hl ht G f initial x W hxs hxW hmass
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let S:=fun e=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (G.sourceLowMass e)
  let field:=fun e=>(f e).field (M.bf (G.sourceLowMass e)) (M.hf (G.sourceLowMass e)) (S e)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hclock:=native_small_source_clock_full_square_budget M Temp Cf hCf hsource hxs1 as ho
  have HC (e : Fin a):=hsource (G.sourceLowMass e) (partitionPoint_mem as ho _)
  have hbond:=(hsource _ (partitionPoint_mem as ho as.length)).1
  have hc:=continuum_center_bound_closed_interval (n+1) M.bf M.hf M.hxs.le hCs.le (hs M)
  have hfield : ∀e,|field e| ≤ Ch*sourceFactorScale x W initial e:=by
    intro e
    have Hu:=partitionPoint_mem as ho (T.splitIndex (G.i e) (G.j e))
    have Hs : |S e| ≤ Cs*(M.xs+G.sourceLowMass e):=hc _ Hu
    have H:=native_source_field_bound (f e) (NNReal.coe_nonneg _) (HC e).1 (NNReal.coe_nonneg _)
      hCf hCs.le (add_nonneg M.hxs.le Hu.1) (HC e).2 Hs
    have Hmass : M.xs+G.sourceLowMass e ≤ (1+Cmass)*sourceFactorScale x W initial e:=by
      have Hx:=source_factor_scale_ge_initial hxW initial e
      nlinarith [hmass e]
    have H':=mul_le_mul_of_nonneg_left Hmass (show 0 ≤ Cf+Temp*Cs by positivity)
    exact H.trans (by simpa only [Ch,mul_assoc,ActualNaturalBoundaryShape.sourceLowMass] using H')
  have hbeta : ∀e,|(G.canonicalMinimumSource M f).β e| ≤ 1+Temp:=by
    intro e
    exact native_source_slope_bound (f e) (NNReal.coe_nonneg _) (HC e).1
  have halpha : ∀e,(G.canonicalMinimumSource M f).α e=field e-
      (G.canonicalMinimumSource M f).β e*S e:=fun e=>native_source_intercept_center (f e) _ _ _
  exact hk U T l t hl ht (G.canonicalMinimumSource M f) initial x W field hxs hxW
    hclock hbond hmass hfield hbeta halpha

end OAI.SKFluctuations.Cavity
