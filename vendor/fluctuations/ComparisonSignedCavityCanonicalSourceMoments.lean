module

public import ComparisonSignedCavityCanonicalSourceBudget
public import ComparisonSignedCavityFullSquareRepeatedBudget

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization
set_option maxHeartbeats 6000000

theorem eventually_actual_minimum_bare_canonical_square_even_moment
    (a d : ℕ) (ha : 0<a) (hd : 0<d) (Bclock Temp Cmass : ℝ) (hT : 0≤Temp) (hCm : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0<cl) (hcu : 0<cu) (hAz : 0≤Az) (hC0 : 0<C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp)→(∀u,M.h u=0)→M.xs≤1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤M.xs→
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
          l∈Icc (0:ℝ) 1→t∈Icc (0:ℝ) 1→
        ∀(G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
          (initial : Finset (Fin a)) (x W : ℝ),M.xs≤x→x≤W→
          (∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e)→
          T.disorderExpect (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h l t)
            (fun σ=>|(G.canonicalMinimumSource M f).product σ|^(2*d)) 0≤
            (C^a*sourceMonomialScale x W initial)^(2*d) := by
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_continuum_center_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cf:=NativeOverlapMinimum.bareSourceClockConstant cl Az D
  let Ch:=(Cf+Temp*Cs)*(1+Cmass)
  have hCf : 0≤Cf:=NativeOverlapMinimum.bare_source_clock_constant_nonneg hcl hAz
  have hCh : 0≤Ch := by dsimp [Ch];positivity
  obtain ⟨C,hC,HB⟩:=eventually_actual_minimum_source_centered_square_repeated_forest_product
    a d ha hd Bclock (4*Cf+2*Temp) Temp Cmass Ch (1+Temp) hCm hCh (by linarith)
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HB,(tendsto_add_atTop_nat 1).eventually HS] with n hn hs
  intro M hb hh hxs1 L us hus hret hmesh
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
  have hclock:=M.bare_sampled_full_square_clock_budget hcl hAz Temp hb hh hxs1 as ho
  have HC (e : Fin a):=M.bare_source_clock_bounds hcl hAz Temp hb hh
    (u:=G.sourceLowMass e) (partitionPoint_mem as ho _)
  have hbond:=(M.bare_source_clock_bounds hcl hAz Temp hb hh
    (partitionPoint_mem as ho as.length)).2.1
  have hc:=continuum_center_bound_closed_interval (n+1) M.bf M.hf M.hxs.le hCs.le (hs M)
  have hfield : ∀e,|field e|≤Ch*sourceFactorScale x W initial e := by
    intro e
    have Hu:=partitionPoint_mem as ho (T.splitIndex (G.i e) (G.j e))
    have Hs : |S e|≤Cs*(M.xs+G.sourceLowMass e) := hc _ Hu
    have H:=native_source_field_bound (f e) (HC e).1 (HC e).2.1 (HC e).2.2.1
      hCf hCs.le (add_nonneg M.hxs.le Hu.1) (HC e).2.2.2 Hs
    have Hmass : M.xs+G.sourceLowMass e≤(1+Cmass)*sourceFactorScale x W initial e := by
      have Hx:=source_factor_scale_ge_initial hxW initial e
      have Hm:=hmass e
      nlinarith
    have H' := mul_le_mul_of_nonneg_left Hmass (show 0≤Cf+Temp*Cs by positivity)
    exact H.trans (by simpa only [Ch,mul_assoc,ActualNaturalBoundaryShape.sourceLowMass] using H')
  have hbeta : ∀e,|(G.canonicalMinimumSource M f).β e|≤1+Temp := by
    intro e
    exact native_source_slope_bound (f e) (HC e).1 (HC e).2.1
  have hαeq : ∀e,(G.canonicalMinimumSource M f).α e=field e-
      (G.canonicalMinimumSource M f).β e*S e := by
    intro e
    exact native_source_intercept_center (f e) _ _ _
  exact hk U T l t hl ht (G.canonicalMinimumSource M f) initial x W field hxs hxW
    hclock hbond hmass hfield hbeta hαeq

end OAI.SKFluctuations.Cavity
