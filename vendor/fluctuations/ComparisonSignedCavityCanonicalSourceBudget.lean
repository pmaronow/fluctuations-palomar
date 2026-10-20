module

public import ComparisonSignedCavityMinimumSourceClocks

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization
set_option maxHeartbeats 6000000

inductive NativeSourceFactorForm
  | centered
  | bondCentered
  | row

def NativeSourceFactorForm.slope : NativeSourceFactorForm → ℝ → ℝ
  | .centered, _ => 1
  | .bondCentered, b => b
  | .row, b => b

def NativeSourceFactorForm.intercept : NativeSourceFactorForm → ℝ → ℝ → ℝ → ℝ
  | .centered, _, _, S => -S
  | .bondCentered, b, _, S => -b*S
  | .row, _, h, _ => h

def NativeSourceFactorForm.field : NativeSourceFactorForm → ℝ → ℝ → ℝ → ℝ
  | .centered, _, _, _ => 0
  | .bondCentered, _, _, _ => 0
  | .row, b, h, S => h+b*S

theorem native_source_intercept_center (f : NativeSourceFactorForm) (b h S : ℝ) :
    f.intercept b h S=f.field b h S-f.slope b*S := by
  cases f <;> simp [NativeSourceFactorForm.intercept,NativeSourceFactorForm.field,
    NativeSourceFactorForm.slope]

theorem native_source_slope_bound (f : NativeSourceFactorForm) {b T : ℝ}
    (hb : 0≤b) (hbT : b≤T) : |f.slope b|≤1+T := by
  cases f <;> simp only [NativeSourceFactorForm.slope,abs_of_nonneg hb,abs_one] <;> linarith

theorem native_source_field_bound (f : NativeSourceFactorForm) {b h S t T Cf Cs : ℝ}
    (hb : 0≤b) (hbT : b≤T) (hh : 0≤h) (hCf : 0≤Cf) (hCs : 0≤Cs)
    (ht : 0≤t) (hhf : h≤Cf*t) (hS : |S|≤Cs*t) :
    |f.field b h S|≤(Cf+T*Cs)*t := by
  have hT : 0≤T := hb.trans hbT
  cases f with
  | centered => simp only [NativeSourceFactorForm.field,abs_zero];positivity
  | bondCentered => simp only [NativeSourceFactorForm.field,abs_zero];positivity
  | row =>
    calc
      |h+b*S| ≤ |h|+|b*S| := abs_add_le _ _
      _ = h+b*|S| := by rw [abs_of_nonneg hh,abs_mul,abs_of_nonneg hb]
      _ ≤ Cf*t+T*(Cs*t) := add_le_add hhf
        (mul_le_mul hbT hS (abs_nonneg S) hT)
      _ = _ := by ring

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def sourceLowMass (G : ActualNaturalBoundaryShape n a T) (e : Fin a) : ℝ :=
  partitionPoint 0 as (T.splitIndex (G.i e) (G.j e))

def canonicalMinimumSource {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm) :
    ActualNaturalBoundaryShape n a T :=
  { G with
    α:=fun e=>(f e).intercept (M.bf (G.sourceLowMass e)) (M.hf (G.sourceLowMass e))
      (pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
        (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (G.sourceLowMass e))
    β:=fun e=>(f e).slope (M.bf (G.sourceLowMass e)) }

end ActualNaturalBoundaryShape

theorem eventually_actual_minimum_bare_canonical_square_forest_product
    (a : ℕ) (ha : 0<a) (Bclock Temp Cmass : ℝ) (hT : 0≤Temp) (hCm : 0≤Cmass)
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
            (fun σ=>(G.canonicalMinimumSource M f).product σ^2) 0≤
            (C^a*sourceMonomialScale x W initial)^2 := by
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_continuum_center_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Cf:=NativeOverlapMinimum.bareSourceClockConstant cl Az D
  let Ch:=(Cf+Temp*Cs)*(1+Cmass)
  have hCf : 0≤Cf:=NativeOverlapMinimum.bare_source_clock_constant_nonneg hcl hAz
  have hCh : 0≤Ch := by dsimp [Ch];positivity
  obtain ⟨C,hC,HB⟩:=eventually_actual_minimum_source_centered_square_forest_product
    a ha Bclock (4*Cf+2*Temp) Temp Cmass Ch (1+Temp) hCm hCh (by linarith)
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
