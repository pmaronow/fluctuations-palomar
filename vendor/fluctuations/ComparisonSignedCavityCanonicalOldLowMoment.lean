module

public import ComparisonSignedCavityCanonicalRestMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 8000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def sourceConsInitial {a : ℕ} (initial : Finset (Fin a)) : Finset (Fin (a+1)) :=
  initial.map ⟨Fin.succ,Fin.succ_injective _⟩

theorem source_cons_factor_zero {a : ℕ} (x W : ℝ) (initial : Finset (Fin a)) :
    sourceFactorScale x W (sourceConsInitial initial) 0=W := by
  simp [sourceFactorScale,sourceConsInitial]

theorem source_cons_factor_succ {a : ℕ} (x W : ℝ) (initial : Finset (Fin a)) (e : Fin a) :
    sourceFactorScale x W (sourceConsInitial initial) e.succ=sourceFactorScale x W initial e := by
  simp [sourceFactorScale,sourceConsInitial]

theorem source_cons_monomial {a : ℕ} (x W : ℝ) (initial : Finset (Fin a)) :
    sourceMonomialScale x W (sourceConsInitial initial)=W*sourceMonomialScale x W initial := by
  rw [←source_factor_scale_product,Fin.prod_univ_succ,source_cons_factor_zero]
  simp_rw [source_cons_factor_succ]
  rw [source_factor_scale_product]

namespace ActualNaturalBoundaryShape
variable {n a : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}

def consLowShape (G : ActualNaturalBoundaryShape n a T) (i j : T.Slot) (hij : i≠j) :
    ActualNaturalBoundaryShape n (a+1) T where
  α:=Fin.cases 0 G.α
  β:=Fin.cases 0 G.β
  i:=Fin.cases i G.i
  j:=Fin.cases j G.j
  distinct:=by intro e;refine Fin.cases hij (fun e=>G.distinct e) e
  lowInGrid:=by intro e;refine Fin.cases (T.splitIndex_le_clockLength i j) (fun e=>G.lowInGrid e) e

theorem cons_low_source_mass_zero (G : ActualNaturalBoundaryShape n a T) (i j : T.Slot) (hij : i≠j) :
    (G.consLowShape i j hij).sourceLowMass 0=partitionPoint 0 as (T.splitIndex i j) := rfl

theorem cons_low_source_mass_succ (G : ActualNaturalBoundaryShape n a T)
    (i j : T.Slot) (hij : i≠j) (e : Fin a) :
    (G.consLowShape i j hij).sourceLowMass e.succ=G.sourceLowMass e := rfl

def canonicalLowRestFactor {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (i j : T.Slot) (σ : T.cavityLeft.Assignment) : ℝ :=
  let u:=partitionPoint 0 as (T.splitIndex i j)
  fullBoundaryAffineFactor n (M.hf u) (M.bf u)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot j),false)
    (T.cavityLeft.atSlot σ (T.cavityLeftSlot i),false)

theorem canonical_cons_restProduct {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n a T) (f : Fin a→NativeSourceFactorForm)
    (i j : T.Slot) (hij : i≠j) (σ : T.cavityLeft.Assignment) :
    ((G.consLowShape i j hij).canonicalMinimumSource M (Fin.cases .row f)).restProduct σ=
      canonicalLowRestFactor M i j σ*(G.canonicalMinimumSource M f).restProduct σ := by
  unfold restProduct
  rw [Fin.prod_univ_succ]
  rfl

end ActualNaturalBoundaryShape

theorem eventually_actual_minimum_canonical_old_low_second_moment
    (a : ℕ) (Bclock Temp Cmass : ℝ) (hTemp : 0≤Temp) (hCm : 0≤Cmass)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        (∀u,M.b u=Temp)→(∀u,M.h u=0)→M.xs≤1→
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1)→(∀u∈uniformMasses L,u∈us)→((L+1:ℕ):ℝ)⁻¹≤M.xs→
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim
          (fun _=>(M.bf (partitionPoint 0 as j):ℝ)) (fun _=>(M.hf (partitionPoint 0 as j):ℝ))
        ∀(T : ClockTree (Spin n×Bool) as) (G : ActualNaturalBoundaryShape n a T)
          (f : Fin a→NativeSourceFactorForm) (initial : Finset (Fin a)) (x W : ℝ),
          M.xs≤x→x≤W→(∀e,G.sourceLowMass e≤Cmass*sourceFactorScale x W initial e)→
        ∀(i j : T.Slot),i≠j→partitionPoint 0 as (T.splitIndex i j)≤Cmass*W→
          T.cavityLeft.disorderExpect (restWeight n) (restFeature n) 0 q
            (fun σ=>(ActualNaturalBoundaryShape.canonicalLowRestFactor M i j σ*
              (G.canonicalMinimumSource M f).restProduct σ)^2) 0≤
            (C*W*(C^a*sourceMonomialScale x W initial))^2 := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_bare_canonical_rest_even_moment
    (a+1) 1 (by omega) (by omega) Bclock Temp Cmass hTemp hCm
    hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro T G f initial x W hxsx hxW hmass i j hij hlow
  have hmass' : ∀e,(G.consLowShape i j hij).sourceLowMass e≤
      Cmass*sourceFactorScale x W (sourceConsInitial initial) e := by
    intro e
    refine Fin.cases ?_ (fun e=>?_) e
    · simpa only [G.cons_low_source_mass_zero,source_cons_factor_zero] using hlow
    · simpa only [G.cons_low_source_mass_succ,source_cons_factor_succ] using hmass e
  have Hmoment:=hk T (G.consLowShape i j hij) (Fin.cases .row f)
    (sourceConsInitial initial) x W hxsx hxW hmass'
  simp_rw [ActualNaturalBoundaryShape.canonical_cons_restProduct] at Hmoment
  norm_num only [Nat.mul_one,sq_abs] at Hmoment
  rw [source_cons_monomial] at Hmoment
  convert Hmoment using 1 <;> ring

end OAI.SKFluctuations.Cavity
