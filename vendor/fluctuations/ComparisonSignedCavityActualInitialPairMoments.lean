module

public import ComparisonSignedCavityActualDecoupledPairTransport
public import ComparisonSignedCavityCanonicalSourceMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 14000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def nativePhysicalResourceCenter (n : ℕ) (bf hf : ℝ → ℝ≥0)
    (as : List PositiveMass) (j : ℕ) : ℝ :=
  pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
    (completedPathClock (n+1) bf hf) (orderedOverlap (n+1)) (partitionPoint 0 as j)

def nativeOnePairCenteredShape (n : ℕ) (as : List PositiveMass) (j : ℕ) :
    ActualNaturalBoundaryShape n 1 (ClockTree.pairClock as j) where
  α:=fun _=>0
  β:=fun _=>0
  i:=fun _=>ClockTree.pairRightSlot as j
  j:=fun _=>ClockTree.pairLeftSlot as j
  distinct:=fun _ H=>ClockTree.pairSlots_distinct as j H.symm
  lowInGrid:=fun _=>(ClockTree.pairClock (S:=Spin n×Bool) as j).splitIndex_le_clockLength _ _

theorem native_one_pair_shape_low_mass (n : ℕ) (as : List PositiveMass) (j : ℕ) (hj : j≤as.length) :
    (nativeOnePairCenteredShape n as j).sourceLowMass 0=partitionPoint 0 as j := by
  simp only [ActualNaturalBoundaryShape.sourceLowMass,nativeOnePairCenteredShape,
    ClockTree.splitIndex_symm (ClockTree.pairClock (S:=Spin n×Bool) as j),
    ClockTree.pairSlots_splitIndex,Nat.min_eq_left hj]

theorem native_one_pair_centered_product
    {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (as : List PositiveMass) (j : ℕ) (hj : j≤as.length)
    (σ : (ClockTree.pairClock (S:=Spin n×Bool) as j).Assignment) :
    ((nativeOnePairCenteredShape n as j).canonicalMinimumSource M (fun _=>.centered)).product σ=
      deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
        (joinSpin (ClockTree.pairSpin as j σ).2)-nativePhysicalResourceCenter n M.bf M.hf as j := by
  unfold ActualNaturalBoundaryShape.product fullBoundaryAffineProduct
  rw [Fin.prod_univ_one]
  simp only [ActualNaturalBoundaryShape.canonicalMinimumSource,NativeSourceFactorForm.intercept,
    NativeSourceFactorForm.slope]
  rw [native_one_pair_shape_low_mass n as j hj]
  simp only [nativeOnePairCenteredShape,ClockTree.pairLeft_atSlot,ClockTree.pairRight_atSlot,
    fullBoundaryAffineFactor]
  change -nativePhysicalResourceCenter n M.bf M.hf as j+
    1*deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
      (joinSpin (ClockTree.pairSpin as j σ).2)=_
  ring

theorem eventually_actual_minimum_initial_centered_pair_even_moment
    (d : ℕ) (hd : 0 < d) (Bclock Temp Cmass : ℝ) (hTemp : 0≤Temp) (hCm : 0≤Cmass)
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
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        ∀(U j : ℕ),j≤as.length→∀x : ℝ,M.xs≤x→partitionPoint 0 as j≤Cmass*x→
          (ClockTree.pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
            (finitePhysicalCavitySquareVariance n U as b h 0 0)
            (fun σ=>|deletedOverlap n (joinSpin (ClockTree.pairSpin as j σ).1)
              (joinSpin (ClockTree.pairSpin as j σ).2)-nativePhysicalResourceCenter n M.bf M.hf as j|^(2*d)) 0≤
            (C*x)^(2*d) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_bare_canonical_square_even_moment
    1 d (by norm_num) hd Bclock Temp Cmass hTemp hCm hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hb hh hxs L us hus hret hmesh
  filter_upwards [hn M hb hh hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  let as:=finiteCutMasses us k
  intro U j hj x hxsx hmass
  have Hpair:=hk U (ClockTree.pairClock as j) 0 0 (by norm_num) (by norm_num)
    (nativeOnePairCenteredShape n _ j) (fun _=>.centered) Finset.univ x x hxsx le_rfl (by
      intro e
      have he : e=(0:Fin 1):=Subsingleton.elim _ _
      subst e
      rw [native_one_pair_shape_low_mass n _ j hj]
      simpa only [sourceFactorScale,Finset.mem_univ,ite_true] using hmass)
  simp_rw [native_one_pair_centered_product M _ j hj] at Hpair
  simpa [sourceMonomialScale] using Hpair

theorem native_physical_resource_center_at_positive_cut (n : ℕ) (bf hf : ℝ → ℝ≥0)
    (hb : MonotoneOn bf (Icc (0:ℝ) 1)) (hh : MonotoneOn hf (Icc (0:ℝ) 1))
    (as : List PositiveMass) (ho : MassOrdered 0 as) (j : ℕ)
    (hpos : 0 < partitionPoint 0 as j) :
    nativePhysicalResourceCenter n bf hf as j=
      orderedPathS (n+1) bf hf (partitionPoint 0 as j) := by
  exact (orderedPathPair_eq_completed (n+1) (by omega) bf hf hb hh (orderedOverlap (n+1))
    ⟨hpos,(partitionPoint_mem as ho j).2⟩).symm

end OAI.SKFluctuations.Cavity
