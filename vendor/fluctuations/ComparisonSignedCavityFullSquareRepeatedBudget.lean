module

public import ComparisonSignedCavityFullSquareSourceBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 6500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

def ActualNaturalBoundaryShape.repeatFactors {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T) (d : ℕ) :
    ActualNaturalBoundaryShape n (a*d) T where
  α:=fun e=>G.α (finProdFinEquiv.symm e).1
  β:=fun e=>G.β (finProdFinEquiv.symm e).1
  i:=fun e=>G.i (finProdFinEquiv.symm e).1
  j:=fun e=>G.j (finProdFinEquiv.symm e).1
  distinct:=fun e=>G.distinct (finProdFinEquiv.symm e).1
  lowInGrid:=fun e=>G.lowInGrid (finProdFinEquiv.symm e).1

def sourceRepeatedResources {a : ℕ} (initial : Finset (Fin a)) (d : ℕ) :
    Finset (Fin (a*d)) :=
  Finset.univ.filter fun e=>(finProdFinEquiv.symm e).1∈initial

theorem repeated_factor_product (a d : ℕ) (f : Fin a→ℝ) :
    (∏e : Fin (a*d),f (finProdFinEquiv.symm e).1)=(∏e,f e)^d := by
  calc
    _ = ∏z : Fin a×Fin d,f z.1:=
      Fintype.prod_equiv finProdFinEquiv.symm _ _ (fun _=>rfl)
    _ = _:=by rw [Fintype.prod_prod_type_right];simp

theorem actual_repeated_shape_product_eq {n a : ℕ} {as : List PositiveMass}
    {T : ClockTree (Spin n×Bool) as} (G : ActualNaturalBoundaryShape n a T)
    (d : ℕ) (σ : T.Assignment) : (G.repeatFactors d).product σ=(G.product σ)^d := by
  change (∏e : Fin (a*d),fullBoundaryAffineFactor n (G.α (finProdFinEquiv.symm e).1)
    (G.β (finProdFinEquiv.symm e).1) (T.atSlot σ (G.j (finProdFinEquiv.symm e).1))
    (T.atSlot σ (G.i (finProdFinEquiv.symm e).1)))=_
  exact repeated_factor_product a d (fun e=>fullBoundaryAffineFactor n (G.α e) (G.β e)
    (T.atSlot σ (G.j e)) (T.atSlot σ (G.i e)))

theorem source_repeated_factor_scale_eq {a : ℕ} (x W : ℝ)
    (initial : Finset (Fin a)) (d : ℕ) (e : Fin (a*d)) :
    sourceFactorScale x W (sourceRepeatedResources initial d) e=
      sourceFactorScale x W initial (finProdFinEquiv.symm e).1 := by
  classical
  simp only [sourceFactorScale,sourceRepeatedResources,Finset.mem_filter,Finset.mem_univ,true_and]

theorem source_repeated_monomial_scale_eq {a : ℕ} (x W : ℝ)
    (initial : Finset (Fin a)) (d : ℕ) :
    sourceMonomialScale x W (sourceRepeatedResources initial d)=(sourceMonomialScale x W initial)^d := by
  rw [←source_factor_scale_product]
  simp_rw [source_repeated_factor_scale_eq]
  rw [repeated_factor_product,source_factor_scale_product]

theorem abs_even_repeat_square (z : ℝ) (d : ℕ) : |z|^(2*d)=(z^d)^2 := by
  rw [Nat.mul_comm 2 d,pow_mul,←abs_pow,sq_abs]

theorem repeated_source_budget_eq {a : ℕ} (C x W : ℝ)
    (initial : Finset (Fin a)) (d : ℕ) :
    (C^(a*d)*sourceMonomialScale x W (sourceRepeatedResources initial d))^2=
      (C^a*sourceMonomialScale x W initial)^(2*d) := by
  rw [source_repeated_monomial_scale_eq,pow_mul,←mul_pow,←pow_mul,Nat.mul_comm d 2]

theorem eventually_actual_minimum_source_centered_square_repeated_forest_product
    (a d : ℕ) (ha : 0 < a) (hd : 0 < d) (Bclock Btotal Bbond Cmass Ch Cb : ℝ)
    (hCm : 0 ≤ Cmass) (hCh : 0 ≤ Ch) (hCb : 0 ≤ Cb)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
        ∀ᶠ k : ℕ in atTop,
          let as:=finiteCutMasses us k
          let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
          let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
          ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as) (l t : ℝ),
            l∈Icc (0:ℝ) 1 → t∈Icc (0:ℝ) 1 →
          ∀(G : ActualNaturalBoundaryShape n a T) (initial : Finset (Fin a))
            (x W : ℝ) (field : Fin a→ℝ),M.xs ≤ x → x ≤ W →
            finitePhysicalMixedClock (n+1) as b h as.length+b as.length+h as.length ≤ Btotal →
            b as.length ≤ Bbond →
            (∀e,partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)) ≤
              Cmass*sourceFactorScale x W initial e) →
            (∀e,|field e| ≤ Ch*sourceFactorScale x W initial e) →
            (∀e,|G.β e| ≤ Cb) →
            (∀e,G.α e=field e-G.β e*pathPairMoment (uniformWeight (n+1))
              (finiteFeature (n+1)) (completedPathClock (n+1) M.bf M.hf)
              (orderedOverlap (n+1)) (partitionPoint 0 as (T.splitIndex (G.i e) (G.j e)))) →
            T.disorderExpect (fullWeight n) (fullFeature n) 0
              (finitePhysicalCavitySquareVariance n U as b h l t) (fun σ=>|G.product σ|^(2*d)) 0 ≤
              (C^a*sourceMonomialScale x W initial)^(2*d) := by
  obtain ⟨C,hC,HC⟩:=eventually_actual_minimum_source_centered_square_forest_product
    (D:=D) (a*d) (Nat.mul_pos ha hd) Bclock Btotal Bbond Cmass Ch Cb
    hCm hCh hCb hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [HC] with n hn
  intro M L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T l t hl ht G initial x W field hxs hxW hclock hbond hmass hfield hβ hαeq
  have H:=hk U T l t hl ht (G.repeatFactors d) (sourceRepeatedResources initial d) x W
    (fun e=>field (finProdFinEquiv.symm e).1) hxs hxW hclock hbond
    (fun e=>by
      rw [source_repeated_factor_scale_eq]
      exact hmass (finProdFinEquiv.symm e).1)
    (fun e=>by
      rw [source_repeated_factor_scale_eq]
      exact hfield (finProdFinEquiv.symm e).1)
    (fun e=>hβ (finProdFinEquiv.symm e).1)
    (fun e=>hαeq (finProdFinEquiv.symm e).1)
  simp_rw [actual_repeated_shape_product_eq] at H
  rw [repeated_source_budget_eq] at H
  have HE : (fun σ=>(G.product σ^d)^2)=(fun σ=>|G.product σ|^(2*d)) := by
    funext σ
    exact (abs_even_repeat_square (G.product σ) d).symm
  rw [HE] at H
  exact H

end OAI.SKFluctuations.Cavity
