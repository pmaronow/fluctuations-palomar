module

public import ComparisonSignedCavityFullSquareRawBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 6500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy LaplaceWindowFormalization

theorem actual_source_square_forest_product_square_le (n U a : ℕ) (ha : 0 < a)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (b h : ℕ→ℝ) (hb : Monotone b) (hh : Monotone h)
    (hb0 : ∀j,0 ≤ b j) (hh0 : ∀j,0 ≤ h j) {l t : ℝ} (hl : l∈Icc (0:ℝ) 1) (ht : t∈Icc (0:ℝ) 1)
    (G : ActualNaturalBoundaryShape n a T) (initial : Finset (Fin a))
    {x W Ca Cb Cd : ℝ} (hx : 0 < x) (hW : 0 < W)
    (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hCd : 0 ≤ Cd)
    (hα : ∀e,|G.α e| ≤ Ca*sourceFactorScale x W initial e)
    (hβ : ∀e,|G.β e| ≤ Cb)
    (hraw : ∀e,finitePhysicalDeletedRawBudget n a as b h
      (T.splitIndex (G.i e) (G.j e)) ≤ (Cd*sourceFactorScale x W initial e)^(2*a)) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0
      (finitePhysicalCavitySquareVariance n U as b h l t) (fun σ=>G.product σ^2) 0 ≤
      ((2*(Ca+Cb*Cd+1))^a*sourceMonomialScale x W initial)^2 := by
  let N:=fun e=>sourceFactorScale x W initial e
  let hN:=source_factor_scale_pos hx hW initial
  let P:=G.calibratedForest b h ha N hN Ca Cb Cd hCa hCb hCd hα hβ hraw
  have H:=actual_full_square_boundary_forest_product_square_le n U a ha T ho b h hb hh hb0 hh0 hl ht P
  have HP:=actual_calibrated_boundary_shape_product G b h ha N hN Ca Cb Cd
    hCa hCb hCd hα hβ hraw
  rw [source_factor_scale_product] at HP
  rw [HP] at H
  exact H

theorem eventually_actual_minimum_source_centered_square_forest_product
    (a : ℕ) (ha : 0 < a) (Bclock Btotal Bbond Cmass Ch Cb : ℝ)
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
              (finitePhysicalCavitySquareVariance n U as b h l t) (fun σ=>G.product σ^2) 0 ≤
              (C^a*sourceMonomialScale x W initial)^2 := by
  obtain ⟨Cd,hCd,HR⟩:=eventually_actual_minimum_deleted_raw_on_retained_net
    (D:=D) a ha Bclock Btotal Bbond hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cs,hCs,HS⟩:=eventually_actual_minimum_continuum_center_bound
    (D:=D) Bclock hm hdelta hroom hcl hcu hAz hC0 hCt
  let Ca:=Ch+Cb*Cs*(1+Cmass)
  let Cr:=Cd*(1+Cmass)
  refine ⟨2*(Ca+Cb*Cr+1),by dsimp [Ca,Cr];positivity,?_⟩
  filter_upwards [HR,(tendsto_add_atTop_nat 1).eventually HS] with n hn hns
  intro M L us hus hret hmesh
  filter_upwards [hn M L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T l t hl ht G initial x W field hxs hxW hclock hbond hmass hfield hβ hαeq
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let mass:=fun e=>partitionPoint 0 as (T.splitIndex (G.i e) (G.j e))
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hx : 0 < x:=M.hxs.trans_le hxs
  have hW : 0 < W:=hx.trans_le hxW
  have hcenter:=continuum_center_bound_closed_interval (n+1) M.bf M.hf M.hxs.le hCs.le (hns M)
  have hc : ∀e,|pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
      (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (mass e)| ≤ Cs*(M.xs+mass e) := by
    intro e
    exact hcenter _ (partitionPoint_mem as ho _)
  have hα : ∀e,|G.α e| ≤ Ca*sourceFactorScale x W initial e := by
    intro e
    rw [hαeq e]
    exact source_centered_affine_intercept_le hxs hxW hx.le hCm hCs.le hCb initial mass
      field G.β (fun e=>pathPairMoment (uniformWeight (n+1)) (finiteFeature (n+1))
        (completedPathClock (n+1) M.bf M.hf) (orderedOverlap (n+1)) (mass e))
      hmass hfield hβ hc e
  have hraw : ∀e,finitePhysicalDeletedRawBudget n a as b h
      (T.splitIndex (G.i e) (G.j e)) ≤ (Cr*sourceFactorScale x W initial e)^(2*a) := by
    intro e
    have H:=hk _ (G.lowInGrid e) hclock hbond
    have hne:= (source_factor_scale_pos hx hW initial e).le
    have Hmass : M.xs+mass e ≤ (1+Cmass)*sourceFactorScale x W initial e := by
      have Hx:=source_factor_scale_ge_initial hxW initial e
      have Hm:=hmass e
      nlinarith
    apply H.trans
    apply pow_le_pow_left₀ (mul_nonneg hCd.le (add_nonneg M.hxs.le (partitionPoint_mem as ho _).1))
    simpa only [Cr,mul_assoc] using mul_le_mul_of_nonneg_left Hmass hCd.le
  have had:=comparisonVariableEndpoint_clocks_admissible M.context.hc M.context.hk M.context.hkc
    M.context.hm M.context.hM M.b M.h M.context.hd.ne' M.hlam.le M.hlb M.hb M.hh M.hh0 M.alpha
  have hb : Monotone b:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.bf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.1 hx hy hxy) as ho
  have hh : Monotone h:=comp_partitionPoint_monotone
    (show MonotoneOn (fun u=>(M.hf u:ℝ)) (Icc (0:ℝ) 1) from
      fun x hx y hy hxy=>toNNReal_monotoneOn had.2.1 hx hy hxy) as ho
  exact actual_source_square_forest_product_square_le n U a ha T ho b h hb hh
    (fun _=>NNReal.coe_nonneg _) (fun _=>NNReal.coe_nonneg _) hl ht G initial hx hW
    (by dsimp [Ca];positivity) hCb (by dsimp [Cr];positivity) hα hβ hraw

end OAI.SKFluctuations.Cavity
