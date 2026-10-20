module

public import ComparisonActualHighOnlyFiniteErrorGrowth

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy
open scoped Topology NNReal
set_option autoImplicit false

namespace ActualHighOnlyOverlapMinimum
variable {m delta cl cu Az C0 Ct D Bclock : ℝ} {dim : ℕ→ℕ}

inductive ActualHighOnlyErrorGrowthHistory
    (root : (k:ℕ)→ActualHighOnlyOverlapMinimum (dim k+1)
      m delta cl cu Az C0 Ct D Bclock) :
    ℕ → ((k:ℕ)→ActualHighOnlyOverlapMinimum (dim k+1)
      m delta cl cu Az C0 Ct D Bclock) → Prop
  | root : ActualHighOnlyErrorGrowthHistory root 0 root
  | child {depth : ℕ}
      {P Q : (k:ℕ)→ActualHighOnlyOverlapMinimum (dim k+1)
        m delta cl cu Az C0 Ct D Bclock}
      (history : ActualHighOnlyErrorGrowthHistory root depth P)
      (growth : ∀ᶠk : ℕ in atTop,
        ((dim k+1:ℕ):ℝ)^(delta/4)*(P k).context.E ≤ (Q k).context.E) :
      ActualHighOnlyErrorGrowthHistory root (depth+1) Q

theorem ActualHighOnlyErrorGrowthHistory.comp
    {root M : (k:ℕ)→ActualHighOnlyOverlapMinimum (dim k+1)
      m delta cl cu Az C0 Ct D Bclock}
    {depth : ℕ} (H : ActualHighOnlyErrorGrowthHistory root depth M)
    (phi : ℕ→ℕ) (hphi : Tendsto phi atTop atTop) :
    ActualHighOnlyErrorGrowthHistory
      (fun k=>root (phi k)) depth (fun k=>M (phi k)) := by
  induction H with
  | root => exact .root
  | child history growth ih => exact .child ih (hphi.eventually growth)

theorem ActualHighOnlyErrorGrowthHistory.finite_readout
    {root M : (k:ℕ)→ActualHighOnlyOverlapMinimum (dim k+1)
      m delta cl cu Az C0 Ct D Bclock}
    {depth : ℕ} (H : ActualHighOnlyErrorGrowthHistory root depth M) :
    ∃chain : Fin (depth+1) →
      (k:ℕ)→ActualHighOnlyOverlapMinimum (dim k+1)
        m delta cl cu Az C0 Ct D Bclock,
      chain 0=root ∧ chain (Fin.last depth)=M ∧
      ∀j : Fin depth,∀ᶠk : ℕ in atTop,
        ((dim k+1:ℕ):ℝ)^(delta/4)*(chain j.castSucc k).context.E ≤
          (chain j.succ k).context.E := by
  induction H with
  | root => exact ⟨fun _=>root,rfl,rfl,fun j=>Fin.elim0 j⟩
  | @child depth P Q history growth ih =>
    obtain ⟨chain,hzero,hlast,hgrowth⟩ := ih
    refine ⟨Fin.snoc chain Q,?_,?_,?_⟩
    · simpa using hzero
    · exact Fin.snoc_last _ _
    · intro j
      refine Fin.lastCases ?_ (fun i=>?_) j
      · simpa [hlast] using growth
      · simpa only [←Fin.castSucc_succ,Fin.snoc_castSucc] using hgrowth i

theorem ActualHighOnlyErrorGrowthHistory.false_at_propagation_depth
    (hm : 0< m) (hdelta : 0<delta) (hC0 : 0<C0)
    (hdim : Tendsto dim atTop atTop)
    {root M : (k:ℕ)→ActualHighOnlyOverlapMinimum (dim k+1)
      m delta cl cu Az C0 Ct D Bclock}
    (H : ActualHighOnlyErrorGrowthHistory root
      (actualPropagationDepth delta) M) : False := by
  obtain ⟨chain,_,_,hgrowth⟩ := H.finite_readout
  exact actual_error_growth_chain_along_false hm hdelta hC0 dim hdim
    chain hgrowth

end ActualHighOnlyOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
