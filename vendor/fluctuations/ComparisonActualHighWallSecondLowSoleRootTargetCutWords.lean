module

public import ComparisonActualHighWallSecondLowSeparateErrorWords
public import ComparisonSignedCavitySecondLowSoleRootTargetCutSource

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false

theorem eventually_actual_high_wall_second_low_sole_root_target_cut_error_words
    (Bclock Ccut : ℝ) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        M.xs=M.data.d →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ),U ≤ as.length → i < U → partitionPoint 0 as U ≤ Ccut*M.data.d →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        ∀p∈g.tree.markedAttach 0,∀r∈p.tree.markedAttach 0,∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,
          r.tree.splitIndex (r.embed p.mark) r.mark < U → t.tree.splitIndex (t.embed s.mark) t.mark < U →
          (|nativeSecondLowFirstErrorWord n q U b h K (fun _=>1) (g.embed (singleSlot as)) g.mark p r s t| ≤
            C*M.data.d*actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as (r.tree.splitIndex (r.embed p.mark) r.mark)+1/(n+1:ℕ))) ∧
          (|nativeSecondLowSecondErrorWord n q U b h K (fun _=>1) (g.embed (singleSlot as)) g.mark p r s t| ≤
            C*M.data.d*actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as (t.tree.splitIndex (t.embed s.mark) t.mark)+1/(n+1:ℕ))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_high_wall_second_low_separate_error_word_budgets
    (D:=D) 0 2 Bclock 0 Ccut le_rfl hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C,hC,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i U hU hi hcut p hp r hr s hs t ht Hfirst Hsecond
  let as:=finiteCutMasses us k
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let G:=nativeSecondLowEmptyOldShape n g.tree
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  have Hmass : ∀e,G.sourceLowMass e ≤ (0:ℝ)*M.data.d:=fun e=>Fin.elim0 e
  have Hproduct : (G.canonicalHighWallSource M forms).restProduct=(fun _=>1):=by
    funext tau
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have Hleaves : g.tree.leaves ≤ 2:=by
    have HL:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ 0 _ i)
    simpa only [single_leaves_exact] using HL
  have Htarget : g.tree.splitIndex (g.embed (singleSlot as)) g.mark < U:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split]
    exact lt_of_le_of_lt (Nat.min_le_left _ _) hi
  have HB:=hk U g.tree hU hcut Hleaves G forms Hmass (g.embed (singleSlot as)) g.mark Htarget
    p hp r hr s hs t ht Hfirst Hsecond
  simpa only [Hproduct,pow_zero,mul_one] using HB

end OAI.SKFluctuations.Cavity
