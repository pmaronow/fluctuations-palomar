module

public import ComparisonSignedCavitySecondLowConstantStarOnlySource
public import ComparisonSignedCavitySecondLowInheritedErrorWordBudgets
public import ComparisonSignedCavitySecondLowActualOriginalConstantB0Budget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem native_second_low_sole_root_target_cut_observed_zero
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (i U : ℕ) (b h K : ℕ→ℝ)
    (as : List PositiveMass) (hU : U≤as.length) (j : Fin 8) :
    let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
    nativeSecondLowClassLedger n q U b h K g.tree hU (fun _=>1) (g.embed (singleSlot as)) g.mark j true=0 :=
  native_second_low_single_fresh_graft_observed_class_zero n q U b h K as hU i (fun _=>1) j

theorem native_second_low_sole_root_target_cut_joint_half_eq_fixed_and_moving
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (i U : ℕ) (b h K : ℕ→ℝ)
    (as : List PositiveMass) (ho : MassOrdered 0 as) (hU : U≤as.length) (hi : i<U) :
    let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
    nativeSecondLowJointLedger n q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2=
      ∑j : Fin 8,(
        nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j true/2+
        nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j false/2+
        nativeSecondLowMovingErrorUnobservedClassLedger n q i i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j true/2+
        nativeSecondLowMovingErrorUnobservedClassLedger n q i i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j false/2) := by
  dsimp only
  rw [native_second_low_single_fresh_graft_joint_ledger_half_eq_unobserved n q i U b h K as ho hU hi]
  apply Finset.sum_congr rfl
  intro j _
  rw [native_second_low_original_unobserved_class_eq_star_moving n q i U b h K _ ho hU (fun _=>1)
    ((nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).embed (singleSlot as))
    (nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i).mark j]
  simp only [add_div]

theorem eventually_actual_minimum_inherited_second_low_sole_root_target_cut_error_words
    (Bclock Temp Cf Couter : ℝ) (hTemp : 0≤Temp) (hCf : 0≤Cf) (hCouter : 0≤Couter)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0≤Az) (hC0 : 0 < C0) (hCt : 0≤Ct) :
    ∃C : ℝ,0<C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
        NativeActualSmallSourceClocks M Temp Cf → M.xs≤1 →
      ∀(L : ℕ) (us : List PositiveMass),
        (∀u∈us,u.val≤1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹≤M.xs →
      ∀ᶠk : ℕ in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(i U : ℕ) (x : ℝ),U≤as.length → i<U → M.xs≤x → x≤M.canonicalDirectTestBandScale →
          partitionPoint 0 as U≤Couter*x →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        ∀(p : MarkedPlacement g.tree),p∈g.tree.markedAttach 0 →
        ∀(r : MarkedPlacement p.tree),r∈p.tree.markedAttach 0 →
        ∀(s : MarkedPlacement r.tree),s∈r.tree.markedAttach 0 →
        ∀(t : MarkedPlacement s.tree),t∈s.tree.markedAttach 0 →
          r.tree.splitIndex (r.embed p.mark) r.mark<U → t.tree.splitIndex (t.embed s.mark) t.mark<U →
          (|nativeSecondLowFirstErrorWord n q U b h K (fun _=>1) (g.embed (singleSlot as)) g.mark p r s t|≤
            C*x*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as (r.tree.splitIndex (r.embed p.mark) r.mark)+1/(n+1:ℕ))) ∧
          (|nativeSecondLowSecondErrorWord n q U b h K (fun _=>1) (g.embed (singleSlot as)) g.mark p r s t|≤
            C*x*actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as (t.tree.splitIndex (t.embed s.mark) t.mark)+1/(n+1:ℕ))) := by
  obtain ⟨C,hC,H⟩:=eventually_actual_minimum_inherited_second_low_error_word_budgets
    (D:=D) 0 2 Bclock Temp Cf 0 hTemp hCf le_rfl hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨C*(1+Couter),mul_pos hC (by linarith),?_⟩
  filter_upwards [H] with n hn
  intro M HS hxs L us hus hret hmesh
  filter_upwards [hn M HS hxs L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro i U x hU hi hxsx _hxW houter p hp r hr s hs t ht Hfirst Hsecond
  let as:=finiteCutMasses us k
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let G:=nativeSecondLowEmptyOldShape n g.tree
  let forms : Fin 0→NativeSourceFactorForm:=Fin.elim0
  have Hmass : ∀e,G.sourceLowMass e≤(0:ℝ)*sourceFactorScale x x (∅ : Finset (Fin 0)) e:=by
    intro e
    exact Fin.elim0 e
  have Hproduct : (G.canonicalMinimumSource M forms).restProduct=(fun _=>1):=by
    funext τ
    simp only [ActualNaturalBoundaryShape.restProduct,Fin.prod_univ_zero]
  have Hleaves : g.tree.leaves≤2:=by
    have HL:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ 0 _ i)
    simpa only [single_leaves_exact] using HL
  have Htarget : g.tree.splitIndex (g.embed (singleSlot as)) g.mark<U:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split]
    exact lt_of_le_of_lt (Nat.min_le_left _ _) hi
  have HB:=hk U g.tree hU Hleaves G forms ∅ x x hxsx le_rfl Hmass (g.embed (singleSlot as)) g.mark Htarget
    p hp r hr s hs t ht Hfirst Hsecond
  rw [Hproduct] at HB
  have Hscale : sourceMonomialScale x x (∅ : Finset (Fin 0))=1:=by
    simp only [sourceMonomialScale,Finset.card_empty,Nat.sub_self,pow_zero,mul_one]
  rw [Hscale,mul_one,mul_one] at HB
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have HCerr : 0≤actualLowErrorComparisonConstant (4*Cf+2*Temp) Temp:=
    actualLowErrorComparisonConstant_nonneg _ hTemp
  have Hother (j : ℕ) (hj : j<U) : M.xs+partitionPoint 0 as j≤(1+Couter)*x:=by
    have HM:=(partitionPoint_mono as ho hj.le).trans houter
    nlinarith only [HM,hxsx]
  have HR (j : ℕ) : 0≤nativeOriginalCutLowErrorRadius n M.bf M.hf as j+1/(n+1:ℕ):=
    add_nonneg (Real.sqrt_nonneg _) (by positivity)
  constructor
  · apply HB.1.trans
    have HH:=mul_le_mul_of_nonneg_left (Hother _ Hsecond)
      (mul_nonneg hC.le (mul_nonneg HCerr (HR (r.tree.splitIndex (r.embed p.mark) r.mark))))
    convert HH using 1
    ring
  · apply HB.2.trans
    have HH:=mul_le_mul_of_nonneg_left (Hother _ Hfirst)
      (mul_nonneg hC.le (mul_nonneg HCerr (HR (t.tree.splitIndex (t.embed s.mark) t.mark))))
    convert HH using 1
    ring

end OAI.SKFluctuations.Cavity
