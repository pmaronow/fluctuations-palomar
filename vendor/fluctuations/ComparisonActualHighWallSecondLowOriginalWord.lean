module

public import ComparisonActualHighWallSecondLowRawAtom
public import ComparisonActualGeneralCanonicalMarkedReset
public import ComparisonSignedCavitySecondLowInheritedInitialWordBudget
public import ComparisonSignedCavitySecondLowOriginalErrorWordAllocation

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false

theorem actual_high_wall_second_low_canonical_old_rest_product
    {n degree : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree → NativeSourceFactorForm)
    (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
    (r : MarkedPlacement p.tree) (hr : r∈p.tree.markedAttach 0)
    (s : MarkedPlacement r.tree) (hs : s∈r.tree.markedAttach 0)
    (t : MarkedPlacement s.tree) (ht : t∈s.tree.markedAttach 0) (sigma : t.tree.cavityLeft.Assignment) :
    ((nativeSecondLowCanonicalOldShape G p hp r hr s hs t ht).canonicalHighWallSource M forms).restProduct sigma=
      nativeSecondLowOldTest (G.canonicalHighWallSource M forms).restProduct p r s t sigma := by
  simp only [ActualNaturalBoundaryShape.canonicalHighWallSource,nativeSecondLowCanonicalOldShape,
    ActualNaturalBoundaryShape.retained_canonical_physical_restProduct,nativeSecondLowOldTest]

theorem eventually_actual_high_wall_second_low_original_word_budget
    (degree rBound : ℕ) (Bclock Cmass Ccut : ℝ) (hCm : 0 ≤ Cmass) (hCcut : 0 ≤ Ccut)
    {m delta cl cu Az C0 Ct D : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta) (hroom : delta < 3*m)
    (hcl : 0 < cl) (hcu : 0 < cu) (hAz : 0 ≤ Az) (hC0 : 0 < C0) (hCt : 0 ≤ Ct) :
    ∃C : ℝ,0 < C ∧ ∀ᶠn : ℕ in atTop,
      ∀M : ActualHighWallOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock,
      M.xs=M.data.d → ∀(L : ℕ) (us : List PositiveMass),
      (∀u∈us,u.val ≤ 1) → (∀u∈uniformMasses L,u∈us) → ((L+1:ℕ):ℝ)⁻¹ ≤ M.xs →
      ∀ᶠk in atTop,
        let as:=finiteCutMasses us k
        let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
        let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
        let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
        let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
        ∀(U : ℕ) (T : ClockTree (Spin n×Bool) as),U ≤ as.length →
          partitionPoint 0 as U ≤ Ccut*M.data.d → T.leaves ≤ rBound →
        ∀(G : ActualNaturalBoundaryShape n degree T) (forms : Fin degree → NativeSourceFactorForm),
          (∀e,G.sourceLowMass e ≤ Cmass*M.data.d) → ∀a z : T.Slot,T.splitIndex a z < U →
        ∀p∈T.markedAttach 0,∀r∈p.tree.markedAttach 0,∀s∈r.tree.markedAttach 0,∀t∈s.tree.markedAttach 0,
          r.tree.splitIndex (r.embed p.mark) r.mark < U → t.tree.splitIndex (t.embed s.mark) t.mark < U →
          |nativeSecondLowWordValue n q U b h K (G.canonicalHighWallSource M forms).restProduct a z p r s t| ≤
            C*M.data.d*actualLowErrorComparisonConstant (2*M.data.T) M.data.T*
              (nativeOriginalCutLowErrorRadius n M.bf M.hf as (r.tree.splitIndex (r.embed p.mark) r.mark)+
                nativeOriginalCutLowErrorRadius n M.bf M.hf as (t.tree.splitIndex (t.embed s.mark) t.mark)+
                2/(n+1:ℕ))*M.data.d^degree := by
  obtain ⟨Cp,Cr,hCp,hCr,H⟩:=eventually_actual_high_wall_second_low_raw_atom_budget
    (D:=D) degree 2 (rBound+4) Bclock Cmass Ccut hCm hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  let C:=Real.exp (wholeLawRowComparisonConstant (rBound+4)*(2*max Bclock 0))*Cp^degree*Cr
  refine ⟨C,by dsimp only [C];positivity,?_⟩
  filter_upwards [H] with n hn
  intro M hwork L us hus hret hmesh
  filter_upwards [hn M hwork L us hus hret hmesh] with k hk
  dsimp only at hk ⊢
  intro U T hU hcut hT G forms hmass a z haz p hp r hr s hs t ht Hfirst Hsecond
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let q : ℕ → RestCoordinate n → ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let Gfinal:=nativeSecondLowCanonicalOldShape G p hp r hr s hs t ht
  let af:=t.embed (s.embed (r.embed (p.embed a)))
  let zf:=t.embed (s.embed (r.embed (p.embed z)))
  let f:=t.embed (s.embed (r.embed p.mark))
  let c:=t.embed (s.embed r.mark)
  let e:=t.embed s.mark
  let d:=t.mark
  have ho:=finiteCutMasses_ordered us hus k
  have hfinal : t.tree.leaves ≤ rBound+4:=(native_second_low_four_mark_leaves_le p hp r hr s hs t ht).trans (by omega)
  have hfinalmass : ∀j,Gfinal.sourceLowMass j ≤ Cmass*M.data.d:=by
    intro j
    rw [native_second_low_canonical_old_shape_source_mass]
    exact hmass j
  have Hfc : t.tree.splitIndex f c=r.tree.splitIndex (r.embed p.mark) r.mark:=by
    dsimp only [f,c]
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,(r.tree.markedAttach_embed_preserves 0 s hs).2]
  have Hf : t.tree.splitIndex f c < U:=by rw [Hfc];exact Hfirst
  have He : t.tree.splitIndex e d < U:=Hsecond
  have Ha : t.tree.splitIndex af zf < U:=by
    dsimp only [af,zf]
    rw [(s.tree.markedAttach_embed_preserves 0 t ht).2,(r.tree.markedAttach_embed_preserves 0 s hs).2,
      (p.tree.markedAttach_embed_preserves 0 r hr).2,(T.markedAttach_embed_preserves 0 p hp).2]
    exact haz
  have Hne (u v : t.tree.Slot) (H : t.tree.splitIndex u v < U) : u ≠ v:=by
    intro HH
    rw [HH,t.tree.splitIndex_self] at H
    omega
  have HP : (Gfinal.canonicalHighWallSource M forms).restProduct=nativeSecondLowOldTest
      (G.canonicalHighWallSource M forms).restProduct p r s t:=by
    funext sigma
    exact actual_high_wall_second_low_canonical_old_rest_product M G forms p hp r hr s hs t ht sigma
  have Bfirst:=hk U t.tree 0 0 hU hcut (by norm_num) (by norm_num) hfinal Gfinal forms hfinalmass f c Hf
    (![false,true]) (![1,0]) (![e,af]) (![d,zf]) (by intro j;fin_cases j <;> norm_num)
    (by intro j;fin_cases j;exact Hne e d He;exact Hne af zf Ha)
  have Bsecond:=hk U t.tree 0 0 hU hcut (by norm_num) (by norm_num) hfinal Gfinal forms hfinalmass e d He
    (![false,true]) (![0,0]) (![f,af]) (![c,zf]) (by intro j;fin_cases j <;> norm_num)
    (by intro j;fin_cases j;exact Hne f c Hf;exact Hne af zf Ha)
  simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,Bool.false_eq_true,ite_false,ite_true,mul_one] at Bfirst Bsecond
  rw [HP] at Bfirst Bsecond
  rw [Hfc] at Bfirst
  rw [native_second_low_original_word_eq_error_allocations n q U b h K T ho _ a z p r s hs t ht]
  apply (abs_add_le _ _).trans
  apply (add_le_add Bfirst Bsecond).trans_eq
  dsimp only [nativeSecondLowFirstErrorWord,nativeSecondLowSecondErrorWord,C,e,d,q,K,b,h,as]
  ring

end OAI.SKFluctuations.Cavity
