module

public import ComparisonActualHighWallSecondLowSoleRootTargetFixedBudget
public import ComparisonActualHighWallSecondLowConstantMovingBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 36000000
set_option backward.isDefEq.respectTransparency false

private theorem wall_sole_root_abs_add_four (a b c d : ℝ) : |a+b+c+d|≤|a|+|b|+|c|+|d| := by
  exact (abs_add_le _ _).trans (add_le_add
    ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)

theorem eventually_actual_high_wall_second_low_sole_root_target_B0_budget
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
        ∀(i U : ℕ),U≤as.length → i<U → partitionPoint 0 as U≤Ccut*M.data.d →
        let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
        let Cerr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T
        let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
        let density:=nativeSecondLowLiteralMovingEntryDensity n M.bf M.hf as i i U
        |nativeSecondLowJointLedger n q U b h K g.tree (fun _=>1) [g.embed (singleSlot as),g.mark]/2|≤
          C*M.data.d^2*Cerr*di+C*M.data.d*Cerr*density := by
  obtain ⟨Ci,hCi,HI⟩:=eventually_actual_high_wall_second_low_sole_root_target_fixed_error_budget
    (D:=D) Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  obtain ⟨Cm,hCm,HM⟩:=eventually_actual_high_wall_second_low_constant_moving_literal_entry_budget
    (D:=D) 2 Bclock Ccut hCcut hm hdelta hroom hcl hcu hAz hC0 hCt
  refine ⟨16*(Ci+Cm),by positivity,?_⟩
  filter_upwards [HI,HM] with n hnI hnM
  intro M hwork L us hus hret hmesh
  filter_upwards [hnI M hwork L us hus hret hmesh,hnM M hwork L us hus hret hmesh] with k hgridI hgridM
  dsimp only at hgridI hgridM ⊢
  intro i U hU hi hcut
  let as:=finiteCutMasses us k
  let b:=fun j=>(M.bf (partitionPoint 0 as j):ℝ)
  let h:=fun j=>(M.hf (partitionPoint 0 as j):ℝ)
  let K:=fun j=>h j+b j*orderedPathS (n+1) M.bf M.hf (partitionPoint 0 as j)
  let q : ℕ→RestCoordinate n→ℝ:=fun j=>Sum.elim (fun _=>b j) (fun _=>h j)
  let g:=nativeFreshAtSlot (single (S:=Spin n×Bool) as) 0 (singleSlot as) i
  let Cerr:=actualLowErrorComparisonConstant (2*M.data.T) M.data.T
  let di:=nativeOriginalCutLowErrorRadius n M.bf M.hf as i+1/(n+1:ℕ)
  let rho:=nativeSecondLowLiteralMovingEntryDensity n M.bf M.hf as i i U
  have Hleaves : g.tree.leaves≤2:=by
    have HL:=(single (S:=Spin n×Bool) as).markedAttach_leaves 0 g (nativeFreshAtSlot_mem _ 0 _ i)
    simpa only [single_leaves_exact] using HL
  have Htarget : g.tree.splitIndex (g.embed (singleSlot as)) g.mark<U:=by
    rw [g.tree.splitIndex_symm,nativeFreshAtSlot_split]
    exact lt_of_le_of_lt (Nat.min_le_left _ _) hi
  have HPersistent : NativePersistentLowForks i i U g.tree:=
    (native_single_persistentLowForks i i U hU).freshStar 0 (singleSlot as)
  have ho : MassOrdered 0 as:=finiteCutMasses_ordered us hus k
  have hCerr : 0≤Cerr:=actualLowErrorComparisonConstant_nonneg _ (M.data.hepsilon.1.trans M.data.hepsilon.2).le
  have hdi : 0≤di:=add_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hx : 0 < M.data.d:=M.data.hd
  have hrho : 0≤rho:=by
    unfold rho nativeSecondLowLiteralMovingEntryDensity
    apply edgeBudget_nonneg ho
    intro j
    unfold nativeSecondLowMovingOriginalEntryRadius
    split_ifs
    · exact add_nonneg (Real.sqrt_nonneg _) (by positivity)
    · exact le_rfl
  have Hmoving (j : Fin 8) (firstError : Bool) :
      |nativeSecondLowMovingErrorUnobservedClassLedger n q i i U b h K g.tree hU (fun _=>1)
        (g.embed (singleSlot as)) g.mark j firstError/2|≤Cm*M.data.d*Cerr*rho:=by
    exact hgridM i i U g.tree hU le_rfl hi HPersistent Hleaves hcut
      (g.embed (singleSlot as)) g.mark Htarget j firstError
  have Hpoint (j : Fin 8) :
      |nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j true/2+
        nativeSecondLowFixedErrorUnobservedClassLedger n q i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j false/2+
        nativeSecondLowMovingErrorUnobservedClassLedger n q i i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j true/2+
        nativeSecondLowMovingErrorUnobservedClassLedger n q i i U b h K g.tree hU (fun _=>1)
          (g.embed (singleSlot as)) g.mark j false/2|≤2*Ci*M.data.d^2*Cerr*di+2*Cm*M.data.d*Cerr*rho:=by
    apply (wall_sole_root_abs_add_four _ _ _ _).trans
    apply (add_le_add (add_le_add (add_le_add
      (hgridI i U hU hi hcut j true) (hgridI i U hU hi hcut j false))
      (Hmoving j true)) (Hmoving j false)).trans_eq
    ring
  rw [native_second_low_sole_root_target_cut_joint_half_eq_fixed_and_moving n q i U b h K as ho hU hi]
  have Hsum:=Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 8)))=>Hpoint j)
  apply (Finset.abs_sum_le_sum_abs _ _).trans (Hsum.trans _)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have Hnon1 : 0≤M.data.d^2*Cerr*di:=by positivity
  have Hnon2 : 0≤M.data.d*Cerr*rho:=by positivity
  have H1:=mul_le_mul_of_nonneg_right (show 16*Ci≤16*(Ci+Cm) by linarith) Hnon1
  have H2:=mul_le_mul_of_nonneg_right (show 16*Cm≤16*(Ci+Cm) by linarith) Hnon2
  convert add_le_add H1 H2 using 1 <;> ring

end OAI.SKFluctuations.Cavity
