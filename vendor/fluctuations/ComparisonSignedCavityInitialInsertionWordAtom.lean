module

public import ComparisonSignedCavityInitialInsertionWordCanonical
public import ComparisonSignedCavityInitialActualAtomModulusBudget

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators
set_option maxHeartbeats 28000000

 def nativeInitialTerminalLowDirections (n U i k : ℕ) (b h K : ℕ→ℝ) (t : ℝ) :
    Fin (k+1)→ℕ→(Spin n×Bool)→(Spin n×Bool)→ℝ :=
  Fin.lastCases
    (fun j σ τ=>if j=i then ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K) j σ τ else 0)
    (fun _=>ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K))

 theorem native_initial_terminal_site_count (k : ℕ) :
    (nativeInitialOrdinaryRowSet (Fin.cases true (fun _ : Fin k=>false))).card=k := by
  classical
  unfold nativeInitialOrdinaryRowSet
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [Fin.sum_univ_succ,Fin.cases_zero,Fin.cases_succ,Bool.true_eq_false,ite_false,ite_true,
    zero_add,Finset.sum_const,Finset.card_univ,Fintype.card_fin,Nat.nsmul_eq_mul,Nat.mul_one]

 theorem native_initial_terminal_word_test_eq_physical_atom
    (n U i k : ℕ) (b h K : ℕ→ℝ) (t : ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (g : NativeInitialInsertionWord T (k+1))
    {aDegree : ℕ} (G : ActualNaturalBoundaryShape n aDegree T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin aDegree→NativeSourceFactorForm) (a z : T.Slot)
    (hsplit : g.tree.splitIndex (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2=i)
    (σ : g.tree.Assignment) :
    g.test (nativeInitialTerminalLowDirections n U i k b h K t)
      (fun τ=>(G.canonicalMinimumSource M forms).product τ*sitePair T a z (T.cavityAssignment τ).2) σ=
      nativeOldInitialRowProduct n g.tree ((g.canonicalShape G).canonicalMinimumSource M forms).restProduct
        (nativeSmallCutOldErrorRestKernel n U b h K)
        (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2
        (fun e : Fin (k+1)=>nativeSmallCutOrdinaryRestKernel n U b h K
          (Fin.cases true (fun _ : Fin k=>false) e) (Fin.cases 0 (fun _ : Fin k=>t) e))
        (Fin.cases (g.embed a) (fun e=> (g.pairSlots e.castSucc).1))
        (Fin.cases (g.embed z) (fun e=> (g.pairSlots e.castSucc).2)) σ := by
  rw [g.test_eq_joint_product,Fin.prod_univ_castSucc]
  simp only [nativeInitialTerminalLowDirections,Fin.lastCases_castSucc,Fin.lastCases_last,hsplit,ite_true,
    sitePair_apply,g.restrict_at]
  rw [←g.canonicalShape_product G M forms]
  unfold nativeOldInitialRowProduct
  rw [Fin.prod_univ_succ]
  simp only [Fin.cases_zero,Fin.cases_succ,nativeSmallCutOrdinaryRestKernel,Bool.false_eq_true,ite_false,ite_true]
  rw [native_small_cut_old_error_eq_original_profile]
  simp_rw [native_small_cut_moving_kernel_eq_original_profile]
  rw [←((g.canonicalShape G).canonicalMinimumSource M forms).product_eq_restProduct]
  simp only [nativeRestRowKernel,one_mul,hsplit]
  ring

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

 theorem native_initial_terminal_direction_get (n U i k : ℕ) (b h K : ℕ→ℝ) (t : ℝ)
    (e : Fin (k+1)) :
    ((List.replicate k (ReplicaTree.coordinateProfile (fullFeature n) (cutLSlope n U t b h K))++
      [fun j σ τ=>if j=i then ReplicaTree.coordinateProfile (fullFeature n) (cutLowError n U b h K) j σ τ else 0])[e.val]'(by
        simpa only [List.length_append,List.length_replicate,List.length_singleton] using e.isLt))=
      nativeInitialTerminalLowDirections n U i k b h K t e := by
  refine Fin.lastCases ?_ (fun e=>?_) e
  · rw [List.getElem_append_right (by simp)]
    simp only [Fin.val_last,List.length_replicate,Nat.sub_self,List.getElem_cons_zero,
      nativeInitialTerminalLowDirections,Fin.lastCases_last]
  · rw [List.getElem_append_left (by simpa only [Fin.val_castSucc,List.length_replicate] using e.isLt)]
    simp only [List.getElem_replicate,nativeInitialTerminalLowDirections,Fin.lastCases_castSucc]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
open scoped BigOperators

 theorem native_initial_terminal_word_zero_error
    (n U i k : ℕ) (b h K : ℕ→ℝ) (t : ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (g : NativeInitialInsertionWord T (k+1))
    (P : T.Assignment→ℝ)
    (hi : g.tree.splitIndex (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2≠i) :
    g.test (nativeInitialTerminalLowDirections n U i k b h K t) P=(fun _=>0) := by
  funext σ
  rw [g.test_eq_joint_product,Fin.prod_univ_castSucc]
  simp only [nativeInitialTerminalLowDirections,Fin.lastCases_last,hi,ite_false,mul_zero]

 theorem native_initial_terminal_word_zero_high
    (n U i k : ℕ) (b h K : ℕ→ℝ) (t : ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (g : NativeInitialInsertionWord T (k+1))
    (P : T.Assignment→ℝ) (e : Fin k)
    (he : U≤g.tree.splitIndex (g.pairSlots e.castSucc).1 (g.pairSlots e.castSucc).2) :
    g.test (nativeInitialTerminalLowDirections n U i k b h K t) P=(fun _=>0) := by
  funext σ
  rw [g.test_eq_joint_product]
  have Hprod : (∏j,nativeInitialTerminalLowDirections n U i k b h K t j
      (g.tree.splitIndex (g.pairSlots j).1 (g.pairSlots j).2)
      (g.tree.atSlot σ (g.pairSlots j).1) (g.tree.atSlot σ (g.pairSlots j).2))=0:=by
    apply Finset.prod_eq_zero (Finset.mem_univ e.castSucc)
    simp only [nativeInitialTerminalLowDirections,Fin.lastCases_castSucc,ReplicaTree.coordinateProfile,
      cutLSlope,not_lt.mpr he,ite_false,Pi.zero_apply,zero_mul,Finset.sum_const_zero]
  rw [Hprod,mul_zero]

end OAI.SKFluctuations.Cavity

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators

 theorem native_initial_terminal_word_test_eq_physical_atom_plain
    (n U i k : ℕ) (b h K : ℕ→ℝ) (t : ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (g : NativeInitialInsertionWord T (k+1))
    {aDegree : ℕ} (G : ActualNaturalBoundaryShape n aDegree T)
    {m delta cl cu Az C0 Ct D Bclock : ℝ}
    (M : NativeOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock)
    (forms : Fin aDegree→NativeSourceFactorForm)
    (hsplit : g.tree.splitIndex (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2=i)
    (σ : g.tree.Assignment) :
    g.test (nativeInitialTerminalLowDirections n U i k b h K t) (G.canonicalMinimumSource M forms).product σ=
      nativeOldInitialRowProduct n g.tree ((g.canonicalShape G).canonicalMinimumSource M forms).restProduct
        (nativeSmallCutOldErrorRestKernel n U b h K)
        (g.pairSlots (Fin.last k)).1 (g.pairSlots (Fin.last k)).2
        (fun _ : Fin k=>nativeSmallCutOrdinaryRestKernel n U b h K false t)
        (fun e=> (g.pairSlots e.castSucc).1) (fun e=> (g.pairSlots e.castSucc).2) σ := by
  rw [g.test_eq_joint_product,Fin.prod_univ_castSucc]
  simp only [nativeInitialTerminalLowDirections,Fin.lastCases_castSucc,Fin.lastCases_last,hsplit,ite_true]
  rw [←g.canonicalShape_product G M forms]
  unfold nativeOldInitialRowProduct
  rw [native_small_cut_old_error_eq_original_profile]
  simp only [nativeSmallCutOrdinaryRestKernel,Bool.false_eq_true,ite_false]
  simp_rw [native_small_cut_moving_kernel_eq_original_profile]
  rw [←((g.canonicalShape G).canonicalMinimumSource M forms).product_eq_restProduct]
  rw [hsplit]
  ring

end OAI.SKFluctuations.Cavity
