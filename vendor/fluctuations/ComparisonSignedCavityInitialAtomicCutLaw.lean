module

public import ComparisonSignedCavityInitialOutsideCutLaw

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S : Type}
set_option maxHeartbeats 18000000

theorem native_initial_marked_rows_exact_level {as : List PositiveMass} {T : ClockTree S as}
    (ps : List (MarkedPlacement T)) (s : T.Slot) (i : ℕ) (hi : 0 < i)
    (F : (V : ClockTree S as)→(V.Assignment→T.Assignment)→(V.Assignment→S)→ℝ) :
    nativeInitialMarkedRowsValue (ps.filter (fun p=>decide (p.tree.splitIndex (p.embed s) p.mark=i))) F=
      nativeInitialMarkedRowsValue (ps.filter (fun p=>decide (p.tree.splitIndex (p.embed s) p.mark ≤ i))) F-
        nativeInitialMarkedRowsValue (ps.filter (fun p=>decide (p.tree.splitIndex (p.embed s) p.mark ≤ i-1))) F := by
  induction ps with
  | nil=>simp only [List.filter_nil,nativeInitialMarkedRowsValue,List.map_nil,List.sum_nil,sub_self]
  | cons p ps ih=>
    by_cases heq : p.tree.splitIndex (p.embed s) p.mark=i
    · have hle : p.tree.splitIndex (p.embed s) p.mark ≤ i:=heq.le
      have hprev : ¬p.tree.splitIndex (p.embed s) p.mark ≤ i-1:=by omega
      have hd1 : decide (p.tree.splitIndex (p.embed s) p.mark ≤ i)=true:=by simp only [hle,decide_true]
      have hd2 : decide (p.tree.splitIndex (p.embed s) p.mark ≤ i-1)=false:=by simp only [hprev,decide_false]
      have hd0 : decide (p.tree.splitIndex (p.embed s) p.mark=i)=true:=by simp only [heq,decide_true]
      simp only [List.filter_cons,hd0,hd1,hd2,Bool.false_eq_true,↓reduceIte,
        nativeInitialMarkedRowsValue,List.map_cons,List.sum_cons] at ih ⊢
      linarith only [ih]
    · by_cases hle : p.tree.splitIndex (p.embed s) p.mark ≤ i
      · have hprev : p.tree.splitIndex (p.embed s) p.mark ≤ i-1:=by omega
        have hd1 : decide (p.tree.splitIndex (p.embed s) p.mark ≤ i)=true:=by simp only [hle,decide_true]
        have hd2 : decide (p.tree.splitIndex (p.embed s) p.mark ≤ i-1)=true:=by simp only [hprev,decide_true]
        have hd0 : decide (p.tree.splitIndex (p.embed s) p.mark=i)=false:=by simp only [heq,decide_false]
        simp only [List.filter_cons,hd0,hd1,hd2,Bool.false_eq_true,↓reduceIte,
          nativeInitialMarkedRowsValue,List.map_cons,List.sum_cons] at ih ⊢
        linarith only [ih]
      · have hprev : ¬p.tree.splitIndex (p.embed s) p.mark ≤ i-1:=by omega
        simpa [List.filter_cons,heq,hle,hprev] using ih

def nativeInitialAtomicCloneValue {as : List PositiveMass} (T : ClockTree S as)
    (i : ℕ) (a : ℝ)
    (F : (V : ClockTree S as)→(V.Assignment→T.Assignment)→(V.Assignment→S)→ℝ) : ℝ :=
  if i=0 then nativeInitialMarkedRowsValue (nativeInitialIndexedCutRows T 0 a) F else
    nativeInitialMarkedRowsValue (nativeInitialIndexedCutRows T i a) F-
      nativeInitialMarkedRowsValue (nativeInitialIndexedCutRows T (i-1) a) F

def nativeInitialAtomicRetainedResamplingValue {as : List PositiveMass} (T : ClockTree S as)
    (s : T.Slot) (i : ℕ) (a : ℝ)
    (F : (V : ClockTree S as)→(V.Assignment→T.Assignment)→(V.Assignment→S)→ℝ) : ℝ :=
  if i=0 then nativeInitialMarkedRowsValue (nativeInitialOutsideCutResidualRows T s 0 a) F else
    nativeInitialMarkedRowsValue (nativeInitialOutsideCutResidualRows T s i a) F-
      nativeInitialMarkedRowsValue (nativeInitialOutsideCutResidualRows T s (i-1) a) F

theorem native_initial_atomic_original_eq_clone_add_retained_resampling {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (i : ℕ) (a : ℝ)
    (F : (V : ClockTree S as)→(V.Assignment→T.Assignment)→(V.Assignment→S)→ℝ) :
    nativeInitialMarkedRowsValue ((T.markedAttach a).filter
      (fun p=>decide (p.tree.splitIndex (p.embed s) p.mark=i))) F=
      nativeInitialAtomicCloneValue T i a F+nativeInitialAtomicRetainedResamplingValue T s i a F := by
  by_cases hi : i=0
  · subst i
    have Hfilter : ((T.markedAttach a).filter
        (fun p=>decide (p.tree.splitIndex (p.embed s) p.mark=0)))=
        nativeOutsideMarkedRows T s 0 a := by
      rw [nativeOutsideMarkedRows_eq_filter]
      congr 1
      funext p
      simp only [Nat.le_zero]
    rw [Hfilter]
    simpa only [nativeInitialAtomicCloneValue,nativeInitialAtomicRetainedResamplingValue,ite_true] using
      native_initial_outside_to_indexed_cut_exact T s 0 a F
  · rw [native_initial_marked_rows_exact_level _ s i (by omega) F]
    rw [←nativeOutsideMarkedRows_eq_filter,←nativeOutsideMarkedRows_eq_filter,
      native_initial_outside_to_indexed_cut_exact T s i a F,
      native_initial_outside_to_indexed_cut_exact T s (i-1) a F]
    simp only [nativeInitialAtomicCloneValue,nativeInitialAtomicRetainedResamplingValue,ite_eq_right hi]
    ring

theorem native_initial_atomic_original_row_off_diagonal {as : List PositiveMass}
    (T : ClockTree S as) (s : T.Slot) (i : ℕ) (hi : i<as.length) (a : ℝ)
    (p : MarkedPlacement T) (hp : p∈(T.markedAttach a).filter
      (fun p=>decide (p.tree.splitIndex (p.embed s) p.mark=i))) :
    p.mark≠p.embed s := by
  have Hsplit : p.tree.splitIndex (p.embed s) p.mark=i:=by
    exact of_decide_eq_true (List.mem_filter.mp hp).2
  intro H
  rw [H,p.tree.splitIndex_self] at Hsplit
  omega

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree
variable {S ι : Type} [Fintype S] [Fintype ι]

theorem native_initial_atomic_original_disorder_eq_clone_add_retained_resampling
    {as : List PositiveMass} (T : ClockTree S as) (s : T.Slot) (i : ℕ) (a : ℝ)
    (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ) (v : ι→ℝ) (q : ℕ→ι→ℝ)
    (H : T.Assignment→S→ℝ) (x : ι→ℝ) :
    nativeInitialDisorderJointRows w φ v q ((T.markedAttach a).filter
      (fun p=>decide (p.tree.splitIndex (p.embed s) p.mark=i))) H x=
      nativeInitialAtomicCloneValue T i a
        (fun V R B=>V.disorderExpect w φ v q (fun σ=>H (R σ) (B σ)) x)+
      nativeInitialAtomicRetainedResamplingValue T s i a
        (fun V R B=>V.disorderExpect w φ v q (fun σ=>H (R σ) (B σ)) x) :=
  native_initial_atomic_original_eq_clone_add_retained_resampling T s i a _

theorem native_initial_atomic_clone_abs_le_mass_weighted_bound
    {as : List PositiveMass} (w : S→ℝ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    (T : ClockTree S as) (ho : MassOrdered 0 as) (i : ℕ)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (H : T.Assignment→S→ℝ) (x : ι→ℝ)
    {C : ℝ} (hC : 0≤C)
    (hrow : ∀k,k ≤ i→∀p∈nativeInitialIndexedCutRows T k 0,
      |p.tree.disorderExpect w φ v q (fun σ=>H (p.restrict σ) (p.spin σ)) x|≤C) :
    |nativeInitialAtomicCloneValue T i 0
      (fun V R B=>V.disorderExpect w φ v q (fun σ=>H (R σ) (B σ)) x)|≤
      4*(T.leaves:ℝ)*partitionPoint 0 as i*C := by
  have H0:=native_initial_cut_row_abs_le_mass_weighted_bound w φ T ho i v q H x hC (hrow i le_rfl)
  by_cases hi : i=0
  · subst i
    simp only [nativeInitialAtomicCloneValue]
    apply H0.trans
    have hmass : 0≤partitionPoint 0 as 0:=(partitionPoint_mem as ho 0).1
    have hprod : 0≤(T.leaves:ℝ)*partitionPoint 0 as 0*C:=mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) hmass) hC
    nlinarith only [hprod]
  · have H1:=native_initial_cut_row_abs_le_mass_weighted_bound w φ T ho (i-1) v q H x hC
      (hrow (i-1) (by omega))
    have Hmass:=partitionPoint_mono as ho (show i-1 ≤ i by omega)
    have H1': |nativeInitialDisorderJointRows w φ v q (nativeInitialIndexedCutRows T (i-1) 0) H x|≤
        2*(T.leaves:ℝ)*partitionPoint 0 as i*C:=H1.trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left Hmass
        (by positivity : 0≤2*(T.leaves:ℝ))) hC)
    simp only [nativeInitialAtomicCloneValue,ite_eq_right hi]
    dsimp only [nativeInitialDisorderJointRows] at H0 H1'
    exact (abs_sub _ _).trans (by nlinarith only [H0,H1'])

end OAI.SKFluctuations.Cavity
