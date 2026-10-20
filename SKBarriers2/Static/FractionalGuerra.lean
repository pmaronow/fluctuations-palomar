module

public import SKBarriers2.Interfaces
public import SKBarriers2.Overshoot.Defs
public import SKBarriers2.Static.FractionalGuerraBasic

@[expose] public section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Set
open OAI OAI.SK OAI.SK.Analytic

namespace SKBarriers2

def fractionalAtoms (k : ℕ) (s : ℝ) (m : Fin (k + 1) → ℝ) : Fin (k + 1) → ℝ :=
  hierarchyAtom k (fun i => m i.succ - s) (1 - s)

theorem fractionalAtoms_sum (k : ℕ) (s : ℝ) (m : Fin (k + 1) → ℝ) :
    ∑ j, fractionalAtoms k s m j = 1 - s :=
  hierarchyAtom_sum k _ _

theorem fractionalAtoms_nonneg {k : ℕ} (s : ℝ) (hs : s ≤ 1)
    (m : Fin (k + 1) → ℝ) (hm : ∀ i, m i ∈ Icc s 1) (hmono : Monotone m)
    (j : Fin (k + 1)) : 0 ≤ fractionalAtoms k s m j := by
  apply hierarchyAtom_nonneg_of_monotone k _ (1 - s) (sub_nonneg.mpr hs)
  · intro i
    exact ⟨sub_nonneg.mpr (hm i.succ).1, sub_le_sub_right (hm i.succ).2 s⟩
  · intro i l hil
    exact sub_le_sub_right (hmono (Fin.succ_le_succ_iff.mpr hil)) s

theorem fractionalAtoms_prefix {k : ℕ} (s : ℝ) (m : Fin (k + 1) → ℝ)
    (hm : m 0 = s) (b : Fin (k + 1)) :
    s + (∑ l, if l < b then fractionalAtoms k s m l else 0) = m b := by
  refine Fin.cases ?_ (fun i => ?_) b
  · simpa using hm.symm
  · have H := massFromAtoms_hierarchyAtom k (fun i => m i.succ - s) (1 - s) i
    have he : (∑ l, if l < i.succ then fractionalAtoms k s m l else 0) = m i.succ - s := by
      simpa only [massFromAtoms, fractionalAtoms, Fin.lt_def, Fin.val_succ,
        Nat.lt_add_one_iff] using H
    rw [he]
    ring

private theorem hierarchyAtom_one (k : ℕ) (j : Fin (k + 1)) :
    hierarchyAtom k (fun _ => (1 : ℝ)) 1 j = if j = 0 then 1 else 0 := by
  induction k with
  | zero => simp [hierarchyAtom, Fin.eq_zero j]
  | succ k ih =>
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [hierarchyAtom]
    · simp only [hierarchyAtom, Fin.lastCases_castSucc]
      simpa using ih i

theorem fractionalAtoms_sum_mul_parts {k : ℕ} (s : ℝ) (m v : Fin (k + 1) → ℝ)
    (hv : v 0 = 0) :
    (∑ j, fractionalAtoms k s m j * v j) =
      v (Fin.last k) - ∑ i : Fin k, m i.succ * (v i.succ - v i.castSucc) := by
  rw [fractionalAtoms, hierarchyAtom_sum_mul_parts]
  have htel := hierarchyAtom_sum_mul_parts k (fun _ => (1 : ℝ)) 1 v
  simp_rw [hierarchyAtom_one, ite_mul, one_mul, zero_mul] at htel
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, hv] at htel
  have htel' : (∑ i : Fin k, (v i.succ - v i.castSucc)) = v (Fin.last k) := by
    linarith
  simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [htel']
  ring

private theorem fractional_rankOne_siteValue {k : ℕ} (d : ℕ) (β s : ℝ)
    (m : Fin (k + 1) → ℝ) (hm : m 0 = s) (b : Fin (k + 1) → Fin d → ℝ) :
    vectorHierarchy ((k + 1) * 1)
      (fun j => s + siteBlockMass 1 k (fractionalAtoms k s m) j)
      (matrixSiteVector β (fun i (_ : Fin 1) => b i) (fun (a : Config d) u => spin (a u)))
      (siteValueTerminal (fun _ : Config d => 0)) 0 =
    vectorHierarchy (k + 1) m (fun i => β • b i)
      (fun x => ∑ u, scalarSpinTerminal (x u)) 0 := by
  have hm' : (fun j => s + siteBlockMass 1 k (fractionalAtoms k s m) j) =
      fun j => m (finProdFinEquiv.symm j).1 := by
    funext j
    exact fractionalAtoms_prefix s m hm _
  rw [hm']
  have hev : matrixSiteVector β (fun i (_ : Fin 1) => b i)
      (fun (a : Config d) u => spin (a u)) =
      replicaSpinMap d ∘ (fun i => β • b (finProdFinEquiv.symm i).1) := by
    funext i a
    simp only [matrixSiteVector, Function.comp_apply, replicaSpinMap_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [hev]
  have H := congrFun (vectorHierarchy_pullback (replicaSpinMap d) ((k + 1) * 1)
    (fun i => m (finProdFinEquiv.symm i).1) (fun i => β • b (finProdFinEquiv.symm i).1)
    (siteValueTerminal (fun _ : Config d => 0))) (0 : Fin d → ℝ)
  simp only [Function.comp_apply, map_zero] at H
  rw [← H, replicaSpin_terminal]
  rw [vectorHierarchy_blocks (k + 1) 1 m (fun i _ => β • b i), vectorBlockHierarchy_one]

theorem fractionalPressure_rankOne {N d k : ℕ} (hN : 0 < N) (β s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (D : Fin d → Fin d → ℝ) (hD : Nonempty (MatrixStates N d D))
    (m : Fin (k + 1) → ℝ) (hm0 : m 0 = s)
    (hm : ∀ i, m i ∈ Icc s 1) (hmono : Monotone m)
    (b : Fin (k + 1) → Fin d → ℝ) (hb0 : b 0 = 0) :
    fractionalPressure N d β s D + β ^ 2 * (d : ℝ) ^ 2 * s / (4 * (N : ℝ)) ≤
      vectorHierarchy (k + 1) m (fun i => β • b i)
        (fun x => ∑ u, scalarSpinTerminal (x u)) 0 +
      β ^ 2 / 4 * matrixSquare d (fun i j => D i j - rankOnePath d b (Fin.last k) i j) -
      β ^ 2 / 4 * ∑ i : Fin k, m i.succ *
        (matrixSquare d (rankOnePath d b i.succ) - matrixSquare d (rankOnePath d b i.castSucc)) := by
  have H := fractionalMatrixConstrainedPressure_le hN (by norm_num : 0 < 1) β s hs D hD
    (fun i (_ : Fin 1) => b i) (fractionalAtoms k s m)
    (fractionalAtoms_nonneg s hs1 m hm hmono) (fractionalAtoms_sum k s m)
  rw [fractional_rankOne_siteValue d β s m hm0 b] at H
  simp_rw [factorPath_rankOne] at H
  have hv : matrixSquare d (rankOnePath d b 0) = 0 := by
    have he : rankOnePath d b 0 = 0 := by
      funext u v
      simp [rankOnePath, hb0]
    rw [he]
    simp [matrixSquare]
  rw [fractionalAtoms_sum_mul_parts s m _ hv] at H
  rw [matrixSquare_sub]
  unfold matrixInner at H ⊢
  convert H using 1
  ring

theorem fractionalPressure_chain {N d : ℕ} (hN : 0 < N) (β s : ℝ)
    (hs : 0 < s) (hs1 : s ≤ 1)
    (D : Fin d → Fin d → ℝ) (hD : Nonempty (MatrixStates N d D))
    (l : List (ℝ × (Fin d → ℝ))) (hm : ∀ p ∈ l, p.1 ∈ Icc s 1)
    (hmono : l.Pairwise (fun p q => p.1 ≤ q.1)) :
    fractionalPressure N d β s D + β ^ 2 * (d : ℝ) ^ 2 * s / (4 * (N : ℝ)) ≤
      vectorIncrementChain (l.map (fun p => (p.1, β • p.2)))
        (fun x => ∑ u, scalarSpinTerminal (x u)) 0 +
      β ^ 2 / 4 * matrixSquare d (fun i j => D i j - matrixChainCovariance l i j) -
      β ^ 2 / 4 * matrixChainPenalty l 0 := by
  let m : Fin (l.length + 1) → ℝ := Fin.cons s (fun i => (l.get i).1)
  let b : Fin (l.length + 1) → Fin d → ℝ := Fin.cons 0 (fun i => (l.get i).2)
  have hm' : ∀ i, m i ∈ Icc s 1 := by
    intro i
    refine Fin.cases ⟨le_rfl, hs1⟩ (fun j => ?_) i
    exact hm _ (List.get_mem l j)
  have hsorted : Monotone m := by
    have H : ((s, 0) :: l).Pairwise (fun p q => p.1 ≤ q.1) :=
      List.pairwise_cons.mpr ⟨fun p hp => (hm p hp).1, hmono⟩
    have HL : List.ofFn (Fin.cons (s, 0) l.get) = (s, 0) :: l := by
      simp [List.ofFn_succ]
    rw [← HL, List.pairwise_ofFn] at H
    intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · have hh := H hij
      have he (a : Fin (l.length + 1)) :
          m a = ((Fin.cons (s, 0) l.get : Fin (l.length + 1) → ℝ × (Fin d → ℝ)) a).1 := by
        refine Fin.cases rfl (fun _ => rfl) a
      simpa only [← he] using hh
    · exact le_rfl
  have H := fractionalPressure_rankOne hN β s hs hs1 D hD m rfl hm' hsorted b rfl
  have hv : vectorHierarchy (l.length + 1) m (fun i => β • b i)
      (fun x => ∑ u, scalarSpinTerminal (x u)) =
      vectorIncrementChain (l.map (fun p => (p.1, β • p.2)))
        (fun x => ∑ u, scalarSpinTerminal (x u)) := by
    rw [← vectorIncrementChain_ofFn]
    have he : (fun i => (m i, β • b i)) =
        Fin.cons (s, 0) (fun i => ((l.get i).1, β • (l.get i).2)) := by
      funext i
      refine Fin.cases ?_ (fun _ => rfl) i
      simp [m, b]
    rw [he, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, vectorIncrementChain, vectorStep_zero]
    congr 1
    simpa only [List.ofFn_get, Function.comp_def] using
      (List.map_ofFn (f := l.get) (g := fun p => (p.1, β • p.2))).symm
  have hc : rankOnePath d b (Fin.last l.length) = matrixChainCovariance l := by
    rw [rankOnePath_cons_last]
    unfold matrixChainCovariance
    have he : l.map (fun p => (p.1, rankOneMatrix p.2)) =
        List.ofFn (fun i => ((l.get i).1, rankOneMatrix (l.get i).2)) := by
      simpa only [List.ofFn_get, Function.comp_def] using
        (List.map_ofFn (f := l.get) (g := fun p => (p.1, rankOneMatrix p.2)))
    rw [he, chainSum_ofFn]
  have hp : (∑ i : Fin l.length, m i.succ *
      (matrixSquare d (rankOnePath d b i.succ) - matrixSquare d (rankOnePath d b i.castSucc))) =
      matrixChainPenalty l 0 := by
    unfold matrixChainPenalty
    have he : l.map (fun p => (p.1, rankOneMatrix p.2)) =
        List.ofFn (fun i => ((l.get i).1, rankOneMatrix (l.get i).2)) := by
      simpa only [List.ofFn_get, Function.comp_def] using
        (List.map_ofFn (f := l.get) (g := fun p => (p.1, rankOneMatrix p.2)))
    rw [he, chainPotentialPenalty_ofFn]
    apply Finset.sum_congr rfl
    intro i _
    simp only [m, Fin.cons_succ, b, rankOnePath_cons_succ, rankOnePath_cons_castSucc, zero_add]
  rw [hv, hc, hp] at H
  exact H

end SKBarriers2
