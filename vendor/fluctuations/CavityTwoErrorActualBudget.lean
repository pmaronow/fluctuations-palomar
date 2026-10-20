module

public import CavityTwoErrorSplitBudget

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
 theorem disorderOffDiagonalJets_markedTest_twoError_L2 {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (Ks : List ((ℕ → S → S → ℝ) × ℝ)) (a k : ℕ) (htot : a+Ks.length=k)
    {C M p : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hp : 2 < p)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) (hP : ∀ σ, |P σ| ≤ C)
    (E : Fin a → ℕ → S → S → ℝ) (s t : Fin a → T.Slot) (hst : ∀ i, s i ≠ t i)
    (rho : Fin a → ℝ) (hrho : ∀ i, 0 < rho i)
    (hpre : ∀ i j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |E i j (pairSpin as j σ).1 (pairSpin as j σ).2|^((p/(p-2))*(k:ℝ))) x ≤ (rho i)^((p/(p-2))*(k:ℝ)))
    (hpositive : ∀ K ∈ Ks, 0 < K.2)
    (A : ℕ → S → S → ℝ) (hA : ∀ j σ τ, |A j σ τ| ≤ M) {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => (A j (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (hmoment : ∀ K ∈ Ks, ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |K.1 j (pairSpin as j σ).1 (pairSpin as j σ).2|^((p/(p-2))*(k:ℝ))) x
        ≤ K.2^((p/(p-2))*(k:ℝ))) :
    |disorderOffDiagonalJets w φ v q x (A::A::Ks.map Prod.fst) T
      (fun σ => P σ*(∏ i, E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i))))| ≤
      pairForkVariation r*pairForkVariation (r+2)*absJetVariation (r+4) Ks.length*C*M^((p-2)/p)*M^((p-2)/p)*(∏ i, rho i)*(Ks.map Prod.snd).prod*
        (T.forkCost (fun j => D j^(4/p)) + (∫ u, edgeDensity 0 as (fun j => D j^(4/p)) u)) := by
  classical
  let Dt : ℕ → ℝ := fun j => D j^(4/p)
  have hDt : ∀ j, 0 ≤ Dt j := fun j => Real.rpow_nonneg (hD j) _
  let V := pairForkVariation (r+2)*absJetVariation (r+4) Ks.length*C*M^((p-2)/p)*M^((p-2)/p)*(∏ i, rho i)*(Ks.map Prod.snd).prod
  have hrprod : 0 ≤ ∏ i, rho i := Finset.prod_nonneg fun i _ => (hrho i).le
  have hkprod : 0 ≤ (Ks.map Prod.snd).prod := List.prod_nonneg (by
    intro a ha
    obtain ⟨K,hK,rfl⟩ := List.mem_map.mp ha
    exact (hpositive K hK).le)
  have hV : 0 ≤ V := by
    have hAV := absJetVariation_nonneg (r+4) Ks.length
    have hPV := pairForkVariation_nonneg (r+2)
    dsimp [V]
    positivity
  have hbound (b : MarkedPlacement T) (hb : b ∈ T.markedAttach 0)
      (c : MarkedPlacement b.tree) (hc : c ∈ b.tree.markedAttach 0) :
      |(1-c.hit b.mark)*disorderOffDiagonalJets w φ v q x (A::Ks.map Prod.fst) c.tree
        (profilePairTest (fun σ => P σ*(∏ i, E i (T.splitIndex (s i) (t i))
          (T.atSlot σ (s i)) (T.atSlot σ (t i)))) A b c)| ≤ V*(c.tree.forkCost Dt+edgeBudget 0 as Dt) := by
    by_cases heq : c.mark = c.embed b.mark
    · simp only [MarkedPlacement.hit,ite_eq_left heq,sub_self,zero_mul,abs_zero]
      exact mul_nonneg hV (add_nonneg (c.tree.forkCost_nonneg hDt) (edgeBudget_nonneg ho hDt))
    · simp only [MarkedPlacement.hit,ite_eq_right heq,sub_zero,one_mul]
      have hleaf : c.tree.leaves ≤ r+2 := by
        have h1 := T.markedAttach_leaves 0 b hb
        have h2 := b.tree.markedAttach_leaves 0 c hc
        omega
      let sn := fun i => c.embed (b.embed (s i))
      let tn := fun i => c.embed (b.embed (t i))
      have hbE := T.markedAttach_embed_preserves 0 b hb
      have hcE := b.tree.markedAttach_embed_preserves 0 c hc
      have hnn : ∀ i, sn i ≠ tn i := fun i H => hst i (hbE.1 (hcE.1 H))
      have hsplit (i : Fin a) : c.tree.splitIndex (sn i) (tn i) = T.splitIndex (s i) (t i) :=
        (hcE.2 _ _).trans (hbE.2 _ _)
      have H := disorderOffDiagonalJets_fixedPair_twoError_L2 hw φ ho v q x Ks a k htot hC hM hp
        c.tree hleaf (fun σ => P (b.restrict (c.restrict σ))) (fun σ => hP _)
        E sn tn hnn rho hrho hpre hpositive A (c.embed b.mark) c.mark (Ne.symm heq) hA
        hD hsecond hmoment
      have Htest : profilePairTest
          (fun σ => P σ*(∏ i, E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i)))) A b c =
          fun σ => P (b.restrict (c.restrict σ))*
            A (c.tree.splitIndex (c.embed b.mark) c.mark) (c.tree.atSlot σ (c.embed b.mark)) (c.tree.atSlot σ c.mark)*
              (∏ i, E i (c.tree.splitIndex (sn i) (tn i)) (c.tree.atSlot σ (sn i)) (c.tree.atSlot σ (tn i))) := by
        funext σ
        simp only [profilePairTest,hsplit,sn,tn,b.spin_at,c.spin_at,b.restrict_at,c.restrict_at]
        ring
      rw [Htest]
      simpa only [V,Dt,show (r+2)+2=r+4 by omega,mul_assoc,mul_left_comm,mul_comm,
        edgeDensity_integral ho (fun j => D j^(4/p))] using H
  have H := T.signedPair_abs_le_pairAbsSum
    (fun b c => (1-c.hit b.mark)*disorderOffDiagonalJets w φ v q x (A::Ks.map Prod.fst) c.tree
      (profilePairTest (fun σ => P σ*(∏ i, E i (T.splitIndex (s i) (t i))
          (T.atSlot σ (s i)) (T.atSlot σ (t i)))) A b c))
  have HB : T.pairAbsSum (fun b c => |(1-c.hit b.mark)*
      disorderOffDiagonalJets w φ v q x (A::Ks.map Prod.fst) c.tree (profilePairTest (fun σ => P σ*(∏ i, E i (T.splitIndex (s i) (t i))
          (T.atSlot σ (s i)) (T.atSlot σ (t i)))) A b c)|) ≤
      V*T.pairAbsSum (fun _ c => c.tree.forkCost Dt+edgeBudget 0 as Dt) := by
    rw [←T.pairAbsSum_const_mul]
    exact T.pairAbsSum_mono hbound
  have HG := T.pairAbsSum_forkBudget_le ho hT hDt (d:=0) le_rfl
  simp only [add_zero] at HG
  have HF := (H.trans HB).trans (mul_le_mul_of_nonneg_left HG hV)
  have hn : 0 ≤ pairForkVariation r*V*(T.forkCost Dt+edgeBudget 0 as Dt) :=
    mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) hV)
      (add_nonneg (T.forkCost_nonneg hDt) (edgeBudget_nonneg ho hDt))
  rw [edgeDensity_integral ho (fun j => D j^(4/p))]
  change |_/2| ≤ _
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  simp only [V,Dt,mul_assoc,mul_left_comm,mul_comm] at HF hn ⊢
  linarith

end OAI.SKFluctuations.Hierarchy.ClockTree
