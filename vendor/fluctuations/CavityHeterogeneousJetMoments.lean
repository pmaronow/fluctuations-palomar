module

public import CavityHeterogeneousPairMoments
public import CavityOneErrorJetMoments

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
 theorem disorderOffDiagonalJets_oneError_scaled_pair_bound {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (Ks : List ((ℕ → S → S → ℝ) × ℝ)) {k : ℕ} (hk : 0 < k)
    {C : ℝ} (hC : 0 ≤ C)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r) (a : ℕ)
    (P : T.Assignment → ℝ) (hP : ∀ σ, |P σ| ≤ C)
    (A : ℕ → S → S → ℝ) (u z : T.Slot) (huz : u ≠ z)
    {D : ℕ → ℝ} (hD : ∀ j, 0 ≤ D j)
    (hsecond : ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => (A j (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2)
    (E : Fin a → ℕ → S → S → ℝ) (s t : Fin a → T.Slot) (hne : ∀ i, s i ≠ t i)
    (rho : Fin a → ℝ) (hrho : ∀ i, 0 < rho i)
    (htot : a+Ks.length=k)
    (hpre : ∀ i j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |E i j (pairSpin as j σ).1 (pairSpin as j σ).2|^(2*k)) x ≤ (rho i)^(2*k))
    (hpost : ∀ K ∈ Ks, ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |K.1 j (pairSpin as j σ).1 (pairSpin as j σ).2|^(2*k)) x ≤ K.2^(2*k))
    (hpositive : ∀ K ∈ Ks, 0 < K.2) :
    |disorderOffDiagonalJets w φ v q x (Ks.map Prod.fst) T
      (fun σ => P σ*A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*(∏ i, E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i))))| ≤
      absJetVariation r Ks.length*C*D (T.splitIndex u z)*(∏ i, rho i)*(Ks.map Prod.snd).prod := by
  induction Ks generalizing T r a with
  | nil =>
    have hae : a=k := by simpa only [List.length_nil,add_zero] using htot
    have ha : 0 < a := by omega
    have H := T.disorderExpect_oneError_product_scales hw φ ho v q x ha P hC
      (hD (T.splitIndex u z)) hP A u z huz E s t hne rho hrho
      (hsecond (T.splitIndex u z))
      (fun i => by simpa only [hae] using hpre i (T.splitIndex (s i) (t i)))
    simpa only [disorderOffDiagonalJets,List.length_nil,List.map_nil,List.prod_nil,absJetVariation,one_mul,mul_one,hae] using H
  | cons K Ks ih =>
    let B := absJetVariation (r+2) Ks.length*C*D (T.splitIndex u z)*(K.2*(∏ i, rho i))*(Ks.map Prod.snd).prod
    have hKpos := hpositive K List.mem_cons_self
    have hrprod : 0 ≤ ∏ i, rho i := Finset.prod_nonneg fun i _ => (hrho i).le
    have hpostprod : 0 ≤ (Ks.map Prod.snd).prod := List.prod_nonneg (by
      intro a ha
      obtain ⟨L,hL,rfl⟩ := List.mem_map.mp ha
      exact (hpositive L (List.mem_cons_of_mem K hL)).le)
    have hB : 0 ≤ B := by
      have hDj := hD (T.splitIndex u z)
      have hAV := absJetVariation_nonneg (r+2) Ks.length
      dsimp [B]
      positivity
    have hbound (b : MarkedPlacement T) (hb : b ∈ T.markedAttach 0)
        (c : MarkedPlacement b.tree) (hc : c ∈ b.tree.markedAttach 0) :
        |(1-c.hit b.mark)*disorderOffDiagonalJets w φ v q x (Ks.map Prod.fst) c.tree
          (profilePairTest
            (fun σ => P σ*A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*(∏ i, E i (T.splitIndex (s i) (t i))
              (T.atSlot σ (s i)) (T.atSlot σ (t i)))) K.1 b c)| ≤ B := by
      classical
      by_cases heq : c.mark = c.embed b.mark
      · simp only [MarkedPlacement.hit,ite_eq_left heq,sub_self,zero_mul,abs_zero]
        exact hB
      · simp only [MarkedPlacement.hit,ite_eq_right heq,sub_zero,one_mul]
        let sn : Fin (a+1) → c.tree.Slot :=
          Fin.cases (c.embed b.mark) (fun i => c.embed (b.embed (s i)))
        let tn : Fin (a+1) → c.tree.Slot :=
          Fin.cases c.mark (fun i => c.embed (b.embed (t i)))
        let En : Fin (a+1) → ℕ → S → S → ℝ := Fin.cases K.1 E
        let rn : Fin (a+1) → ℝ := Fin.cases K.2 rho
        have hrn : ∀ i, 0 < rn i := fun i => Fin.cases hKpos hrho i
        let un := c.embed (b.embed u)
        let zn := c.embed (b.embed z)
        let Pn := fun σ => P (b.restrict (c.restrict σ))
        have hEmbB := T.markedAttach_embed_preserves 0 b hb
        have hEmbC := b.tree.markedAttach_embed_preserves 0 c hc
        have hnuz : un ≠ zn := fun H => huz (hEmbB.1 (hEmbC.1 H))
        have hsplitA : c.tree.splitIndex un zn = T.splitIndex u z :=
          (hEmbC.2 _ _).trans (hEmbB.2 _ _)
        have hsplit (i : Fin a) : c.tree.splitIndex (c.embed (b.embed (s i)))
            (c.embed (b.embed (t i))) = T.splitIndex (s i) (t i) :=
          (hEmbC.2 _ _).trans (hEmbB.2 _ _)
        have hnn : ∀ i, sn i ≠ tn i := by
          intro i
          refine Fin.cases (Ne.symm heq) (fun i => ?_) i
          exact fun H => hne i (hEmbB.1 (hEmbC.1 H))
        have hPn : ∀ σ, |Pn σ| ≤ C := fun σ => hP _
        have hEn : ∀ i j, (pairClock as j).disorderExpect w φ v q
            (fun σ => |En i j (pairSpin as j σ).1 (pairSpin as j σ).2|^(2*k)) x ≤ (rn i)^(2*k) := by
          intro i
          refine Fin.cases (hpost K List.mem_cons_self) (fun i => hpre i) i
        have hKn : ∀ L ∈ Ks, ∀ j, (pairClock as j).disorderExpect w φ v q
            (fun σ => |L.1 j (pairSpin as j σ).1 (pairSpin as j σ).2|^(2*k)) x ≤ L.2^(2*k) :=
          fun L hL => hpost L (List.mem_cons_of_mem _ hL)
        have hleaf : c.tree.leaves ≤ r+2 := by
          have h1 := T.markedAttach_leaves 0 b hb
          have h2 := b.tree.markedAttach_leaves 0 c hc
          omega
        have htest : profilePairTest
            (fun σ => P σ*A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*(∏ i, E i (T.splitIndex (s i) (t i))
              (T.atSlot σ (s i)) (T.atSlot σ (t i)))) K.1 b c =
            fun σ => Pn σ*A (c.tree.splitIndex un zn) (c.tree.atSlot σ un) (c.tree.atSlot σ zn)*(∏ i, En i (c.tree.splitIndex (sn i) (tn i))
              (c.tree.atSlot σ (sn i)) (c.tree.atSlot σ (tn i))) := by
          funext σ
          simp only [profilePairTest,Fin.prod_univ_succ,sn,tn,En,Pn,
            Fin.cases_zero,Fin.cases_succ,hsplit,hsplitA,un,zn,b.restrict_at,c.restrict_at,b.spin_at,c.spin_at]
          ring
        rw [htest]
        have H := ih c.tree hleaf (a+1) Pn hPn un zn hnuz En sn tn hnn rn hrn (by simp only [List.length_cons] at htot; omega)
          hEn hKn (fun L hL => hpositive L (List.mem_cons_of_mem K hL))
        simpa only [hsplitA,B,Fin.prod_univ_succ,rn,Fin.cases_zero,Fin.cases_succ] using H
    have H := T.signedPair_abs_le_pairAbsSum
      (fun b c => (1-c.hit b.mark)*disorderOffDiagonalJets w φ v q x (Ks.map Prod.fst) c.tree
        (profilePairTest (fun σ => P σ*A (T.splitIndex u z) (T.atSlot σ u) (T.atSlot σ z)*(∏ i, E i (T.splitIndex (s i) (t i))
          (T.atSlot σ (s i)) (T.atSlot σ (t i)))) K.1 b c))
    have HB := T.pairAbsSum_mono hbound
    have HH := (H.trans HB).trans (T.pairAbsSum_constant_le ho hT hB)
    have hscale : 4*(r:ℝ)*(r+1)*B = absJetVariation r (K::Ks).length*C*D (T.splitIndex u z)*(∏ i, rho i)*((K::Ks).map Prod.snd).prod := by
      simp only [B,List.length_cons,absJetVariation,List.map_cons,List.prod_cons]
      ring
    rw [hscale] at HH
    have hn : 0 ≤ absJetVariation r (K::Ks).length*C*D (T.splitIndex u z)*(∏ i, rho i)*((K::Ks).map Prod.snd).prod := by
      simp only [List.map_cons,List.prod_cons]
      have hDj := hD (T.splitIndex u z)
      have hAV := absJetVariation_nonneg r (K::Ks).length
      positivity
    simp only [List.map_cons,disorderOffDiagonalJets,mul_assoc,abs_div,show |(2:ℝ)|=2 by norm_num]
    simp only [mul_assoc,List.map_cons,List.prod_cons] at HH hn ⊢
    linarith

end OAI.SKFluctuations.Hierarchy.ClockTree
