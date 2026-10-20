module

public import CavityAllDiagonalCancellation
public import CavityMarkedEmbedding

@[expose] public section

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]
local instance : DecidableEq ι := Classical.decEq ι

 theorem disorderOffDiagonalJets_pair_moment_bound {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (Ks : List (ℕ → S → S → ℝ)) {p : ℕ} (hp : 0 < p)
    {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r) (a : ℕ)
    (P : T.Assignment → ℝ) (hP : ∀ σ, |P σ| ≤ C)
    (E : Fin a → ℕ → S → S → ℝ) (s t : Fin a → T.Slot) (hne : ∀ i, s i ≠ t i)
    (htot : a+Ks.length=p)
    (hpre : ∀ i j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |E i j (pairSpin as j σ).1 (pairSpin as j σ).2|^p) x ≤ rho^p)
    (hpost : ∀ K ∈ Ks, ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |K j (pairSpin as j σ).1 (pairSpin as j σ).2|^p) x ≤ rho^p) :
    |disorderOffDiagonalJets w φ v q x Ks T
      (fun σ => P σ*(∏ i, E i (T.splitIndex (s i) (t i)) (T.atSlot σ (s i)) (T.atSlot σ (t i))))| ≤
      absJetVariation r Ks.length*C*rho^p := by
  induction Ks generalizing T r a with
  | nil =>
    have hae : a=p := by simpa only [List.length_nil,add_zero] using htot
    have ha : 0 < a := by omega
    have H := T.disorderExpect_pair_product_actual hw φ ho v q x ha s t hne P
      (fun i σ τ => E i (T.splitIndex (s i) (t i)) σ τ) hC hP
      (fun i => by simpa only [hae] using hpre i (T.splitIndex (s i) (t i)))
    simpa only [disorderOffDiagonalJets,List.length_nil,absJetVariation,one_mul,hae] using H
  | cons K Ks ih =>
    let D := absJetVariation (r+2) Ks.length*C*rho^p
    have hD : 0 ≤ D := mul_nonneg
      (mul_nonneg (absJetVariation_nonneg _ _) hC) (pow_nonneg hrho _)
    have hbound (b : MarkedPlacement T) (hb : b ∈ T.markedAttach 0)
        (c : MarkedPlacement b.tree) (hc : c ∈ b.tree.markedAttach 0) :
        |(1-c.hit b.mark)*disorderOffDiagonalJets w φ v q x Ks c.tree
          (profilePairTest
            (fun σ => P σ*(∏ i, E i (T.splitIndex (s i) (t i))
              (T.atSlot σ (s i)) (T.atSlot σ (t i)))) K b c)| ≤ D := by
      classical
      by_cases heq : c.mark = c.embed b.mark
      · simp only [MarkedPlacement.hit,ite_eq_left heq,sub_self,zero_mul,abs_zero]
        exact hD
      · simp only [MarkedPlacement.hit,ite_eq_right heq,sub_zero,one_mul]
        let sn : Fin (a+1) → c.tree.Slot :=
          Fin.cases (c.embed b.mark) (fun i => c.embed (b.embed (s i)))
        let tn : Fin (a+1) → c.tree.Slot :=
          Fin.cases c.mark (fun i => c.embed (b.embed (t i)))
        let En : Fin (a+1) → ℕ → S → S → ℝ := Fin.cases K E
        let Pn := fun σ => P (b.restrict (c.restrict σ))
        have hEmbB := T.markedAttach_embed_preserves 0 b hb
        have hEmbC := b.tree.markedAttach_embed_preserves 0 c hc
        have hsplit (i : Fin a) : c.tree.splitIndex (c.embed (b.embed (s i)))
            (c.embed (b.embed (t i))) = T.splitIndex (s i) (t i) :=
          (hEmbC.2 _ _).trans (hEmbB.2 _ _)
        have hnn : ∀ i, sn i ≠ tn i := by
          intro i
          refine Fin.cases (Ne.symm heq) (fun i => ?_) i
          exact fun H => hne i (hEmbB.1 (hEmbC.1 H))
        have hPn : ∀ σ, |Pn σ| ≤ C := fun σ => hP _
        have hEn : ∀ i j, (pairClock as j).disorderExpect w φ v q
            (fun σ => |En i j (pairSpin as j σ).1 (pairSpin as j σ).2|^p) x ≤ rho^p := by
          intro i
          refine Fin.cases (hpost K List.mem_cons_self) (fun i => hpre i) i
        have hKn : ∀ L ∈ Ks, ∀ j, (pairClock as j).disorderExpect w φ v q
            (fun σ => |L j (pairSpin as j σ).1 (pairSpin as j σ).2|^p) x ≤ rho^p :=
          fun L hL => hpost L (List.mem_cons_of_mem _ hL)
        have hleaf : c.tree.leaves ≤ r+2 := by
          have h1 := T.markedAttach_leaves 0 b hb
          have h2 := b.tree.markedAttach_leaves 0 c hc
          omega
        have htest : profilePairTest
            (fun σ => P σ*(∏ i, E i (T.splitIndex (s i) (t i))
              (T.atSlot σ (s i)) (T.atSlot σ (t i)))) K b c =
            fun σ => Pn σ*(∏ i, En i (c.tree.splitIndex (sn i) (tn i))
              (c.tree.atSlot σ (sn i)) (c.tree.atSlot σ (tn i))) := by
          funext σ
          simp only [profilePairTest,Fin.prod_univ_succ,sn,tn,En,Pn,
            Fin.cases_zero,Fin.cases_succ,hsplit,b.restrict_at,c.restrict_at,b.spin_at,c.spin_at]
          ring
        rw [htest]
        exact ih c.tree hleaf (a+1) Pn hPn En sn tn hnn (by simp only [List.length_cons] at htot; omega)
          hEn hKn
    have H := T.signedPair_abs_le_pairAbsSum
      (fun b c => (1-c.hit b.mark)*disorderOffDiagonalJets w φ v q x Ks c.tree
        (profilePairTest (fun σ => P σ*(∏ i, E i (T.splitIndex (s i) (t i))
          (T.atSlot σ (s i)) (T.atSlot σ (t i)))) K b c))
    have HB := T.pairAbsSum_mono hbound
    have HH := (H.trans HB).trans (T.pairAbsSum_constant_le ho hT hD)
    have hscale : 4*(r:ℝ)*(r+1)*D = absJetVariation r (K::Ks).length*C*rho^p := by
      simp only [D,List.length_cons,absJetVariation]
      ring
    rw [hscale] at HH
    have hn : 0 ≤ absJetVariation r (K::Ks).length*C*rho^p := mul_nonneg
      (mul_nonneg (absJetVariation_nonneg _ _) hC) (pow_nonneg hrho _)
    simp only [disorderOffDiagonalJets,mul_assoc,abs_div,show |(2:ℝ)|=2 by norm_num]
    simp only [mul_assoc] at HH hn
    linarith

 theorem disorderOffDiagonalJets_moment_bound {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) {as : List PositiveMass} (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (x : ι → ℝ)
    (Ks : List (ℕ → S → S → ℝ)) (hk : 0 < Ks.length)
    {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) (hP : ∀ σ, |P σ| ≤ C)
    (hpost : ∀ K ∈ Ks, ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |K j (pairSpin as j σ).1 (pairSpin as j σ).2|^Ks.length) x ≤ rho^Ks.length) :
    |disorderOffDiagonalJets w φ v q x Ks T P| ≤
      absJetVariation r Ks.length*C*rho^Ks.length := by
  have H := disorderOffDiagonalJets_pair_moment_bound hw φ ho v q x Ks hk hC hrho
    T hT 0 P hP Fin.elim0 Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i)
    (by omega) (fun i => Fin.elim0 i) hpost
  simpa only [Fin.prod_univ_zero,mul_one] using H

 theorem disorderProfileJets_moment_bound {w : S → ℝ} (hw : ∀ σ, 0 < w σ)
    (φ : S → (ι → ℝ) →L[ℝ] ℝ) (A : ι → ℝ)
    (hA : ∀ σ i, (φ σ (Pi.single i 1))^2=A i)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (hq : ∀ i, Monotone (fun j => q j i)) (hq0 : ∀ i, v i ≤ q 0 i)
    (Ds : List (ℕ → ι → ℝ)) (hk : 0 < Ds.length) {B : ℝ} (hB : 0 ≤ B)
    (hDs : ∀ D ∈ Ds, ∀ j i, |D j i| ≤ B)
    {C rho : ℝ} (hC : 0 ≤ C) (hrho : 0 ≤ rho)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment → ℝ) (hP : ∀ σ, |P σ| ≤ C) (x : ι → ℝ)
    (hmoment : ∀ D ∈ Ds, ∀ j, (pairClock as j).disorderExpect w φ v q
      (fun σ => |ReplicaTree.coordinateProfile φ D j
        (pairSpin as j σ).1 (pairSpin as j σ).2|^Ds.length) x ≤ rho^Ds.length) :
    |disorderProfileJets w φ v q x (Ds.map (ReplicaTree.coordinateProfile φ)) T P| ≤
      absJetVariation r Ds.length*C*rho^Ds.length := by
  rw [T.disorderProfileJets_eq_allOffDiagonal hw φ A hA ho v q hq hq0 Ds hB hDs P x]
  have H := disorderOffDiagonalJets_moment_bound hw φ ho v q x
    (Ds.map (ReplicaTree.coordinateProfile φ))
    (by simpa only [List.length_map] using hk) hC hrho T hT P hP (by
      intro K hK j
      obtain ⟨D,hD,rfl⟩ := List.mem_map.mp hK
      simpa only [List.length_map] using hmoment D hD j)
  simpa only [List.length_map] using H

end OAI.SKFluctuations.Hierarchy.ClockTree
