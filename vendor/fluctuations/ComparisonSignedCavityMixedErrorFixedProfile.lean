module

public import ComparisonSignedCavityMixedErrorPairProduct
public import ComparisonSignedCavityWholeLawZeroLowError

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

theorem disorderProfileJets_fixedLow_highError_wholeLaw_product_bound
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ] ℝ)
    {as : List PositiveMass} (ho : MassOrdered 0 as) (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    (T : ClockTree S as) {r : ℕ} (hT : T.leaves ≤ r)
    (P : T.Assignment→ℝ) {C p Mlow Mhigh dlow : ℝ}
    (hC : 0 ≤ C) (hp : 2 < p) (hMlow : 0 ≤ Mlow) (hMhigh : 0 ≤ Mhigh) (hdlow : 0 ≤ dlow)
    (hP : T.disorderExpect w φ v q (fun σ=>|P σ|^(2*(p/(p-2)))) x ≤ C^(2*(p/(p-2))))
    (A : S→S→ℝ) (u z : T.Slot) (huz : u≠z) (hA : ∀σ τ,|A σ τ| ≤ Mlow)
    (hsecondLow : (pairClock as (T.splitIndex u z)).disorderExpect w φ v q
      (fun σ=>(A (pairSpin as (T.splitIndex u z) σ).1 (pairSpin as (T.splitIndex u z) σ).2)^2) x ≤ dlow^2)
    (B : ℕ→S→S→ℝ) {diag : ℝ} (hdiag : ∀σ,B as.length σ σ=diag)
    (hB : ∀j σ τ,|B j σ τ| ≤ Mhigh)
    (Dhigh : ℕ→ℝ) (hDhigh : ∀j,0 ≤ Dhigh j)
    (hsecondHigh : ∀j,(pairClock as j).disorderExpect w φ v q
      (fun σ=>(B j (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (Dhigh j)^2) :
    |disorderProfileJets w φ v q x [B] T (fun σ=>P σ*A (T.atSlot σ u) (T.atSlot σ z))| ≤
      pairForkVariation r*C*Mlow^((p-2)/p)*Mhigh^((p-2)/p)*dlow^(2/p)*
        (T.forkCost (fun j=>(Dhigh j)^(2/p))+
          (∫s,edgeDensity 0 as (fun j=>(Dhigh j)^(2/p)) s)) := by
  classical
  let e:=(2:ℝ)/p
  let V:=C*Mlow^((p-2)/p)*Mhigh^((p-2)/p)*dlow^e
  let D:=fun j=>(Dhigh j)^e
  let J:=fun σ=>P σ*A (T.atSlot σ u) (T.atSlot σ z)
  have hV : 0 ≤ V:=by dsimp [V];positivity
  have hD j : 0 ≤ D j:=Real.rpow_nonneg (hDhigh j) _
  rw [T.disorderProfileJets_one_eq_offDiagonal hw φ ho v q J hdiag x]
  have H:=T.signedPair_abs_le_pairAbsSum
    (fun b c=>(1-c.hit b.mark)*c.tree.disorderExpect w φ v q (profilePairTest J B b c) x)
  have HB : T.pairAbsSum (fun b c=>|(1-c.hit b.mark)*
      c.tree.disorderExpect w φ v q (profilePairTest J B b c) x|) ≤
      V*T.pairAbsSum (fun _ c=>c.tree.forkCost D+edgeBudget 0 as D) := by
    rw [←T.pairAbsSum_const_mul]
    apply T.pairAbsSum_mono
    intro b hb c hc
    by_cases heq : c.mark=c.embed b.mark
    · simp only [MarkedPlacement.hit,ite_eq_left heq,sub_self,zero_mul,abs_zero]
      exact mul_nonneg hV (add_nonneg (c.tree.forkCost_nonneg hD) (edgeBudget_nonneg ho hD))
    · simp only [MarkedPlacement.hit,ite_eq_right heq,sub_zero,one_mul]
      let un:=c.embed (b.embed u)
      let zn:=c.embed (b.embed z)
      let j:=c.tree.splitIndex (c.embed b.mark) c.mark
      let Pn:=fun σ=>P (b.restrict (c.restrict σ))
      have hbEmb:=T.markedAttach_embed_preserves 0 b hb
      have hcEmb:=b.tree.markedAttach_embed_preserves 0 c hc
      have hneLow : un≠zn:=fun H=>huz (hbEmb.1 (hcEmb.1 H))
      have hsplit : c.tree.splitIndex un zn=T.splitIndex u z:=
        (hcEmb.2 _ _).trans (hbEmb.2 _ _)
      have HPn : c.tree.disorderExpect w φ v q (fun σ=>|Pn σ|^(2*(p/(p-2)))) x ≤ C^(2*(p/(p-2))) := by
        change c.tree.disorderExpect w φ v q (fun σ=>|P (b.restrict (c.restrict σ))|^(2*(p/(p-2)))) x ≤ _
        rw [wholeLaw_double_marked_moment_eq hw φ T ho v q x P _ b hb c hc]
        exact hP
      have HP:=c.tree.disorderExpect_mixedError_wholeLaw_product_budget hw φ ho v q x Pn
        hC hp hMlow hMhigh hdlow (hDhigh j) HPn
        A (B j) un zn (c.embed b.mark) c.mark hneLow (Ne.symm heq) hA (hB j)
        (by rw [hsplit];exact hsecondLow) (hsecondHigh j)
        (a:=0) Fin.elim0 Fin.elim0 Fin.elim0 (fun i=>Fin.elim0 i) Fin.elim0
        (fun i=>Fin.elim0 i) (fun i=>Fin.elim0 i)
      have heqTest : profilePairTest J B b c=
          fun σ=>Pn σ*(A (c.tree.atSlot σ un) (c.tree.atSlot σ zn)*
            B j (c.tree.atSlot σ (c.embed b.mark)) (c.tree.atSlot σ c.mark)*(∏i : Fin 0,Fin.elim0 i)) := by
        funext σ
        simp only [profilePairTest,J,Pn,un,zn,j,b.restrict_at,c.restrict_at,b.spin_at,c.spin_at,Fin.prod_univ_zero,mul_one]
        ring
      have Hpair : |c.tree.disorderExpect w φ v q (profilePairTest J B b c) x| ≤ V*D j := by
        rw [heqTest]
        simpa only [Fin.prod_univ_zero,mul_one,V,D,e,mul_assoc] using HP
      apply Hpair.trans
      apply mul_le_mul_of_nonneg_left _ hV
      exact (c.tree.split_le_forkCost hD _ _ (Ne.symm heq)).trans
        (le_add_of_nonneg_right (edgeBudget_nonneg ho hD))
  have HG:=T.pairAbsSum_forkBudget_le ho hT hD (d:=0) le_rfl
  simp only [add_zero] at HG
  have HF:=(H.trans HB).trans (mul_le_mul_of_nonneg_left HG hV)
  rw [edgeDensity_integral ho D]
  unfold disorderOffDiagonalProfileJet
  change |_/2| ≤ _
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  have hn : 0 ≤ pairForkVariation r*V*(T.forkCost D+edgeBudget 0 as D):=
    mul_nonneg (mul_nonneg (pairForkVariation_nonneg _) hV)
      (add_nonneg (T.forkCost_nonneg hD) (edgeBudget_nonneg ho hD))
  have HF':=HF
  rw [mul_left_comm V] at HF'
  dsimp only [V,D,e] at HF' hn ⊢
  simp only [mul_assoc] at HF' hn ⊢
  linarith

end OAI.SKFluctuations.Hierarchy.ClockTree
