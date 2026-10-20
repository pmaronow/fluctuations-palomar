module

public import ComparisonSignedCavityWholeLawZeroLowError
public import ComparisonSignedCavityWholeLawTaylorMoments

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
set_option maxHeartbeats 12000000

namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S ι : Type*} [Fintype S] [Fintype ι] [Nonempty S] [Nonempty ι]

theorem disorderProfileJets_two_kernel_cap_wholeLaw_L2
    {w : S→ℝ} (hw : ∀σ,0 < w σ) (φ : S→(ι→ℝ)→L[ℝ]ℝ)
    {as : List PositiveMass} (T : ClockTree S as) (ho : MassOrdered 0 as)
    (v : ι→ℝ) (q : ℕ→ι→ℝ) (x : ι→ℝ)
    {r : ℕ} (hT : T.leaves ≤ r) (P : T.Assignment→ℝ)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hP : T.disorderExpect w φ v q (fun σ=>P σ^2) x ≤ C^2)
    (E : ℕ→S→S→ℝ) {d : ℝ} (hdiag : ∀σ,E as.length σ σ=d)
    (hcap : ∀j,j ≤ as.length→∀σ τ,|E j σ τ| ≤ M)
    {D : ℕ→ℝ} (hD : ∀j,0 ≤ D j)
    (hsecond : ∀j,(pairClock as j).disorderExpect w φ v q
      (fun σ=>(E j (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2) :
    |disorderProfileJets w φ v q x [E,E] T P| ≤
      pairForkVariation r*pairForkVariation (r+2)*M*C*
        (T.forkCost D+edgeBudget 0 as D) := by
  let V:=pairForkVariation (r+2)*(M*C)
  have hV : 0 ≤ V:=mul_nonneg (pairForkVariation_nonneg _) (mul_nonneg hM hC)
  have Hrow (p : MarkedPlacement T) (hp : p∈T.markedAttach 0)
      (s : MarkedPlacement p.tree) (hs : s∈p.tree.markedAttach 0) :
      |disorderProfileJets w φ v q x [E] s.tree (profilePairTest P E p s)| ≤
        V*(s.tree.forkCost D+edgeBudget 0 as D) := by
    have hleaf : s.tree.leaves ≤ r+2 := by
      have h₁:=T.markedAttach_leaves 0 p hp
      have h₂:=p.tree.markedAttach_leaves 0 s hs
      omega
    have Hpull : s.tree.disorderExpect w φ v q
        (fun σ=>P (p.restrict (s.restrict σ))^2) x ≤ C^2 := by
      have H:=wholeLaw_double_marked_nat_moment_eq hw φ T ho v q x P 2 p hp s hs
      simp only [sq_abs] at H
      rw [H]
      exact hP
    have Hmoment : s.tree.disorderExpect w φ v q
        (fun σ=>profilePairTest P E p s σ^2) x ≤ (M*C)^2 := by
      have Hpoint (σ : s.tree.Assignment) :
          profilePairTest P E p s σ^2 ≤
            M^2*P (p.restrict (s.restrict σ))^2 := by
        have HE:=hcap (s.tree.splitIndex (s.embed p.mark) s.mark)
          (s.tree.splitIndex_le_clockLength _ _) (p.spin (s.restrict σ)) (s.spin σ)
        have HE2 : (E (s.tree.splitIndex (s.embed p.mark) s.mark)
            (p.spin (s.restrict σ)) (s.spin σ))^2 ≤ M^2 := by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) HE 2
        dsimp only [profilePairTest]
        rw [mul_pow,mul_comm]
        exact mul_le_mul_of_nonneg_right HE2 (sq_nonneg _)
      have Hbound : s.tree.disorderExpect w φ v q
          (fun σ=>profilePairTest P E p s σ^2) x ≤
          M^2*s.tree.disorderExpect w φ v q
            (fun σ=>P (p.restrict (s.restrict σ))^2) x := by
        unfold disorderExpect
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro σ _
        have HW:=(s.tree.disorderWeight_probability hw φ ho v q x).1 σ
        simpa only [mul_assoc,mul_left_comm,mul_comm] using
          mul_le_mul_of_nonneg_left (Hpoint σ) HW
      exact Hbound.trans (by simpa only [mul_pow] using
        mul_le_mul_of_nonneg_left Hpull (sq_nonneg M))
    have H:=s.tree.disorderProfileJets_oneError_offDiagonal_wholeLaw_L2 hw φ ho v q x
      hleaf (profilePairTest P E p s) (mul_nonneg hM hC) Hmoment E hdiag hD hsecond
    rw [edgeDensity_integral ho D] at H
    exact H
  have Hsum:=T.signedPair_abs_le_pairAbsSum
    (fun p s=>disorderProfileJets w φ v q x [E] s.tree (profilePairTest P E p s))
  have Hbudget:=T.pairAbsSum_forkBudget_le ho hT hD (d:=0) le_rfl
  simp only [add_zero] at Hbudget
  have Hbound : T.pairAbsSum (fun p s=>
      |disorderProfileJets w φ v q x [E] s.tree (profilePairTest P E p s)|) ≤
      V*(pairForkVariation r*(T.forkCost D+edgeBudget 0 as D)) := by
    calc
      _ ≤ T.pairAbsSum (fun _ s=>V*(s.tree.forkCost D+edgeBudget 0 as D)) :=
        T.pairAbsSum_mono Hrow
      _ = V*T.pairAbsSum (fun _ s=>s.tree.forkCost D+edgeBudget 0 as D) :=
        T.pairAbsSum_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left Hbudget hV
  have H:=Hsum.trans Hbound
  have Hnonneg : 0 ≤ V*(pairForkVariation r*(T.forkCost D+edgeBudget 0 as D)) :=
    mul_nonneg hV (mul_nonneg (pairForkVariation_nonneg _)
      (add_nonneg (T.forkCost_nonneg hD) (edgeBudget_nonneg ho hD)))
  change |_/2| ≤ _
  rw [abs_div,show |(2:ℝ)|=2 by norm_num]
  have Hhalf : |((T.markedAttach 0).map fun p=>p.coeff*
      ((p.tree.markedAttach 0).map fun s=>s.coeff*
        disorderProfileJets w φ v q x [E] s.tree (profilePairTest P E p s)).sum).sum|/2 ≤
      V*(pairForkVariation r*(T.forkCost D+edgeBudget 0 as D)) := by linarith
  calc
    _ ≤ V*(pairForkVariation r*(T.forkCost D+edgeBudget 0 as D)) := Hhalf
    _ = _ := by dsimp only [V]; ring

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem cutFrozenLowHighJet_two_high_wholeLaw_L2_bound
    (n : ℕ) (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (x : FullCoordinate n→ℝ)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    {r : ℕ} (hT : T.leaves ≤ r) {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hP : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 t b h K) (fun σ=>P σ^2) x ≤ C^2)
    (hcap : ∀j,j ≤ as.length→∀σ τ,
      |ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j σ τ| ≤ M)
    {D : ℕ→ℝ} (hD : ∀j,0 ≤ D j)
    (hsecond : ∀j,(pairClock as j).disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 t b h K)
      (fun σ=>(ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K) j
        (pairSpin as j σ).1 (pairSpin as j σ).2)^2) x ≤ (D j)^2) :
    |cutFrozenLowHighJet n q U b h K T P x 0 2 t| ≤
      pairForkVariation r*pairForkVariation (r+2)*M*C*
        (T.forkCost D+edgeBudget 0 as D) := by
  rw [cutFrozenLowHighJet_eq_profileJets n q U b h K T ho P x
    hq0 hq hb hh hK hbm hhm hKm 0 2 ht]
  simpa only [List.replicate_succ,List.replicate_zero,List.nil_append] using
    T.disorderProfileJets_two_kernel_cap_wholeLaw_L2 (fullWeight_pos n) (fullFeature n) ho
      0 (cutFullVariance n q U 0 t b h K) x hT P hC hM hP
      (ReplicaTree.coordinateProfile (fullFeature n) (cutTSlope n U 0 b h K))
      (fun σ=>fullFeature_coordinateProfile_self n (cutTSlope n U 0 b h K) as.length σ)
      hcap hD hsecond

end OAI.SKFluctuations.Cavity
