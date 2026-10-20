module

public import ComparisonSignedCavityLowGammaHighTaylor

@[expose] public section

noncomputable section
set_option maxHeartbeats 15000000
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy LaplaceWindowFormalization
open scoped Topology NNReal ENNReal BigOperators

theorem native_low_rest_only_first_derivative_zero (n : ℕ) (q : ℕ→RestCoordinate n→ℝ)
    (U : ℕ) (b h K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.cavityLeft.Assignment→ℝ)
    (hq0 : ∀ j i,0 ≤ q j i) (hq : ∀ i,Monotone (fun j=>q j i))
    (hb : ∀ j,0 ≤ b j) (hh : ∀ j,0 ≤ h j) (hK : ∀ j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K)
    (hU : U ≤ as.length) :
    cutLowJet n q U b h K T (fun σ=>P (T.cavityAssignment σ).1) 0 1 0 1=0 := by
  classical
  let J:=fun σ=>P (T.cavityAssignment σ).1
  let A:=siteRestKernel n (restLowKernel n U b h)
  let law:=cutFullVariance n q U 0 1 b h K
  rw [cutLowJet_eq_profileJets n q U b h K T ho _ 0 hq0 hq hb hh hK hbm hhm hKm
    1 (by norm_num) (by norm_num)]
  simp only [List.replicate_one]
  rw [←siteRestKernel_eq_cut_low]
  have Hdiag : ∀σ,A as.length σ σ=(0:ℝ) := by
    intro σ
    simp only [A,siteRestKernel,restLowKernel,not_lt.mpr hU,ite_false,mul_zero]
  rw [T.disorderProfileJets_one_eq_offDiagonal (fullWeight_pos n) (fullFeature n) ho 0 law J Hdiag 0]
  unfold ClockTree.disorderOffDiagonalProfileJet
  rw [div_eq_zero_iff]
  left
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨p,hp,rfl⟩:=List.mem_map.mp hx
  rw [mul_eq_zero]
  right
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨r,hr,rfl⟩:=List.mem_map.mp hy
  have HE : r.tree.disorderExpect (fullWeight n) (fullFeature n) 0 law
      (ClockTree.profilePairTest J A p r) 0=0 := by
    let c:=r.embed p.mark
    let d:=r.mark
    let j:=r.tree.splitIndex c d
    by_cases hj : j<U
    · have Hdegree : Odd (blockDegree r.tree U c [c,d]) := by
        have Hself : U ≤ r.tree.splitIndex c c:=by rw [r.tree.splitIndex_self];exact hU
        simpa only [blockDegree,Hself,ite_true,show ¬U ≤ r.tree.splitIndex c d from not_le.mpr hj,
          ite_false,Nat.add_zero] using (show Odd 1 by decide)
      have Hodd:=cutDisorderExpect_graph_odd n q U (by omega : 0<U) 1 b h K r.tree hU c [c,d]
        Hdegree (insertedRestTest P (restLowKernel n U b h) p r) 0 (by intro i;rfl) (by intro i;rfl)
      have Htest : ClockTree.profilePairTest J A p r=
          fun σ=>insertedRestTest P (restLowKernel n U b h) p r (r.tree.cavityAssignment σ).1*
            siteMonomial r.tree σ [c,d] := by
        funext σ
        simp only [ClockTree.profilePairTest,J,A,siteRestKernel,insertedRestTest,siteMonomial,
          ClockTree.MarkedPlacement.restSpin,p.spin_at,r.spin_at,r.restrict_at,
          r.restRestrict_actual,p.restRestrict_actual,r.restRestrict_at,r.tree.atSlot_cavityLeft,c,d]
        ring
      rw [Htest]
      exact Hodd
    · have Htest : ClockTree.profilePairTest J A p r=fun _=>0 := by
        funext σ
        simp only [ClockTree.profilePairTest,A,siteRestKernel,restLowKernel,
          show ¬r.tree.splitIndex (r.embed p.mark) r.mark<U from hj,ite_false,mul_zero]
      rw [Htest]
      simp only [ClockTree.disorderExpect,mul_zero,Finset.sum_const_zero]
  rw [HE,mul_zero]

end OAI.SKFluctuations.Cavity
