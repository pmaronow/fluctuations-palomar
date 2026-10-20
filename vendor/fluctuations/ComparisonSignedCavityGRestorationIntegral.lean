module

public import ComparisonSignedCavityGWordRestorationCanonical
public import ComparisonSignedCavityActualHighErrorProfile

@[expose] public section

noncomputable section
set_option maxHeartbeats 12000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem native_actual_law_restoration_abs_le (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ)
    (Bhigh Blow : ℝ)
    (hHigh : ∀t∈Icc (0:ℝ) 1,|cutMixedJet n q U b h K T P 0 0 0 t| ≤ Bhigh)
    (hLow : ∀l∈Icc (0:ℝ) 1,|cutLowJet n q U b h K T P 0 1 l 1| ≤ Blow) :
    |nativeActualLawRestorationRemainder n q U b h K T P| ≤ Bhigh+Blow := by
  have HH:=intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (C:=Bhigh) (fun t ht=>by
      rw [Real.norm_eq_abs]
      have ht' : t∈Ioc (0:ℝ) 1:=by simpa only [uIoc_of_le zero_le_one] using ht
      exact hHigh t ⟨ht'.1.le,ht'.2⟩)
  have HL:=intervalIntegral.norm_integral_le_of_norm_le_const
    (a:=(0:ℝ)) (b:=1) (C:=Blow) (fun l hl=>by
      rw [Real.norm_eq_abs]
      have hl' : l∈Ioc (0:ℝ) 1:=by simpa only [uIoc_of_le zero_le_one] using hl
      exact hLow l ⟨hl'.1.le,hl'.2⟩)
  simp only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] at HH HL
  exact (abs_add_le _ _).trans (add_le_add HH HL)

theorem native_actual_law_restoration_zero_test (n : ℕ)
    (q : ℕ→RestCoordinate n→ℝ) (U : ℕ) (b h K : ℕ→ℝ)
    {as : List PositiveMass} (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (hP : ∀σ,P σ=0)
    (hq0 : ∀j i,0 ≤ q j i) (hq : ∀i,Monotone (fun j=>q j i))
    (hb : ∀j,0 ≤ b j) (hh : ∀j,0 ≤ h j) (hK : ∀j,0 ≤ K j)
    (hbm : Monotone b) (hhm : Monotone h) (hKm : Monotone K) :
    nativeActualLawRestorationRemainder n q U b h K T P=0 := by
  have H:=actual_original_law_eq_decoupled_add_restoration n q U b h K T ho P
    hq0 hq hb hh hK hbm hhm hKm
  have Hfull : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 1 1 b h K) P 0=0:=by
    simp only [ClockTree.disorderExpect,hP,mul_zero,Finset.sum_const_zero]
  have Hzero : T.disorderExpect (fullWeight n) (fullFeature n) 0
      (cutFullVariance n q U 0 0 b h K) P 0=0:=by
    simp only [ClockTree.disorderExpect,hP,mul_zero,Finset.sum_const_zero]
  rw [Hfull,Hzero,zero_add] at H
  exact H.symm

theorem NativeOriginalGMarkedWord.originalRestorationTest_diagonal_zero
    {n : ℕ} {as : List PositiveMass} {T : ClockTree (Spin n×Bool) as}
    (g : NativeOriginalGMarkedWord T) (U : ℕ) (K b S : ℕ→ℝ)
    (P : T.Assignment→ℝ) (a : T.Slot) (hdiag : g.z.embed g.r.mark=g.z.mark)
    (σ : g.tree.Assignment) : g.originalRestorationTest U K b S P a σ=0 := by
  unfold NativeOriginalGMarkedWord.originalRestorationTest nativeOriginalHighGAtom
  split_ifs with hsupport
  · exact False.elim (hsupport.2.2.2 hdiag)
  · exact mul_zero _

end OAI.SKFluctuations.Cavity
