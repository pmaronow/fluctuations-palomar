module

public import ComparisonActualHighWallThetaZeroEq7FiniteMaskDefs

@[expose] public section

noncomputable section
namespace OAI.SKFluctuations.LaplaceWindowFormalization
open Set Filter MeasureTheory Hierarchy WholeUnitSideKernel
open scoped Topology NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
attribute [local instance] Classical.propDecidable

namespace ActualThetaZeroOverlapMinimum
variable {n : ℕ} {m delta cl cu Az C0 Ct D Bclock : ℝ}
variable {Q : ActualThetaZeroOverlapMinimum (n+1) m delta cl cu Az C0 Ct D Bclock}

theorem eq7_inner_low_dyad_card_le_six (h : ℝ) :
    Fintype.card (Eq7InnerLowDyad Q h) ≤ 6 := by
  classical
  let U := comparisonSmallMass Q.data.N Q.data.E
  let s := Q.data.s
  by_cases hUs : U ≤ s
  · obtain ⟨k, hklo, hkhi⟩ :=
      comparison_mass_dyadic_cover Q.data.hU hUs Q.data.hs1
    let kn : ℕ := k.val
    have hscale (a b : ℕ) (hab : a ≤ b) :
        U*(2:ℝ)^a ≤ U*(2:ℝ)^b :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hab)
        Q.data.hU.le
    have hwindow (j : Eq7InnerLowDyad Q h) :
        kn ≤ (j.val.val : ℕ)+4 ∧ (j.val.val : ℕ) ≤ kn+1 := by
      let jn : ℕ := (j.val.val : ℕ)
      have hjpos : 0 < U*(2:ℝ)^jn := by
        exact mul_pos Q.data.hU (pow_pos (by norm_num) _)
      have hjup : U*(2:ℝ)^jn ≤ 2*s := by
        simpa only [U,s,jn,eq7InnerDyadMass] using j.property.2.1
      have hjlo : s ≤ 16*(U*(2:ℝ)^jn) := by
        have H := j.property.2.2
        change s ≤ min (16*(U*(2:ℝ)^jn)) 1 at H
        exact H.trans (min_le_left _ _)
      have hklo' : U*(2:ℝ)^kn ≤ s := by
        simpa only [U,s,kn,eq7InnerDyadMass] using hklo
      have hkhi' : s < 2*(U*(2:ℝ)^kn) := by
        simpa only [U,s,kn,eq7InnerDyadMass] using hkhi
      constructor
      · by_contra hn
        have hgap : jn+5 ≤ kn := by omega
        have H := hscale (jn+5) kn hgap
        have Hfive : 32*(U*(2:ℝ)^jn) ≤ U*(2:ℝ)^kn := by
          calc
            _ = U*(2:ℝ)^(jn+5) := by rw [pow_add]; norm_num; ring
            _ ≤ _ := H
        nlinarith only [Hfive,hklo',hjlo,hjpos]
      · by_contra hn
        have hgap : kn+2 ≤ jn := by omega
        have H := hscale (kn+2) jn hgap
        have Htwo : 4*(U*(2:ℝ)^kn) ≤ U*(2:ℝ)^jn := by
          calc
            _ = U*(2:ℝ)^(kn+2) := by rw [pow_add]; norm_num; ring
            _ ≤ _ := H
        nlinarith only [Htwo,hkhi',hjup]
    let f : Eq7InnerLowDyad Q h → Fin 6 := fun j =>
      ⟨kn+1-(j.val.val : ℕ), by have H := hwindow j; omega⟩
    have hf : Function.Injective f := by
      intro a b hab
      have ha := (hwindow a).2
      have hb := (hwindow b).2
      have heq : kn+1-(a.val.val : ℕ)=kn+1-(b.val.val : ℕ) :=
        congrArg Fin.val hab
      have hnat : (a.val.val : ℕ)=(b.val.val : ℕ) := by omega
      exact Subtype.ext (Subtype.ext (Subtype.ext hnat))
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  · let f : Eq7InnerLowDyad Q h → Fin 6 := fun j =>
      False.elim (hUs j.property.1)
    have hf : Function.Injective f := by
      intro a b hab
      exact False.elim (hUs a.property.1)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf

end ActualThetaZeroOverlapMinimum
end OAI.SKFluctuations.LaplaceWindowFormalization
