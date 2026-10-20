module

public import CavityAttachedTree

@[expose] public section

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Cavity
open Hierarchy

 theorem deleted_overlap_power_le (n m : ℕ) (σ τ : Spin (n+1)) (S : ℝ) :
    |deletedOverlap n σ τ-S|^m ≤ (2:ℝ)^(m-1)*
      (|orderedOverlap (n+1) σ τ-S|^m+(1/(n+1:ℕ):ℝ)^m) := by
  have h : |deletedOverlap n σ τ-S| ≤ |orderedOverlap (n+1) σ τ-S|+1/(n+1:ℕ) := by
    calc _ = |(orderedOverlap (n+1) σ τ-S)+(deletedOverlap n σ τ-orderedOverlap (n+1) σ τ)| := by congr 1; ring
         _ ≤ |orderedOverlap (n+1) σ τ-S|+|deletedOverlap n σ τ-orderedOverlap (n+1) σ τ| := abs_add_le _ _
         _ = _ := by rw [abs_deletedOverlap_sub]
  exact (pow_le_pow_left₀ (abs_nonneg _) h m).trans
    (add_pow_le (abs_nonneg _) (by positivity : (0:ℝ) ≤ 1/(n+1:ℕ)) m)

 theorem disorder_deleted_overlap_power_le (n m : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    (v : FullCoordinate n → ℝ) (q : ℕ → FullCoordinate n → ℝ) (x : FullCoordinate n → ℝ)
    (s t : T.Slot) (S : ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ => |deletedOverlap n (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))-S|^m) x ≤
    (2:ℝ)^(m-1)*(T.disorderExpect (fullWeight n) (fullFeature n) v q
      (fun σ => |orderedOverlap (n+1) (joinSpin (T.atSlot σ s))
        (joinSpin (T.atSlot σ t))-S|^m) x+(1/(n+1:ℕ):ℝ)^m) := by
  let w := fun σ => T.disorderWeight (fullWeight n) (fullFeature n) v q σ x
  have hw := (T.disorderWeight_probability (fullWeight_pos n) (fullFeature n) ho v q x)
  have hsum := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left
      (deleted_overlap_power_le n m (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t)) S) (hw.1 σ))
  change (∑ σ, w σ*_) ≤ _
  calc _ ≤ ∑ σ, w σ*((2:ℝ)^(m-1)*
      (|orderedOverlap (n+1) (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ t))-S|^m+
        (1/(n+1:ℕ):ℝ)^m)) := hsum
       _ = _ := by
        let F := fun σ => |orderedOverlap (n+1) (joinSpin (T.atSlot σ s))
          (joinSpin (T.atSlot σ t))-S|^m
        change (∑ σ, w σ*((2:ℝ)^(m-1)*(F σ+(1/(n+1:ℕ):ℝ)^m))) =
          (2:ℝ)^(m-1)*((∑ σ, w σ*F σ)+(1/(n+1:ℕ):ℝ)^m)
        calc
          _ = (2:ℝ)^(m-1)*((∑ σ, w σ*F σ)+(1/(n+1:ℕ):ℝ)^m*(∑ σ, w σ)) := by
            simp only [mul_add,Finset.mul_sum,← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro σ _
            ring
          _ = _ := by rw [show ∑ σ, w σ = 1 from hw.2,mul_one]

theorem cavityPath_deleted_moment_le_endpoint (n m U : ℕ) {as : List PositiveMass}
    (T : ClockTree (Spin n × Bool) as) (ho : MassOrdered 0 as)
    {l t : ℝ} (hl : l ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1)
    {q : ℕ → RestCoordinate n → ℝ} {b h K : ℕ → ℝ}
    (hq : ∀ i, Monotone (fun j => q j i)) (hb : Monotone b) (hh : Monotone h) (hK : Monotone K)
    (hq0 : ∀ j i, 0 ≤ q j i) (hb0 : ∀ j, 0 ≤ b j) (hh0 : ∀ j, 0 ≤ h j) (hK0 : ∀ j, 0 ≤ K j)
    (s r : T.Slot) (S : ℝ) (x : FullCoordinate n → ℝ) :
    T.disorderExpect (fullWeight n) (fullFeature n) 0 (cavityPath n U l t q b h K)
      (fun σ => |deletedOverlap n (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ r))-S|^m) x ≤
    Real.exp (2*(7*(T.leaves:ℝ)+8*(T.leaves:ℝ)^2*(T.leaves+1:ℝ))*
      (K as.length+b as.length+h as.length))*(2:ℝ)^(m-1)*
      (T.disorderExpect (fullWeight n) (fullFeature n) 0 (cavityPath n U 1 1 q b h K)
        (fun σ => |orderedOverlap (n+1) (joinSpin (T.atSlot σ s))
          (joinSpin (T.atSlot σ r))-S|^m) x+(1/(n+1:ℕ):ℝ)^m) := by
  have H := cavityPath_expect_close n U T ho hl ht (by norm_num : (1:ℝ) ∈ Icc 0 1)
    (by norm_num : (1:ℝ) ∈ Icc 0 1) hq hb hh hK hq0 hb0 hh0 hK0
    (fun σ => |deletedOverlap n (joinSpin (T.atSlot σ s)) (joinSpin (T.atSlot σ r))-S|^m)
    (fun σ => pow_nonneg (abs_nonneg _) _) x
  apply H.le_mul.trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (disorder_deleted_overlap_power_le n m T ho 0 (cavityPath n U 1 1 q b h K) x s r S)
    (Real.exp_pos _).le

end OAI.SKFluctuations.Cavity
