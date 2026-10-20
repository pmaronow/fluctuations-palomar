module

public import CavityNativeSignedProjectedReplacement
public import CavityPhysicalWeightedExterior

@[expose] public section

noncomputable section
set_option maxHeartbeats 1500000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal RealInnerProductSpace
namespace OAI.SKFluctuations.Cavity
open Hierarchy

theorem deleted_overlap_join_eq_scaled (n : ℕ) (σ τ : Spin n) (b c : Bool) :
    deletedOverlap n (joinSpin (σ,b)) (joinSpin (τ,c))=
      ((n:ℝ)/(n+1 : ℕ))*orderedOverlap n σ τ := by
  simp only [deletedOverlap,joinSpin_old,orderedOverlap]
  by_cases hn : n=0
  · subst n
    simp
  · have hn' : (n:ℝ)≠0 := by exact_mod_cast hn
    field_simp

def nativeWeightedExteriorAnchor (n : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  ((n:ℝ)/(n+1 : ℕ)) • ∑ σ,
    (E.weight (restWeight n) (restFeature n) q σ x*H σ) •
      WithLp.toLp 2 (normalizedSpin n (E.atSlot σ s))

theorem native_weighted_target_difference (n : ℕ) {as : List PositiveMass}
    (E U : ClockTree (Spin n) as) (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ)
    (Z : U.Assignment → ℝ) (old new : U.Assignment → Spin n) :
    (E.fork U).expect (restWeight n) (restFeature n) q (fun σ=>Z σ.2*H σ.1*
      (deletedOverlap n (joinSpin (old σ.2,false)) (joinSpin (E.atSlot σ.1 s,false))-
        deletedOverlap n (joinSpin (new σ.2,false)) (joinSpin (E.atSlot σ.1 s,false)))) x=
    U.expect (restWeight n) (restFeature n) q (fun σ=>Z σ*inner ℝ
      (WithLp.toLp 2 (normalizedSpin n (old σ))-
        WithLp.toLp 2 (normalizedSpin n (new σ)))
      (nativeWeightedExteriorAnchor n E H s q x)) x := by
  simp_rw [deleted_overlap_join_eq_scaled]
  rw [ClockTree.expect_fork]
  unfold ClockTree.expect nativeWeightedExteriorAnchor
  simp only [inner_smul_right,inner_sum,inner_sub_left,normalizedSpin_inner_eq_overlap,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  apply Finset.sum_congr rfl
  intro τ _
  ring

theorem native_weighted_exterior_anchor_moment (n l : ℕ) {as : List PositiveMass}
    (E : ClockTree (Spin n) as) {a : ℝ} (ho : MassOrdered a as)
    (H : E.Assignment → ℝ) (s : E.Slot)
    (q : ℕ → RestCoordinate n → ℝ≥0) (x : RestCoordinate n → ℝ) :
    ‖nativeWeightedExteriorAnchor n E H s q x‖^(4*l)≤
      E.expect (restWeight n) (restFeature n) q (fun σ=>|H σ|^(4*l)) x*
        (E.fork E).expect (restWeight n) (restFeature n) q (fun σ=>
          |deletedOverlap n (joinSpin (E.atSlot σ.1 s,false))
            (joinSpin (E.atSlot σ.2 s,false))|^(2*l)) x := by
  let c : ℝ := (n:ℝ)/(n+1 : ℕ)
  have hc0 : 0 ≤ c := by dsimp only [c]; positivity
  have hc1 : c≤1 := by
    dsimp only [c]
    apply (div_le_one (by positivity : (0:ℝ)<(n+1 : ℕ))).2
    exact_mod_cast Nat.le_succ n
  let w := fun σ=>E.weight (restWeight n) (restFeature n) q σ x
  let y := fun σ:E.Assignment=>WithLp.toLp 2 (normalizedSpin n (E.atSlot σ s))
  have hw := E.weight_probability (restWeight_pos n) (restFeature n) ho q x
  have he := finite_weighted_vector_even w H y hw.1 hw.2 l
  have hpow := mul_le_mul_of_nonneg_left he (pow_nonneg hc0 (4*l))
  have hn : ‖nativeWeightedExteriorAnchor n E H s q x‖^(4*l)=
      c^(4*l)*‖∑ σ, (w σ*H σ) • y σ‖^(4*l) := by
    simp only [nativeWeightedExteriorAnchor,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg hc0,mul_pow,c,w,y]
  rw [←hn] at hpow
  have hcp : c^(4*l)≤c^(2*l) := by
    have hcl : c^(2*l)≤1 := pow_le_one₀ hc0 hc1
    calc
      c^(4*l)=(c^(2*l))^2 := by rw [←pow_mul]; congr 1; omega
      _ ≤ c^(2*l) := by nlinarith [pow_nonneg hc0 (2*l)]
  have hH0 : 0 ≤ ∑ σ, w σ*|H σ|^(4*l) :=
    Finset.sum_nonneg fun σ _=>mul_nonneg (hw.1 σ) (by positivity)
  have hR0 : 0 ≤ ∑ z:E.Assignment×E.Assignment,
      w z.1*w z.2*|inner ℝ (y z.1) (y z.2)|^(2*l) :=
    Finset.sum_nonneg fun z _=>mul_nonneg (mul_nonneg (hw.1 _) (hw.1 _)) (by positivity)
  apply hpow.trans
  apply (mul_le_mul_of_nonneg_right hcp (mul_nonneg hH0 hR0)).trans_eq
  have hc0' : 0 ≤ (n:ℝ)/(n+1 : ℕ) := hc0
  simp only [deleted_overlap_join_eq_scaled,abs_mul,abs_of_nonneg hc0',mul_pow]
  unfold ClockTree.expect
  simp only [ClockTree.weight_fork,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  dsimp only [w,y,c]
  rw [normalizedSpin_inner_eq_overlap]
  ring

end OAI.SKFluctuations.Cavity
