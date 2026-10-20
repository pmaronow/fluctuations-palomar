module

public import ComparisonSignedCavityGeneratedBaseFactorization

@[expose] public section

noncomputable section
set_option maxHeartbeats 10000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {S B : Type} {as : List PositiveMass}

theorem native_generated_low_slot_ne_target {T : ClockTree (S×B) as}
    (P : NativeGeneratedTest T) {star : ℕ} (hlen : star < as.length)
    (c : T.Slot) (hc : T.splitIndex P.target c ≤ star) : c≠P.target := by
  intro h
  rw [h,T.splitIndex_self] at hc
  omega

theorem native_rest_generated_exterior_replace {T : ClockTree (S×B) as}
    (P : NativeGeneratedTest T) {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hlen : star < as.length) (R : S→S→ℝ) (C : ℕ→ℝ)
    (σ : T.cavityLeft.Assignment) (u : S) :
    nativeRestGeneratedExteriorValue T P R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) σ u)=
      nativeRestGeneratedExteriorValue T P R C σ := by
  unfold nativeRestGeneratedExteriorValue
  apply congrArg List.prod
  apply List.map_congr_left
  intro e he
  have H:=hP.exterior_departure e he
  have h₁ := native_generated_low_slot_ne_target P hlen e.1 H.1
  have h₂ := native_generated_low_slot_ne_target P hlen e.2 H.2
  have hc₁ : T.cavityLeftSlot e.1≠T.cavityLeftSlot P.target :=
    fun h=>h₁ (T.cavityLeftSlot.injective h)
  have hc₂ : T.cavityLeftSlot e.2≠T.cavityLeftSlot P.target :=
    fun h=>h₂ (T.cavityLeftSlot.injective h)
  simp only [nativeReplaceAtSlot_at,ite_eq_right hc₁,ite_eq_right hc₂]

theorem native_rest_generated_incoming_replace_sub {T : ClockTree (S×B) as}
    (P : NativeGeneratedTest T) {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (hi : i ≤ star) (hlen : star < as.length) (R : S→S→ℝ) (C : ℕ→ℝ)
    (σ : T.cavityLeft.Assignment) (u : S) :
    nativeRestGeneratedIncomingValue T P R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) σ u)-
        nativeRestGeneratedIncomingValue T P R C σ=
      (P.incoming.map (fun c=>R u (T.cavityLeft.atSlot σ (T.cavityLeftSlot c))-
        R (T.cavityLeft.atSlot σ (T.cavityLeftSlot P.target))
          (T.cavityLeft.atSlot σ (T.cavityLeftSlot c)))).sum := by
  have hlenI:=hP.incoming_degree
  have hread (c : T.Slot) (hc : c∈P.incoming) :
      T.cavityLeft.atSlot
        (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) σ u) (T.cavityLeftSlot c)=
          T.cavityLeft.atSlot σ (T.cavityLeftSlot c) := by
    have hcut : T.splitIndex P.target c≤ star := by
      rcases hP.incoming_cuts c hc with h|h <;> omega
    have hn:=native_generated_low_slot_ne_target P hlen c hcut
    rw [nativeReplaceAtSlot_at,ite_eq_right (fun h=>hn (T.cavityLeftSlot.injective h))]
  unfold nativeRestGeneratedIncomingValue
  cases he : P.incoming with
  | nil=>simp
  | cons c cs=>
    have hcs : cs=[] := by
      rw [he,List.length_cons] at hlenI
      exact List.length_eq_zero_iff.mp (by omega)
    subst cs
    have hc : c∈P.incoming := by simp [he]
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
      List.sum_cons,List.sum_nil,add_zero]
    rw [hread c hc,nativeReplaceAtSlot_at,ite_eq_left rfl]
    ring

theorem native_rest_generated_reset_replace_sub {T : ClockTree (S×B) as}
    (P : NativeGeneratedTest T) {i star : ℕ} (hP : NativeGeneratedTestAncestry i star P)
    (ht : P.teeth=[]) (hi : i≤ star) (hlen : star<as.length)
    (R : S→S→ℝ) (C : ℕ→ℝ) (σ : T.cavityLeft.Assignment) (u : S) :
    nativeRestGeneratedTestValue T P R C
      (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) σ u)-
        nativeRestGeneratedTestValue T P R C σ=
      nativeRestGeneratedExteriorValue T P R C σ*
        (P.incoming.map (fun c=>R u (T.cavityLeft.atSlot σ (T.cavityLeftSlot c))-
          R (T.cavityLeft.atSlot σ (T.cavityLeftSlot P.target))
            (T.cavityLeft.atSlot σ (T.cavityLeftSlot c)))).sum := by
  rw [native_rest_generated_reset_value P ht,native_rest_generated_reset_value P ht,
    native_rest_generated_exterior_replace P hP hlen,←mul_sub,
    native_rest_generated_incoming_replace_sub P hP hi hlen]

end OAI.SKFluctuations.Hierarchy.ClockTree

namespace OAI.SKFluctuations.Cavity
open Hierarchy Hierarchy.ClockTree

theorem native_paired_power_difference_algebra (d : ℕ) (s t A B : ℝ) :
    (t-s)*(B*t^d-A*s^d)=
      (t-s)*(B-A)*t^d+
        ∑j∈Finset.range d,(t-s)^2*A*(s^j*t^(d-1-j)) := by
  rw [←Finset.mul_sum]
  have H:=geom_sum₂_mul s t d
  calc
    _ = (t-s)*(B-A)*t^d+(t-s)*A*(t^d-s^d) := by ring
    _ = _ := by rw [show t^d-s^d= -(s^d-t^d) by ring,←H];ring

theorem native_reset_paired_projection_allocation {S B : Type} {as : List PositiveMass}
    {T : ClockTree (S×B) as} (P : NativeGeneratedTest T) {i star : ℕ}
    (hP : NativeGeneratedTestAncestry i star P) (ht : P.teeth=[])
    (hi : i≤ star) (hlen : star<as.length) (d : ℕ)
    (R : S→S→ℝ) (C : ℕ→ℝ) (Y : S→ℝ)
    (σ : T.cavityLeft.Assignment) (u : S) :
    let s:=T.cavityLeft.atSlot σ (T.cavityLeftSlot P.target)
    let Δ:=Y u-Y s
    Δ*(nativeRestGeneratedTestValue T P R C
        (nativeReplaceAtSlot T.cavityLeft (T.cavityLeftSlot P.target) σ u)*Y u^d-
      nativeRestGeneratedTestValue T P R C σ*Y s^d)=
    Δ*nativeRestGeneratedExteriorValue T P R C σ*
      (P.incoming.map (fun c=>R u (T.cavityLeft.atSlot σ (T.cavityLeftSlot c))-
        R s (T.cavityLeft.atSlot σ (T.cavityLeftSlot c)))).sum*Y u^d+
      ∑j∈Finset.range d,Δ^2*nativeRestGeneratedTestValue T P R C σ*
        (Y s^j*Y u^(d-1-j)) := by
  dsimp only
  rw [native_paired_power_difference_algebra,
    native_rest_generated_reset_replace_sub P hP ht hi hlen]
  ring

end OAI.SKFluctuations.Cavity
