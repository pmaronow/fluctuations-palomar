module

public import ComparisonSignedCavityHighRowsSupportReduction
public import ComparisonSignedCavityActualOriginalFreshPartnerCollapse

@[expose] public section

noncomputable section
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
namespace OAI.SKFluctuations.Cavity
open Set Filter MeasureTheory ProbabilityTheory Hierarchy Hierarchy.ClockTree LaplaceWindowFormalization
open scoped BigOperators Topology NNReal

def nativeOriginalGammaWeightedExpectation (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ) (a c : T.Slot) : ℝ :=
  fullScalarCutGamma T U K a c*T.disorderExpect (fullWeight n) (fullFeature n) v q P x

theorem native_original_gamma_weighted_cross_zero (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a c : T.Slot) (hU : U ≤ as.length)
    (hac : T.splitIndex a c < U) :
    nativeOriginalGammaWeightedExpectation n v q x U K T P a c=0 := by
  unfold nativeOriginalGammaWeightedExpectation
  rw [fullScalarCutGamma_cross_zero T ho U K a c hU hac,zero_mul]

def nativeOriginalGammaLowForward (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ) (a z : T.Slot)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
        nativeOriginalGammaWeightedExpectation n v q x U K r.tree
          (fun σ=>P (p.restrict (r.restrict σ))*A (p.spin (r.restrict σ)) (r.spin σ))
          (r.embed (p.embed a)) (r.embed p.mark)))).sum)).sum

def nativeOriginalGammaLowReverse (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (P : T.Assignment→ℝ) (a z : T.Slot)
    (A : (Spin n×Bool)→(Spin n×Bool)→ℝ) : ℝ :=
  ((T.markedAttach 0).map (fun p=>p.coeff*
    ((p.tree.markedAttach 0).map (fun r=>r.coeff*
      (fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
        nativeOriginalGammaWeightedExpectation n v q x U K r.tree
          (fun σ=>P (p.restrict (r.restrict σ))*A (p.spin (r.restrict σ)) (r.spin σ))
          (r.embed (p.embed a)) r.mark))).sum)).sum

theorem native_original_gamma_low_orientations_equal (n : ℕ)
    (v : FullCoordinate n→ℝ) (q : ℕ→FullCoordinate n→ℝ) (x : FullCoordinate n→ℝ)
    (U : ℕ) (K : ℕ→ℝ) {as : List PositiveMass}
    (T : ClockTree (Spin n×Bool) as) (ho : MassOrdered 0 as)
    (P : T.Assignment→ℝ) (a z : T.Slot) (A : (Spin n×Bool)→(Spin n×Bool)→ℝ)
    (hA : ∀σ τ,A σ τ=A τ σ) (hU : U ≤ as.length) (haz : T.splitIndex a z < U) :
    nativeOriginalGammaLowForward n v q x U K T P a z A=
      nativeOriginalGammaLowReverse n v q x U K T P a z A := by
  let F : (V : ClockTree (Spin n×Bool) as)→(V.Assignment→T.Assignment)→
      (T.Slot→V.Slot)→V.Slot→V.Slot→ℝ := fun V read emb c d=>
    fullScalarCutGamma V U K (emb z) d*
      nativeOriginalGammaWeightedExpectation n v q x U K V
        (fun σ=>P (read σ)*A (V.atSlot σ c) (V.atSlot σ d)) (emb a) c
  let f (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :=
    fullScalarCutGamma r.tree U K (r.embed (p.embed z)) r.mark*
      nativeOriginalGammaWeightedExpectation n v q x U K r.tree
        (fun σ=>P (p.restrict (r.restrict σ))*A (p.spin (r.restrict σ)) (r.spin σ))
        (r.embed (p.embed a)) (r.embed p.mark)
  let g (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :=
    fullScalarCutGamma r.tree U K (r.embed (p.embed z)) (r.embed p.mark)*
      nativeOriginalGammaWeightedExpectation n v q x U K r.tree
        (fun σ=>P (p.restrict (r.restrict σ))*A (p.spin (r.restrict σ)) (r.spin σ))
        (r.embed (p.embed a)) r.mark
  have Hf:=native_two_high_nested_full_of_support T a z (U-1) 0 f
    (by
      intro p hp r hr hh
      have hs : r.tree.splitIndex (r.embed (p.embed a)) (r.embed p.mark) < U := by
        rw [(p.tree.markedAttach_embed_preserves 0 r hr).2]
        omega
      dsimp only [f]
      rw [native_original_gamma_weighted_cross_zero n v q x U K r.tree ho _ _ _ hU hs,mul_zero])
    (by
      intro p hp r hr hh
      dsimp only [f]
      rw [fullScalarCutGamma_cross_zero r.tree ho U K _ _ hU (by omega),zero_mul])
  have Hg:=native_two_high_nested_full_of_support T z a (U-1) 0 g
    (by
      intro p hp r hr hh
      have hs : r.tree.splitIndex (r.embed (p.embed z)) (r.embed p.mark) < U := by
        rw [(p.tree.markedAttach_embed_preserves 0 r hr).2]
        omega
      dsimp only [g]
      rw [fullScalarCutGamma_cross_zero r.tree ho U K _ _ hU hs,zero_mul])
    (by
      intro p hp r hr hh
      dsimp only [g]
      rw [native_original_gamma_weighted_cross_zero n v q x U K r.tree ho _ _ _ hU (by omega),mul_zero])
  have HF (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      F r.tree (fun σ=>p.restrict (r.restrict σ)) (fun c=>r.embed (p.embed c))
        (r.embed p.mark) r.mark=f p r := by
    dsimp only [F,f]
    congr 2
    funext σ
    rw [r.spin_at,p.spin_at,r.restrict_at]
  have HG (p : MarkedPlacement T) (r : MarkedPlacement p.tree) :
      F r.tree (fun σ=>p.restrict (r.restrict σ)) (fun c=>r.embed (p.embed c))
        r.mark (r.embed p.mark)=g p r := by
    dsimp only [F,g]
    congr 2
    funext σ
    rw [r.spin_at,p.spin_at,r.restrict_at,hA]
  have H:=native_two_high_nested_signed_rows_commute T a z (U-1) 0 (by omega) F
  simp_rw [HF,HG] at H
  unfold nativeOriginalGammaLowForward nativeOriginalGammaLowReverse
  exact Hf.symm.trans (H.trans Hg)

end OAI.SKFluctuations.Cavity
