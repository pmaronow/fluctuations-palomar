module

public import ComparisonSignedCavityGeneratedResources
public import CavityBoundaryResamplingMoments
public import CavitySplitDensity

@[expose] public section

noncomputable section
set_option maxHeartbeats 5000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
open OAI.SKFluctuations.Cavity
variable {S : Type} {ι : Type*} [Fintype S] [Nonempty S] [Fintype ι] [Nonempty ι]
variable {as : List PositiveMass}

def nativeResourceEnvelope (A x W ε : ℝ) (rs : List NativeResourceMark) : ℝ :=
  (rs.map (fun m => A*m.savedScale x W ε)).prod

theorem NativeResourceMark.savedScale_pos (m : NativeResourceMark)
    {x W ε : ℝ} (hx : 0<x) (hW : 0<W) (hε : 0<ε) :
    0 < m.savedScale x W ε := by
  cases m <;> simp only [NativeResourceMark.savedScale] <;> positivity

theorem nativeResourceEnvelope_pos (rs : List NativeResourceMark)
    {A x W ε : ℝ} (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε) :
    0<nativeResourceEnvelope A x W ε rs := by
  induction rs with
  | nil => simp [nativeResourceEnvelope]
  | cons m rs ih =>
    change 0<(A*m.savedScale x W ε)*nativeResourceEnvelope A x W ε rs
    exact mul_pos (mul_pos hA (m.savedScale_pos hx hW hε)) ih

theorem nativeResourceEnvelope_append (A x W ε : ℝ)
    (rs ss : List NativeResourceMark) :
    nativeResourceEnvelope A x W ε (rs++ss) =
      nativeResourceEnvelope A x W ε rs*nativeResourceEnvelope A x W ε ss := by
  simp only [nativeResourceEnvelope,List.map_append,List.prod_append]

theorem nativeResourceEnvelope_scale (A x W ε : ℝ) (rs : List NativeResourceMark) :
    nativeResourceEnvelope A x W ε rs = A^rs.length*nativeResourceScale x W ε rs := by
  induction rs with
  | nil => simp [nativeResourceEnvelope,nativeResourceScale]
  | cons m rs ih =>
    change (A*m.savedScale x W ε)*nativeResourceEnvelope A x W ε rs =
      A^(rs.length+1)*(m.savedScale x W ε*nativeResourceScale x W ε rs)
    rw [ih,pow_succ]
    ring

def NativeResourceMonomial.PairMomentBudget {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ) : Prop :=
  ∀ e : Fin P.factors.length,
    let f := P.factors.get e
    (pairClock (S:=S) as (f.1.cut i star)).disorderExpect w φ v q
      (fun σ => |R (pairSpin as (f.1.cut i star) σ).1
        (pairSpin as (f.1.cut i star) σ).2-C (f.1.cut i star)|^(2*P.factors.length)) x₀ ≤
      (A*f.1.savedScale x W ε)^(2*P.factors.length)

omit [Fintype S] [Nonempty S] in
theorem NativeResourceMonomial.factor_endpoints_distinct {i star : ℕ}
    {T : ClockTree S as} (P : NativeResourceMonomial i star T)
    (hi : i ≤ star) (hstar : star < as.length) (e : Fin P.factors.length) :
    (P.factors.get e).2.1 ≠ (P.factors.get e).2.2 := by
  have hcut := P.cuts (P.factors.get e) (List.get_mem _ e)
  have hlow : (P.factors.get e).1.cut i star < as.length := by
    cases (P.factors.get e).1 <;> simp only [NativeResourceMark.cut] <;> omega
  intro heq
  rw [heq,T.splitIndex_self] at hcut
  omega

omit [Fintype S] [Nonempty S] in
theorem NativeResourceMonomial.value_eq_product_get {i star : ℕ}
    {T : ClockTree S as} (P : NativeResourceMonomial i star T)
    (R : S → S → ℝ) (C : ℕ → ℝ) (σ : T.Assignment) :
    P.test.value R C σ = ∏ e : Fin P.factors.length,
      (R (T.atSlot σ (P.factors.get e).2.1) (T.atSlot σ (P.factors.get e).2.2)-
        C (T.splitIndex (P.factors.get e).2.1 (P.factors.get e).2.2)) := by
  rw [←P.factor_product_eq R C σ]
  let f := fun e : NativeResourceFactor T =>
    R (T.atSlot σ e.2.1) (T.atSlot σ e.2.2)-C (T.splitIndex e.2.1 e.2.2)
  rw [←List.prod_ofFn]
  change (P.factors.map f).prod = (List.ofFn (f ∘ P.factors.get)).prod
  rw [←List.map_ofFn,List.ofFn_get]

theorem NativeResourceMonomial.square_moment_le {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceMonomial i star T) {w : S → ℝ} (hw : ∀ σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ)
    (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star < as.length)
    (hm : P.PairMomentBudget w φ v q R C x₀ A x W ε) :
    T.disorderExpect w φ v q (fun σ => (P.test.value R C σ)^2) x₀ ≤
      (nativeResourceEnvelope A x W ε P.tags)^2 := by
  by_cases ha : 0<P.factors.length
  · let F := fun e : Fin P.factors.length => fun σ : T.Assignment =>
      R (T.atSlot σ (P.factors.get e).2.1) (T.atSlot σ (P.factors.get e).2.2)-
        C (T.splitIndex (P.factors.get e).2.1 (P.factors.get e).2.2)
    let rho := fun e : Fin P.factors.length =>
      A*(P.factors.get e).1.savedScale x W ε
    have hrho : ∀ e,0<rho e := fun e =>
      mul_pos hA ((P.factors.get e).1.savedScale_pos hx hW hε)
    have H := finite_weighted_product_square_scales (A:=T.Assignment)
      (a:=P.factors.length) ha
      (fun σ : T.Assignment => T.disorderWeight w φ v q σ x₀) F
      (T.disorderWeight_probability hw φ ho v q x₀).1 rho hrho (by
        intro e
        change T.disorderExpect w φ v q (fun σ => |F e σ|^(2*P.factors.length)) x₀ ≤ _
        dsimp only [F]
        rw [T.disorderExpect_pairAtSlot_actual hw φ ho v q x₀
          (P.factors.get e).2.1 (P.factors.get e).2.2
          (P.factor_endpoints_distinct hi hstar e)
          (fun s t => |R s t-C (T.splitIndex (P.factors.get e).2.1
            (P.factors.get e).2.2)|^(2*P.factors.length))]
        rw [P.cuts (P.factors.get e) (List.get_mem _ e)]
        exact hm e)
    have hr : (∏ e,rho e) = nativeResourceEnvelope A x W ε P.tags := by
      unfold nativeResourceEnvelope NativeResourceMonomial.tags
      rw [List.map_map]
      rw [←List.prod_ofFn]
      change (List.ofFn ((fun f : NativeResourceFactor T =>
        A*f.1.savedScale x W ε) ∘ P.factors.get)).prod =
        (P.factors.map (fun f => A*f.1.savedScale x W ε)).prod
      rw [←List.map_ofFn,List.ofFn_get]
    simpa only [←P.value_eq_product_get R C,hr,ClockTree.disorderExpect,F] using H
  · have hnil : P.factors = [] := List.eq_nil_of_length_eq_zero (by omega)
    have he : P.test.value R C = fun _ => 1 := by
      funext σ
      rw [←P.factor_product_eq R C σ,hnil]
      rfl
    simp only [he,one_pow,T.disorderExpect_one hw φ ho,
      NativeResourceMonomial.tags,hnil,nativeResourceEnvelope,List.map_nil,List.prod_nil,le_refl]

theorem NativeFrozenResource.mean_abs_le {i star : ℕ}
    (F : NativeFrozenResource S as i star) {w : S → ℝ} (hw : ∀ σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ)
    (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star < as.length)
    (hm : F.monomial.PairMomentBudget w φ v q R C x₀ A x W ε) :
    |F.mean w φ v q R C x₀| ≤ nativeResourceEnvelope A x W ε F.monomial.tags := by
  have H := F.monomial.square_moment_le hw φ ho v q R C x₀ A x W ε
    hA hx hW hε hi hstar hm
  have HC := F.tree.disorderExpect_mul_sq_le hw φ ho v q
    (F.monomial.test.value R C) (fun _ => 1) x₀
  simp only [mul_one,one_pow,F.tree.disorderExpect_one hw φ ho] at HC
  apply (sq_le_sq₀ (abs_nonneg _) (nativeResourceEnvelope_pos _ hA hx hW hε).le).mp
  simpa only [sq_abs,NativeFrozenResource.mean] using HC.trans H

def NativeResourceTerm.PairMomentBudget {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) (w : S → ℝ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ) : Prop :=
  P.live.PairMomentBudget w φ v q R C x₀ A x W ε ∧
    ∀ F∈P.frozen,F.monomial.PairMomentBudget w φ v q R C x₀ A x W ε

private theorem frozen_resource_product_abs_le {i star : ℕ}
    (Fs : List (NativeFrozenResource S as i star)) {w : S → ℝ} (hw : ∀ σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ)
    (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star < as.length)
    (hm : ∀ F∈Fs,F.monomial.PairMomentBudget w φ v q R C x₀ A x W ε) :
    |(Fs.map (fun F => F.mean w φ v q R C x₀)).prod| ≤
      nativeResourceEnvelope A x W ε (Fs.flatMap (fun F => F.monomial.tags)) := by
  induction Fs with
  | nil => simp [nativeResourceEnvelope]
  | cons F Fs ih =>
    have hF := F.mean_abs_le hw φ ho v q R C x₀ A x W ε hA hx hW hε hi hstar
      (hm F (List.mem_cons_self))
    have hFs := ih (fun F hF => hm F (List.mem_cons_of_mem _ hF))
    simpa only [List.map_cons,List.prod_cons,abs_mul,List.flatMap_cons,
      nativeResourceEnvelope_append] using
      mul_le_mul hF hFs (abs_nonneg _) (nativeResourceEnvelope_pos _ hA hx hW hε).le

theorem NativeResourceTerm.square_moment_le {i star : ℕ} {T : ClockTree S as}
    (P : NativeResourceTerm i star T) {w : S → ℝ} (hw : ∀ σ,0<w σ)
    (φ : S → (ι → ℝ) →L[ℝ]ℝ) (ho : MassOrdered 0 as)
    (v : ι → ℝ) (q : ℕ → ι → ℝ) (R : S → S → ℝ)
    (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star < as.length)
    (hm : P.PairMomentBudget w φ v q R C x₀ A x W ε) :
    T.disorderExpect w φ v q (fun σ => (P.value w φ v q R C x₀ σ)^2) x₀ ≤
      (|P.coefficient| * nativeResourceEnvelope A x W ε P.resources)^2 := by
  have HF := frozen_resource_product_abs_le P.frozen hw φ ho v q R C x₀ A x W ε
    hA hx hW hε hi hstar hm.2
  have HS : |P.scalar w φ v q R C x₀| ≤
      |P.coefficient| * nativeResourceEnvelope A x W ε
        (P.frozen.flatMap (fun F => F.monomial.tags)) := by
    simpa only [NativeResourceTerm.scalar,abs_mul] using
      mul_le_mul_of_nonneg_left HF (abs_nonneg P.coefficient)
  have HS2 := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (abs_nonneg _)
    (nativeResourceEnvelope_pos _ hA hx hW hε).le)).mpr HS
  rw [sq_abs] at HS2
  have HL := P.live.square_moment_le hw φ ho v q R C x₀ A x W ε
    hA hx hW hε hi hstar hm.1
  have hL0 : 0 ≤ T.disorderExpect w φ v q (fun σ => (P.live.test.value R C σ)^2) x₀ :=
    Finset.sum_nonneg (fun σ _ => mul_nonneg
      ((T.disorderWeight_probability hw φ ho v q x₀).1 σ) (sq_nonneg _))
  have he : (fun σ => (P.value w φ v q R C x₀ σ)^2) =
      fun σ => (P.scalar w φ v q R C x₀)^2*(P.live.test.value R C σ)^2 := by
    funext σ
    exact mul_pow _ _ 2
  rw [he,T.disorderExpect_const_mul hw φ ho]
  apply (mul_le_mul HS2 HL hL0 (sq_nonneg _)).trans
  rw [NativeResourceTerm.resources,nativeResourceEnvelope_append]
  ring_nf
  rfl

theorem NativeResourceGenerated.terminal_pairing_sq_le {i star : ℕ}
    {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
    {P : NativeResourceTerm i star T} (hP : NativeResourceGenerated i star seed k T P)
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star < as.length)
    (hm : P.PairMomentBudget w φ v q R C x₀ A x W ε)
    (G : T.Assignment → ℝ) (B : ℝ)
    (hG : T.disorderExpect w φ v q (fun σ => (G σ)^2) x₀ ≤ B^2) :
    (T.disorderExpect w φ v q
      (fun σ => P.value w φ v q R C x₀ σ*G σ) x₀)^2 ≤
      (|P.coefficient| * A^P.resources.length*nativeResourceScale x W ε seed*
        (ε*W)^k*B)^2 := by
  have HS := P.square_moment_le hw φ ho v q R C x₀ A x W ε hA hx hW hε hi hstar hm
  have HG0 : 0 ≤ T.disorderExpect w φ v q (fun σ => (G σ)^2) x₀ :=
    Finset.sum_nonneg (fun σ _ => mul_nonneg
      ((T.disorderWeight_probability hw φ ho v q x₀).1 σ) (sq_nonneg _))
  have HC := T.disorderExpect_mul_sq_le hw φ ho v q (P.value w φ v q R C x₀) G x₀
  apply (HC.trans (mul_le_mul HS hG HG0 (sq_nonneg _))).trans
  rw [nativeResourceEnvelope_scale,hP.saved_scale x W ε]
  ring_nf
  rfl

theorem NativeResourceGenerated.normalized_terminal_pairing_sq_le {i star : ℕ}
    {seed : List NativeResourceMark} {k : ℕ} {T : ClockTree S as}
    {P : NativeResourceTerm i star T} (hP : NativeResourceGenerated i star seed k T P)
    {w : S → ℝ} (hw : ∀ σ,0<w σ) (φ : S → (ι → ℝ) →L[ℝ]ℝ)
    (ho : MassOrdered 0 as) (v : ι → ℝ) (q : ℕ → ι → ℝ)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x₀ : ι → ℝ) (A x W ε : ℝ)
    (hA : 0<A) (hx : 0<x) (hW : 0<W) (hε : 0<ε)
    (hi : i ≤ star) (hstar : star < as.length)
    (hm : P.PairMomentBudget w φ v q R C x₀ A x W ε)
    (G : T.Assignment → ℝ) (B : ℝ)
    (hG : T.disorderExpect w φ v q (fun σ => (G σ)^2) x₀ ≤ B^2) :
    (T.disorderExpect w φ v q
      (fun σ => (W⁻¹)^k*(P.value w φ v q R C x₀ σ*G σ)) x₀)^2 ≤
      (|P.coefficient| * A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B)^2 := by
  rw [T.disorderExpect_const_mul hw φ ho,mul_pow]
  have H := mul_le_mul_of_nonneg_left
    (hP.terminal_pairing_sq_le hw φ ho v q R C x₀ A x W ε hA hx hW hε hi hstar hm G B hG)
    (sq_nonneg ((W⁻¹)^k))
  rw [hP.total_factor_depth] at H
  apply H.trans
  rw [←mul_pow]
  have he : (W⁻¹)^k*(|P.coefficient| * A^(seed.length+k)*
      nativeResourceScale x W ε seed*(ε*W)^k*B) =
      |P.coefficient| * A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B := by
    calc
      _ = (|P.coefficient| * A^(seed.length+k)*nativeResourceScale x W ε seed*ε^k*B)*
          ((W⁻¹)^k*W^k) := by rw [mul_pow];ring
      _ = _ := by rw [←mul_pow,inv_mul_cancel₀ hW.ne',one_pow,mul_one]
  rw [he]

end OAI.SKFluctuations.Hierarchy.ClockTree
