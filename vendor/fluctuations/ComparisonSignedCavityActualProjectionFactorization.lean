module

public import ComparisonSignedCavityActualProjectionSpine

@[expose] public section

noncomputable section
set_option maxHeartbeats 16000000
open scoped BigOperators Topology NNReal
namespace OAI.SKFluctuations.Hierarchy.ClockTree
variable {ι S B : Type} [Fintype ι] [Fintype S] [Nonempty S] [Nonempty B]
variable {as : List PositiveMass}

omit [Nonempty S] in
theorem NativeProjectionSpine.rest_factorization
    {A T : ClockTree (S×B) as} {base : NativeGeneratedTest A} {P : NativeGeneratedTest T}
    {star : ℕ} (h : NativeProjectionSpine base star P)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (q : ℕ → ι → ℝ≥0)
    (R : S → S → ℝ) (C : ℕ → ℝ)
    (J : (ι → ℝ) → A.cavityLeft.Assignment → ℝ) (x : ι → ℝ) :
    nativeStarFieldTestMean w φ T.cavityLeft (T.cavityLeftSlot P.target) star q
      (fun y σ=>J y (h.restRead σ)*nativeRestGeneratedTestValue T P R C σ) x=
    nativeStarFieldTestMean w φ A.cavityLeft (A.cavityLeftSlot base.target) star q
      (fun y σ=>J y σ*nativeRestGeneratedTestValue A base R C σ*
        (nativeStarPairFactor w φ as star q (fun u v=>R u v-C star) y
          (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.target)))^h.toothCount) x := by
  induction h generalizing a₀ q J x with
  | base=>
    dsimp only [NativeProjectionSpine.restRead,NativeProjectionSpine.toothCount]
    simp only [id_eq,pow_zero,mul_one]
  | @projection T P h a hl ih=>
    dsimp only [NativeProjectionSpine.restRead,NativeProjectionSpine.toothCount]
    simp_rw [native_rest_add_projection_value P a hl R C]
    let F:=fun u v=>R u v-C star
    let G:=fun (y:ι→ℝ) (σ:T.cavityLeft.Assignment)=>
      J y (h.restRead σ)*nativeRestGeneratedTestValue T P R C σ
    have hFun : (fun (y:ι→ℝ) (σ:(nativeFreshAtSlot T a P.target star).tree.cavityLeft.Assignment)=>
        J y (h.restRead ((nativeFreshAtSlot T a P.target star).restRestrict σ))*
          (nativeRestGeneratedTestValue T P R C ((nativeFreshAtSlot T a P.target star).restRestrict σ)*
            (R (T.cavityLeft.atSlot ((nativeFreshAtSlot T a P.target star).restRestrict σ)
              (T.cavityLeftSlot P.target)) ((nativeFreshAtSlot T a P.target star).restSpin σ)-C star)))=
        (fun y σ=>G y ((nativeFreshAtSlot T a P.target star).restRestrict σ)*
          F (T.cavityLeft.atSlot ((nativeFreshAtSlot T a P.target star).restRestrict σ)
            (T.cavityLeftSlot P.target)) ((nativeFreshAtSlot T a P.target star).restSpin σ)) := by
      funext y σ
      dsimp only [G,F]
      ring
    rw [hFun]
    dsimp only [NativeGeneratedTest.addProjection]
    rw [native_star_field_test_fresh_rest_factor T P.target star hl a hw φ ho q G F x]
    have hPayload : (fun y σ=>G y σ*nativeStarPairFactor w φ as star q F y
        (T.cavityLeft.atSlot σ (T.cavityLeftSlot P.target)))=
        (fun y σ=>(J y (h.restRead σ)*nativeStarPairFactor w φ as star q F y
          (A.cavityLeft.atSlot (h.restRead σ) (A.cavityLeftSlot base.target)))*
          nativeRestGeneratedTestValue T P R C σ) := by
      funext y σ
      rw [h.restTargetRead]
      dsimp only [G]
      ring
    rw [hPayload,ih ho q (fun y σ=>J y σ*nativeStarPairFactor w φ as star q F y
      (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.target))) x]
    apply congrArg (fun L=>nativeStarFieldTestMean w φ A.cavityLeft
      (A.cavityLeftSlot base.target) star q L x)
    funext y σ
    dsimp only [F]
    rw [pow_succ]
    ring

theorem native_actual_generated_projection_power_law
    {T : ClockTree (S×B) as} {i star U k : ℕ} {seed : List NativeResourceMark}
    {P : NativeResourceTerm i star T}
    (hP : NativeActualResourceGenerated i star U seed k T P)
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (q : ℕ → ι → ℝ≥0)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x : ι → ℝ) :
    ∃(A : ClockTree (S×B) as) (base : NativeResourceTerm i star A)
      (seed₀ : List NativeResourceMark) (k₀ : ℕ),
      NativeActualResourceGenerated i star U seed₀ k₀ A base ∧ base.live.test.teeth=[] ∧
      T.cavityLeft.expect w φ q (nativeRestGeneratedTestValue T P.live.test R C) x=
        nativeStarFieldTestMean w φ A.cavityLeft (A.cavityLeftSlot base.live.test.target) star q
          (fun y σ=>nativeRestGeneratedTestValue A base.live.test R C σ*
            (nativeStarPairFactor w φ as star q (fun u v=>R u v-C star) y
              (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.live.test.target)))^P.live.test.teeth.length) x := by
  obtain ⟨A,base,seed₀,k₀,hBase,ht,⟨spine⟩⟩:=hP.projectionDecomposition
  refine ⟨A,base,seed₀,k₀,hBase,ht,?_⟩
  have hc:=spine.teeth_length
  rw [ht,List.length_nil,Nat.zero_add] at hc
  have H:=spine.rest_factorization hw φ ho q R C (fun _ _=>1) x
  simp only [one_mul] at H
  rw [←hc] at H
  exact (native_star_field_test_field_independent T.cavityLeft
    (T.cavityLeftSlot P.live.test.target) star hw φ ho q
    (nativeRestGeneratedTestValue T P.live.test R C) x).symm.trans H

theorem native_actual_initial_expansion_projection_power_law
    (i star U : ℕ) (hi : i ≤ star) (hs : star < U) (hU : U≤as.length) (a : ℝ)
    (Γ : ∀st : NativeHighSwitchState (S×B) as,MarkedPlacement st.tree → ℝ)
    (ops : List NativeActualExpansionOp) (Q : NativeActualResourceState (S×B) as i star)
    (hQ : Q∈nativeActualResourceExpansion Γ hs (by omega) ops
      (nativeActualInitialState as i star a (by omega)))
    {w : S → ℝ} (hw : ∀σ,0<w σ) (φ : S → (ι → ℝ)→L[ℝ]ℝ)
    {a₀ : ℝ} (ho : MassOrdered a₀ as) (q : ℕ → ι → ℝ≥0)
    (R : S → S → ℝ) (C : ℕ → ℝ) (x : ι → ℝ) :
    ∃(A : ClockTree (S×B) as) (base : NativeResourceTerm i star A)
      (seed₀ : List NativeResourceMark) (k₀ : ℕ),
      NativeActualResourceGenerated i star U seed₀ k₀ A base ∧ base.live.test.teeth=[] ∧
      Q.tree.cavityLeft.expect w φ q (nativeRestGeneratedTestValue Q.tree Q.term.live.test R C) x=
        nativeStarFieldTestMean w φ A.cavityLeft (A.cavityLeftSlot base.live.test.target) star q
          (fun y σ=>nativeRestGeneratedTestValue A base.live.test R C σ*
            (nativeStarPairFactor w φ as star q (fun u v=>R u v-C star) y
              (A.cavityLeft.atSlot σ (A.cavityLeftSlot base.live.test.target)))^Q.term.live.test.teeth.length) x :=
  native_actual_generated_projection_power_law
    (nativeActualInitialExpansion_valid as i star U hi hs hU a Γ ops Q hQ) hw φ ho q R C x

end OAI.SKFluctuations.Hierarchy.ClockTree
