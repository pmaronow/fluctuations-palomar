module

public import SKBarriers2.Analysis.CompactParameterJets
public import SKBarriers2.Corner.FrozenRowsNoise

@[expose] public section

noncomputable section
open scoped BigOperators Topology ContDiff
open Set OAI.SK.Analytic SKOptimized.Overshoot

namespace SKBarriers2.Corner

abbrev FrozenGeometryBase := ℝ × (ℝ × ℝ)
abbrev FrozenGeometryParameter := (FrozenGeometryBase × ℝ) × ℝ

def frozenGeometryQuadratic (p : FrozenGeometryParameter) : QuadraticTerminal :=
  separableTaylorQuadratic 0 p.1.1.2.1 p.1.1.2.2 0

def frozenGeometryMass (j : Fin 12) (p : FrozenGeometryParameter) : ℝ :=
  p.1.1.1 * frozenUnitMass j

def frozenGeometryDirection (β : ℝ) (j : Fin 12) (p : FrozenGeometryParameter) : Vec3 :=
  p.1.2 • frozenUnitDirection β p.2 j

def frozenGeometryLabels (j : ℕ) : List (Fin 12) := (List.finRange 12).drop (j + 1)

def frozenGeometrySchedule (β : ℝ) (p : FrozenGeometryParameter) : List (ℝ × Vec3) :=
  (List.finRange 12).map (fun j => (frozenGeometryMass j p, frozenGeometryDirection β j p))

def frozenGeometryBaseDomain : Set FrozenGeometryParameter :=
  {p | |p.2| < 3 / 5 ∧ p.1.1.1 ≠ 0}

def frozenGeometryDomain (β : ℝ) : Set FrozenGeometryParameter :=
  {p | p ∈ frozenGeometryBaseDomain ∧
    NoisePrecisionsPositive (frozenGeometrySchedule β p) (frozenGeometryQuadratic p)}

theorem frozenGeometryBaseDomain_isOpen : IsOpen frozenGeometryBaseDomain := by
  exact (isOpen_lt (continuous_abs.comp continuous_snd) continuous_const).inter
    (isOpen_ne_fun (by fun_prop) continuous_const)

theorem frozenGeometryDirection_contDiffAt (β : ℝ) {p : FrozenGeometryParameter}
    (hp : |p.2| < 3 / 5) (j : Fin 12) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun q => frozenGeometryDirection β j q i) p := by
  have h := (contDiffAt_pi.mp (frozenUnitDirection_contDiffAt_k β hp j)) i
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun q : FrozenGeometryParameter => q.1.2) p).mul
    (h.comp p (by fun_prop))

theorem frozenGeometryQuadratic_contDiffAt (p : FrozenGeometryParameter) :
    QuadraticFamilyContDiffAt frozenGeometryQuadratic p := by
  constructor
  · simp only [frozenGeometryQuadratic, separableTaylorQuadratic, mul_zero, sub_zero,
      zero_pow (by decide : 2 ≠ 0), add_zero]
    exact contDiffAt_const
  · intro i
    simp only [frozenGeometryQuadratic, separableTaylorQuadratic, mul_zero, sub_zero]
    fun_prop
  · intro i j
    by_cases hij : i = j <;>
      simp only [frozenGeometryQuadratic, separableTaylorQuadratic, hij,
        ite_true, ite_false] <;> fun_prop

theorem frozenGeometryDomain_isOpen (β : ℝ) : IsOpen (frozenGeometryDomain β) := by
  apply noisePrecisionsPositive_isOpen (List.finRange 12)
    frozenGeometryMass (frozenGeometryDirection β) frozenGeometryQuadratic
    frozenGeometryBaseDomain frozenGeometryBaseDomain_isOpen
  · intro j _
    unfold frozenGeometryMass
    fun_prop
  · intro j _ i p hp
    exact (frozenGeometryDirection_contDiffAt β hp.1 j i).contDiffWithinAt
  · intro i j p _
    exact ((frozenGeometryQuadratic_contDiffAt p).hessian i j).contDiffWithinAt

private theorem noisePrecisionsPositive_zeroDirection {ι : Type*}
    (l : List ι) (m : ι → ℝ) (Q : QuadraticTerminal) :
    NoisePrecisionsPositive (l.map (fun j => (m j, (0 : Vec3)))) Q := by
  induction l with
  | nil => simp [NoisePrecisionsPositive, riccatiPrecisions]
  | cons j l ih =>
    simpa only [List.map_cons, NoisePrecisionsPositive, riccatiPrecisions,
      List.mem_cons, forall_eq_or_imp, QuadraticTerminal.precision,
      QuadraticTerminal.curvature, QuadraticTerminal.hessianDirection,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero,
      zero_lt_one, true_and] using ih

theorem frozenGeometry_zero_mem (β : ℝ) (b : FrozenGeometryBase) (k : ℝ)
    (ha : b.1 ≠ 0) (hk : |k| < 3 / 5) :
    ((b, 0), k) ∈ frozenGeometryDomain β := by
  refine ⟨⟨hk, ha⟩, ?_⟩
  simpa only [frozenGeometrySchedule, frozenGeometryDirection, zero_smul] using
    noisePrecisionsPositive_zeroDirection (List.finRange 12)
      (fun j => frozenGeometryMass j ((b, 0), k))
      (frozenGeometryQuadratic ((b, 0), k))

def frozenGeometryBaseBox (a₀ B : ℝ) : Set FrozenGeometryBase :=
  Icc a₀ 1 ×ˢ (Icc (-B) B ×ˢ Icc (-B) B)

theorem frozenGeometry_uniform_domain (β a₀ B : ℝ) (ha₀ : 0 < a₀) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ b ∈ frozenGeometryBaseBox a₀ B, ∀ ρ ∈ Icc (-δ) δ,
        ∀ k ∈ Icc (-(1 / 2) : ℝ) (1 / 2),
          ((b, ρ), k) ∈ frozenGeometryDomain β := by
  let K := frozenGeometryBaseBox a₀ B ×ˢ Icc (-(1 / 2) : ℝ) (1 / 2)
  let swap : (FrozenGeometryBase × ℝ) × ℝ → FrozenGeometryParameter :=
    fun q => ((q.1.1, q.2), q.1.2)
  let U := swap ⁻¹' frozenGeometryDomain β
  have hK : IsCompact K :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc
  have hU : IsOpen U := (frozenGeometryDomain_isOpen β).preimage (by fun_prop)
  have hzero : K ×ˢ ({0} : Set ℝ) ⊆ U := by
    rintro ⟨⟨b, k⟩, ρ⟩ ⟨⟨hb, hk⟩, hρ⟩
    have hρ0 : ρ = 0 := hρ
    subst ρ
    exact frozenGeometry_zero_mem β b k (ne_of_gt (ha₀.trans_le hb.1.1))
      (abs_lt.mpr ⟨by linarith [hk.1], by linarith [hk.2]⟩)
  obtain ⟨δ, hδ, H⟩ := SKBarriers2.compact_zero_slice_rectangle hK hU hzero
  refine ⟨δ, hδ, ?_⟩
  intro b hb ρ hρ k hk
  exact H (show ((b, k), ρ) ∈ K ×ˢ Icc (-δ) δ from ⟨⟨hb, hk⟩, hρ⟩)

private theorem noisePrecisionsPositive_suffix (l t : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (h : NoisePrecisionsPositive (l ++ t) Q) :
    NoisePrecisionsPositive t Q := by
  induction l with
  | nil => exact h
  | cons u l ih =>
    apply ih
    intro d hd
    exact h d (List.mem_cons_of_mem _ hd)

private theorem riccatiAdmissible_of_positivePrecisions (l : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (h : NoisePrecisionsPositive l Q)
    (hm : ∀ u ∈ l, u.1 ≠ 0) : RiccatiAdmissible l Q := by
  induction l with
  | nil => trivial
  | cons u l ih =>
    refine ⟨ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
      (fun v hv => hm v (List.mem_cons_of_mem _ hv)), hm u List.mem_cons_self, ?_⟩
    exact h _ List.mem_cons_self

theorem frozenGeometry_suffix_admissible (β : ℝ) {p : FrozenGeometryParameter}
    (hp : p ∈ frozenGeometryDomain β) (j : ℕ) :
    RiccatiAdmissible
      ((frozenGeometryLabels j).map
        (fun i => (frozenGeometryMass i p, frozenGeometryDirection β i p)))
      (frozenGeometryQuadratic p) := by
  have hfull : RiccatiAdmissible (frozenGeometrySchedule β p) (frozenGeometryQuadratic p) := by
    apply riccatiAdmissible_of_positivePrecisions _ _ hp.2
    intro u hu
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hu
    exact mul_ne_zero hp.1.2 (by fin_cases i <;> norm_num [frozenUnitMass])
  have hs := riccatiAdmissible_suffix
    ((frozenGeometrySchedule β p).take (j + 1))
    ((frozenGeometrySchedule β p).drop (j + 1)) (frozenGeometryQuadratic p)
    (by simpa only [List.take_append_drop] using hfull)
  simpa only [frozenGeometrySchedule, frozenGeometryLabels, List.map_drop] using hs

private theorem positivePrecisions_of_riccatiAdmissible (l : List (ℝ × Vec3))
    (Q : QuadraticTerminal) (h : RiccatiAdmissible l Q) : NoisePrecisionsPositive l Q := by
  induction l with
  | nil => simp [NoisePrecisionsPositive, riccatiPrecisions]
  | cons u l ih =>
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact h.2.2
    · exact ih h.1 d hd

def frozenGeometryCoefficient (β : ℝ) (j : Fin 12) (i : Fin 9)
    (p : FrozenGeometryParameter) : ℝ :=
  let t := (frozenGeometryLabels j.val).map
    (fun q => (frozenGeometryMass q p, frozenGeometryDirection β q p))
  let Q := frozenGeometryQuadratic p
  let R := riccatiRecursion t Q
  let v := frozenGeometryDirection β j p
  let μ := gaussianPathMean t Q 0
  let b := gaussianPathLinear t Q v
  ![R.constant, R.linearDirection v, R.curvature v / 2,
    μ 0, μ 1, μ 2, b 0, b 1, b 2] i

theorem frozenGeometryCoefficient_contDiffOn (β : ℝ) (j : Fin 12) (i : Fin 9) :
    ContDiffOn ℝ ∞ (frozenGeometryCoefficient β j i) (frozenGeometryDomain β) := by
  intro p hp
  let l := frozenGeometryLabels j.val
  let m := frozenGeometryMass
  let v := frozenGeometryDirection β
  let Q := frozenGeometryQuadratic
  have hm (q : Fin 12) (_ : q ∈ l) : ContDiffAt ℝ ∞ (m q) p := by
    unfold m frozenGeometryMass
    fun_prop
  have hv (q : Fin 12) (_ : q ∈ l) (a : Fin 3) :
      ContDiffAt ℝ ∞ (fun p => v q p a) p :=
    frozenGeometryDirection_contDiffAt β hp.1.1 q a
  have hQ := frozenGeometryQuadratic_contDiffAt p
  have hA := frozenGeometry_suffix_admissible β hp j.val
  have hR := riccatiRecursion_coefficients_contDiffAt l m v Q hm hv hQ hA
  have hhead (a : Fin 3) : ContDiffAt ℝ ∞ (fun p => v j p a) p :=
    frozenGeometryDirection_contDiffAt β hp.1.1 j a
  have hμ := gaussianPathMean_contDiffAt l m v Q hm hv hQ hA
    (fun _ => (0 : Vec3)) (fun _ => contDiffAt_const)
  have hb := gaussianPathLinear_contDiffAt l m v Q hm hv hQ.hessian
    (positivePrecisions_of_riccatiAdmissible _ _ hA) (v j) hhead
  have hL := hR.linearDirection hhead
  have hH : ContDiffAt ℝ ∞
      (fun p => (riccatiRecursion (l.map (fun q => (m q p, v q p))) (Q p)).curvature
        (v j p) / 2) p := by
    exact (ContDiffAt.sum (fun a _ => (hhead a).mul (hR.hessianDirection hhead a))).div_const 2
  have H : ContDiffAt ℝ ∞ (frozenGeometryCoefficient β j i) p := by
    fin_cases i
    · exact hR.constant
    · exact hL
    · exact hH
    · exact hμ 0
    · exact hμ 1
    · exact hμ 2
    · exact hb 0
    · exact hb 1
    · exact hb 2
  exact H.contDiffWithinAt

theorem frozenGeometry_uniform_coefficients (β a₀ B : ℝ) (ha₀ : 0 < a₀) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ b ∈ frozenGeometryBaseBox a₀ B, ∀ ρ ∈ Icc (-δ) δ,
        ∀ k ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ∀ j : Fin 12, ∀ i : Fin 9,
          let F := frozenGeometryCoefficient β j i
          let p := ((b, ρ), k)
          |F p| ≤ C ∧ |SKBarriers2.parameterVerticalDerivative F p| ≤ C ∧
            |SKBarriers2.parameterVerticalDerivative
              (SKBarriers2.parameterVerticalDerivative F) p| ≤ C ∧
            HasDerivAt (fun t => F ((b, ρ), t))
              (SKBarriers2.parameterVerticalDerivative F p) k ∧
            HasDerivAt (fun t => SKBarriers2.parameterVerticalDerivative F ((b, ρ), t))
              (SKBarriers2.parameterVerticalDerivative
                (SKBarriers2.parameterVerticalDerivative F) p) k := by
  obtain ⟨δ, hδ, hδU⟩ := frozenGeometry_uniform_domain β a₀ B ha₀
  let K := (frozenGeometryBaseBox a₀ B ×ˢ Icc (-δ) δ) ×ˢ
    Icc (-(1 / 2) : ℝ) (1 / 2)
  have hK : IsCompact K :=
    ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).prod isCompact_Icc).prod isCompact_Icc
  have hKU : K ⊆ frozenGeometryDomain β := by
    rintro ⟨⟨b, ρ⟩, k⟩ ⟨⟨hb, hρ⟩, hk⟩
    exact hδU b hb ρ hρ k hk
  choose S hS hbound using fun ji : Fin 12 × Fin 9 =>
    SKBarriers2.compact_parameter_vertical_bounds hK (frozenGeometryDomain_isOpen β)
      (frozenGeometryCoefficient_contDiffOn β ji.1 ji.2) hKU
  let C := 1 + ∑ ji : Fin 12 × Fin 9, S ji
  have hC : 0 < C := by
    have hsum : 0 ≤ ∑ ji : Fin 12 × Fin 9, S ji :=
      Finset.sum_nonneg (fun ji _ => (hS ji).le)
    dsimp only [C]
    linarith
  refine ⟨δ, C, hδ, hC, ?_⟩
  intro b hb ρ hρ k hk j i
  have hSC : S (j, i) ≤ C := by
    have H := Finset.single_le_sum (f := S) (fun ji _ => (hS ji).le)
      (Finset.mem_univ (j, i))
    dsimp only [C]
    linarith
  have H := hbound (j, i) ((b, ρ), k) ⟨⟨hb, hρ⟩, hk⟩
  exact ⟨H.1.trans hSC, H.2.1.trans hSC, H.2.2.1.trans hSC,
    H.2.2.2.1, H.2.2.2.2⟩

end SKBarriers2.Corner
