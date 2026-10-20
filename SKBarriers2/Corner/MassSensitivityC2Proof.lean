module

public import SKBarriers2.Corner.MassValue
public import SKBarriers2.Corner.KStability
public import SKBarriers2.Analysis.ParamStep2

@[expose] public section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set OAI.SK.Analytic

namespace SKBarriers2.Corner

structure C2BoundAt (A : ℝ) (f : ℝ → ℝ) (k : ℝ) : Prop where
  nonneg : 0 ≤ A
  smooth : ContDiffAt ℝ 2 f k
  bound : ∀ c : ℕ, c ≤ 2 → |iteratedDeriv c f k| ≤ A

namespace C2BoundAt

theorem mono {A B k : ℝ} {f : ℝ → ℝ} (hf : C2BoundAt A f k)
    (hAB : A ≤ B) : C2BoundAt B f k := by
  exact ⟨hf.nonneg.trans hAB, hf.smooth, fun c hc => (hf.bound c hc).trans hAB⟩

theorem const (a k : ℝ) : C2BoundAt |a| (fun _ : ℝ => a) k := by
  refine ⟨abs_nonneg _, contDiffAt_const, ?_⟩
  intro c _
  by_cases hc : c = 0
  · subst c
    exact le_rfl
  · simp only [iteratedDeriv_const, hc, ite_false, abs_zero, abs_nonneg]

theorem add {A B k : ℝ} {f g : ℝ → ℝ}
    (hf : C2BoundAt A f k) (hg : C2BoundAt B g k) :
    C2BoundAt (A+B) (fun t => f t+g t) k := by
  refine ⟨add_nonneg hf.nonneg hg.nonneg, hf.smooth.add hg.smooth, ?_⟩
  intro c hc
  rw [iteratedDeriv_fun_add (hf.smooth.of_le (by exact_mod_cast hc))
    (hg.smooth.of_le (by exact_mod_cast hc))]
  exact (abs_add_le _ _).trans (add_le_add (hf.bound c hc) (hg.bound c hc))

theorem const_mul {A k : ℝ} {f : ℝ → ℝ} (hf : C2BoundAt A f k) (a : ℝ) :
    C2BoundAt (|a| * A) (fun t => a*f t) k := by
  refine ⟨mul_nonneg (abs_nonneg _) hf.nonneg, contDiffAt_const.mul hf.smooth, ?_⟩
  intro c hc
  rw [iteratedDeriv_const_mul_field, abs_mul]
  exact mul_le_mul_of_nonneg_left (hf.bound c hc) (abs_nonneg a)

theorem mul {A B k : ℝ} {f g : ℝ → ℝ}
    (hf : C2BoundAt A f k) (hg : C2BoundAt B g k) :
    C2BoundAt (4*A*B) (fun t => f t*g t) k := by
  have hA := hf.nonneg
  have hB := hg.nonneg
  refine ⟨by positivity, hf.smooth.mul hg.smooth, ?_⟩
  intro c hc
  have he := iteratedDeriv_mul (hf.smooth.of_le (by exact_mod_cast hc))
    (hg.smooth.of_le (by exact_mod_cast hc))
  change iteratedDeriv c (fun t => f t*g t) k = _ at he
  rw [he]
  calc
    _ ≤ ∑ i ∈ Finset.range (c+1),
        |(c.choose i : ℝ)*iteratedDeriv i f k*iteratedDeriv (c-i) g k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (c+1), (c.choose i : ℝ)*A*B := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ c := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hf.bound i (hi'.trans hc))
        (Nat.cast_nonneg _)) (hg.bound (c-i) (by omega)) (abs_nonneg _) (by positivity)
    _ ≤ 4*A*B := by
      interval_cases c <;> norm_num [Finset.sum_range_succ] <;>
        nlinarith only [mul_nonneg hf.nonneg hg.nonneg]

theorem sum {ι : Type*} (s : Finset ι) {A k : ℝ} {f : ι → ℝ → ℝ}
    (_hA : 0 ≤ A) (hf : ∀ i ∈ s, C2BoundAt A (f i) k) :
    C2BoundAt ((s.card:ℝ)*A) (fun t => ∑ i ∈ s, f i t) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, zero_mul, abs_zero] using
      const 0 k
  | @insert i s hi ih =>
    have hhead := hf i (Finset.mem_insert_self _ _)
    have htail := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    convert hhead.add htail using 1 <;>
      simp only [Finset.sum_insert hi, Finset.card_insert_of_notMem hi, Nat.cast_add,
        Nat.cast_one, add_mul, one_mul]
    ring

end C2BoundAt

local notation "E" => (Fin 3 → ℝ)

private theorem interpolatedMass_c2BoundAt {C h k a lam : ℝ} {m : ℝ → ℝ}
    (hC : 0 ≤ C) (_hh : 0 ≤ h) (hh1 : h ≤ 1)
    (ha : a ∈ Icc (0:ℝ) 1) (hlam : lam ∈ Icc (0:ℝ) 1)
    (hm : ContDiffAt ℝ 2 m k) (hm0 : m k ∈ Icc (0:ℝ) 1)
    (hm1 : |deriv m k| ≤ C*h) (hm2 : |deriv (deriv m) k| ≤ C*h) :
    C2BoundAt (C+2) (fun t => (1-lam)*a+lam*m t) k := by
  have hm' : C2BoundAt (C+1) m k := by
    refine ⟨by positivity,hm,?_⟩
    intro c hc
    interval_cases c
    · simpa only [iteratedDeriv_zero,abs_of_nonneg hm0.1] using hm0.2.trans (by linarith : (1:ℝ)≤C+1)
    · simpa only [iteratedDeriv_one] using hm1.trans
        ((mul_le_of_le_one_right hC hh1).trans (by linarith : C≤C+1))
    · simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hm2.trans
        ((mul_le_of_le_one_right hC hh1).trans (by linarith : C≤C+1))
  have H := (C2BoundAt.const ((1-lam)*a) k).add (hm'.const_mul lam)
  apply H.mono
  rw [abs_mul,abs_of_nonneg (by linarith [hlam.2] : 0≤1-lam),abs_of_nonneg ha.1,
    abs_of_nonneg hlam.1]
  have hleft : (1-lam)*a ≤ 1 :=
    (mul_le_mul_of_nonneg_left ha.2 (by linarith [hlam.2] : 0≤1-lam)).trans (by linarith [hlam.1])
  have hright : lam*(C+1) ≤ C+1 := mul_le_of_le_one_left (by positivity) hlam.2
  linarith

theorem c2BoundAt_coordinate {L k : ℝ} {v : ℝ → E}
    (hL : 0 ≤ L) (hv : ContDiffAt ℝ 2 v k)
    (hb : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c v k‖ ≤ L) (i : Fin 3) :
    C2BoundAt L (fun t => v t i) k := by
  refine ⟨hL, (contDiffAt_pi.mp hv) i, ?_⟩
  intro c hc
  have he : iteratedDeriv c (fun t => v t i) k = iteratedDeriv c v k i := by
    simp only [iteratedDeriv_eq_iteratedFDeriv]
    have H := (ContinuousLinearMap.proj i : E →L[ℝ] ℝ).iteratedFDeriv_comp_left
      (hv.of_le (by exact_mod_cast hc)) le_rfl
    exact congrArg (fun T => T (fun _ : Fin c => (1:ℝ))) H
  rw [he]
  exact (norm_le_pi_norm (iteratedDeriv c v k) i).trans (hb c hc)

theorem KStabilityInputs.innerChain_increment_c2BoundAt
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ} (hK : KStabilityInputs β α I) :
    ∃ B h0 kap : ℝ, 0≤B ∧ 0<h0 ∧ 0<kap ∧
      ∀ r ∈ I, ∀ h : ℝ, 0<h → h≤h0 → ∀ N : ℕ, 1≤N →
        ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N), ∀ x : E,
          let F := fun t => vectorIncrementChain
            ((massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N) lam).drop (j.val+1))
            (massVariationTerminal β α (r-h) h) x
          ∀ k : ℝ, |k|≤kap → C2BoundAt (B*h) (fun t => F t-F 0) k := by
  obtain ⟨B,h0,kap,hB,hh0,hkap,hK⟩ := hK
  refine ⟨B,h0,min kap 1,hB,hh0,lt_min hkap (by norm_num),?_⟩
  intro r hr h hh hh0' N hN lam hlam j x
  obtain ⟨hjets,hregular⟩ := hK r hr h hh hh0' N hN lam hlam
  let F := fun t => vectorIncrementChain
    ((massPath (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N) lam).drop (j.val+1))
    (massVariationTerminal β α (r-h) h) x
  change ∀ k : ℝ, |k| ≤ min kap 1 → C2BoundAt (B*h) (fun t => F t-F 0) k
  have hF (t : ℝ) (ht : |t|≤kap) : ContDiffAt ℝ 2 F t := by
    have H := (hregular j.val j.isLt 0 (by norm_num) t ht x).comp t
      (contDiffAt_id.prodMk (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ => x) t))
    have H' := (continuousMultilinearCurryFin0 ℝ E ℝ).contDiff.contDiffAt.comp t H
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,id_eq,
      LinearIsometryEquiv.apply_symm_apply] using H'
  have hbound (t : ℝ) (ht : |t|≤kap) (c : ℕ) (hc : c=1 ∨ c=2) :
      |iteratedDeriv c F t|≤B*h := by
    have hj : j.val < (windowMassPath β α (α (r-h)) (1/2) (r-h) h t N).length := by
      rw [windowMassPath_length]
      exact j.isLt
    exact (hjets t ht j.val hj c hc).abs_le x
  intro k hk
  have hkK : |k|≤kap := hk.trans (min_le_left _ _)
  refine ⟨mul_nonneg hB hh.le,(hF k hkK).sub contDiffAt_const,?_⟩
  intro c hc
  by_cases hc0 : c=0
  · subst c
    have hsegment (t : ℝ) (ht : t∈uIcc (0:ℝ) k) : |t|≤kap := by
      have Ht : |t|≤|k| := by simpa only [sub_zero] using abs_sub_left_of_mem_uIcc ht
      exact Ht.trans hkK
    have H := (convex_uIcc (0:ℝ) k).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => ((hF t (hsegment t ht)).differentiableAt (by norm_num)).hasDerivAt.hasDerivWithinAt)
      (C := B*h) (by
        intro t ht
        simpa only [Real.norm_eq_abs,← iteratedDeriv_one] using
          hbound t (hsegment t ht) 1 (Or.inl rfl))
      (left_mem_uIcc : (0:ℝ)∈uIcc (0:ℝ) k) (right_mem_uIcc : k∈uIcc (0:ℝ) k)
    have H' : |F k-F 0|≤B*h*|k| := by
      simpa only [Real.norm_eq_abs,sub_zero] using H
    exact H'.trans (mul_le_of_le_one_right (mul_nonneg hB hh.le)
      (hk.trans (min_le_right _ _)))
  · rw [iteratedDeriv_fun_sub ((hF k hkK).of_le (by exact_mod_cast hc))
      (contDiffAt_const : ContDiffAt ℝ c (fun _ : ℝ => F 0) k)]
    simp only [iteratedDeriv_const,hc0,ite_false,sub_zero]
    exact hbound k hkK c (by omega)

theorem c2BoundAt_pathEnergySelfInteraction {L M k : ℝ}
    {v : ℝ → E} {m : ℝ → ℝ} (hL : 0 ≤ L)
    (hv : ContDiffAt ℝ 2 v k)
    (hvb : ∀ c : ℕ, c ≤ 2 → ‖iteratedDeriv c v k‖ ≤ L)
    (hm : C2BoundAt M m k) (u chi d : ℝ) :
    C2BoundAt ((576*|u*d|+13824*M*|u^2*chi|)*L^4)
      (fun t => pathEnergySelfInteraction 1 u chi d (m t) (v t)) k := by
  have hcoord (i : Fin 3) := c2BoundAt_coordinate hL hv hvb i
  have hsum : C2BoundAt (3*L) (fun t => pathCoordinateSum (v t)) k := by
    simpa only [pathCoordinateSum, Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat] using
      C2BoundAt.sum Finset.univ hL (fun i _ => hcoord i)
  have hsq (i : Fin 3) : C2BoundAt (4*L^2) (fun t => (v t i)^2) k := by
    convert (hcoord i).mul (hcoord i) using 1
    · ring
    · funext t
      ring
  have hcube (i : Fin 3) : C2BoundAt (16*L^3) (fun t => (v t i)^3) k := by
    convert (hsq i).mul (hcoord i) using 1
    · ring
    · funext t
      ring
  have hsqsum : C2BoundAt (12*L^2) (fun t => ∑ i, (v t i)^2) k := by
    convert C2BoundAt.sum Finset.univ (by positivity : 0 ≤ 4*L^2) (fun i _ => hsq i) using 1
    norm_num
    ring
  have hcubesum : C2BoundAt (48*L^3) (fun t => ∑ i, (v t i)^3) k := by
    convert C2BoundAt.sum Finset.univ (by positivity : 0 ≤ 16*L^3) (fun i _ => hcube i) using 1
    norm_num
    ring
  have hsumSq := hsum.mul hsum
  have hfirst := (hsum.mul hcubesum).const_mul (u*d)
  have hsecond := ((hm.mul hsumSq).mul hsqsum).const_mul (2*u^2*chi)
  convert hfirst.add hsecond using 1
  · have he : |2*u^2*chi| = 2*|u^2*chi| := by
      rw [show 2*u^2*chi = 2*(u^2*chi) by ring, abs_mul]
      norm_num
    rw [he]
    ring
  · funext t
    dsimp only [pathEnergySelfInteraction]
    ring

theorem scalarData_windowSelfInteraction_c2BoundAt {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0<l) (hlu : l≤u) (hu : u<D.q) :
    ∃ K h0 : ℝ, 0≤K ∧ 0<h0 ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0<h → h≤h0 → ∀ N : ℕ, 1≤N →
        ∀ lam ∈ Icc (0:ℝ) 1,
          ∀ p ∈ windowKCurves β (interpolatedProfile (cdf (D.μ : Measure ℝ))
            (cdf (D.μ : Measure ℝ) (r-h)) lam) (r-h) h N,
            ∀ z k : ℝ, |k|≤1/2 →
              C2BoundAt (K*h^2/(N:ℝ)^2)
                (fun t => pathEnergySelfInteraction 1
                  (jet β (cdf (D.μ : Measure ℝ)) 1 ((r-h)+4*h) z)
                  (jet β (cdf (D.μ : Measure ℝ)) 2 ((r-h)+4*h) z)
                  (jet β (cdf (D.μ : Measure ℝ)) 3 ((r-h)+4*h) z)
                  (p t).1 (p t).2) k := by
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  obtain ⟨C,hP,hC,hhP,hparam⟩ := scalarData_window_parameter_budget D hl hlu hu
  let T := scalarTerminalJetBound D 3
  let M := C+2
  let A := 576*T^2+13824*M*T^3
  have hT : 0≤T := scalarTerminalJetBound_nonneg D _
  have hM : 0≤M := by dsimp only [M]; positivity
  have hA : 0≤A := by dsimp only [A]; positivity
  refine ⟨A*C^4*β^4,min hP (kStabilityInteriorRadius D.q l u),by positivity,
    lt_min hhP (kStabilityInteriorRadius_pos hl hu),?_⟩
  intro r hr h hh hh0 N hN lam hlam p hp z k hk
  have hhP' : h≤hP := hh0.trans (min_le_left _ _)
  have hhI : h≤kStabilityInteriorRadius D.q l u := hh0.trans (min_le_right _ _)
  have hh1 : h≤1 := hhI.trans (min_le_left _ _)
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  obtain ⟨σ,hσ,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨j,hj,hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hp
  let x := (j:ℝ)/(N:ℝ)
  let p0 : ℝ → ℝ × E := fun t =>
    (kStageMass α (r-h) h x σ t,
      (β*Real.sqrt (h/(N:ℝ))) • kDirectionShape i t)
  have hp0 : p0 ∈ windowKCurves β α (r-h) h N := by
    apply List.mem_flatMap.mpr
    refine ⟨σ,hσ,List.mem_flatMap.mpr ⟨j,hj,?_⟩⟩
    exact List.mem_map.mpr ⟨i,hi,rfl⟩
  obtain ⟨hp0c,hm1,hm2,hv0,hv1,hv2⟩ := hparam r hr h hh hhP' N hN p0 hp0 k hk
  have hc : 1≤kStageMassDivisor σ := by
    fin_cases σ <;> norm_num [kStageMassDivisor]
  have hc0 : 0<kStageMassDivisor σ := by linarith
  have hm0 : (p0 k).1 ∈ Icc (0:ℝ) 1 := by
    constructor
    · exact div_nonneg (cdf_nonneg _ _) hc0.le
    · exact (div_le_self (cdf_nonneg _ _) hc).trans (cdf_le_one _ _)
  have ha : α (r-h)/kStageMassDivisor σ ∈ Icc (0:ℝ) 1 :=
    ⟨div_nonneg (cdf_nonneg _ _) hc0.le,
      (div_le_self (cdf_nonneg _ _) hc).trans (cdf_le_one _ _)⟩
  have he : kStageMass (interpolatedProfile α (α (r-h)) lam) (r-h) h x σ =
      fun t => (1-lam)*(α (r-h)/kStageMassDivisor σ)+lam*(p0 t).1 := by
    funext t
    dsimp only [kStageMass,quadraticGridMass,interpolatedProfile,p0]
    ring
  have hm : C2BoundAt M
      (kStageMass (interpolatedProfile α (α (r-h)) lam) (r-h) h x σ) k := by
    rw [he]
    exact interpolatedMass_c2BoundAt hC.le hh.le hh1 ha hlam hp0c.fst hm0 hm1 hm2
  have hvb (c : ℕ) (hcb : c≤2) :
      ‖iteratedDeriv c (fun t => (p0 t).2) k‖≤C*|β| * Real.sqrt (h/(N:ℝ)) := by
    interval_cases c
    · exact hv0
    · simpa only [iteratedDeriv_one] using hv1
    · simpa only [iteratedDeriv_succ,iteratedDeriv_zero] using hv2
  have H := c2BoundAt_pathEnergySelfInteraction (by positivity : 0≤C*|β| * Real.sqrt (h/(N:ℝ)))
    hp0c.snd hvb hm (jet β α 1 ((r-h)+4*h) z) (jet β α 2 ((r-h)+4*h) z)
      (jet β α 3 ((r-h)+4*h) z)
  have ht : (r-h)+4*h ∈ Icc (0:ℝ) 1 := by
    have Ht := kStability_time_mem hr hh.le hhI (show (4:ℝ)∈Icc (0:ℝ) 4 by norm_num)
    constructor <;> linarith [Ht.1,Ht.2,D.q_mem.2]
  have hjet (c : ℕ) (hc1 : 1≤c) (hc3 : c≤3) : |jet β α c ((r-h)+4*h) z|≤T :=
    scalarData_jet_le D hc1 hc3 ht z
  have hud : |jet β α 1 ((r-h)+4*h) z*jet β α 3 ((r-h)+4*h) z|≤T^2 := by
    rw [abs_mul]
    exact (mul_le_mul (hjet 1 (by norm_num) (by norm_num))
      (hjet 3 (by norm_num) (by norm_num)) (abs_nonneg _) hT).trans_eq (by ring)
  have huc : |jet β α 1 ((r-h)+4*h) z^2*jet β α 2 ((r-h)+4*h) z|≤T^3 := by
    rw [abs_mul,abs_pow]
    exact (mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hjet 1 (by norm_num) (by norm_num)) 2)
      (hjet 2 (by norm_num) (by norm_num)) (abs_nonneg _) (sq_nonneg _)).trans_eq (by ring)
  apply H.mono
  calc
    _ ≤ A*(C*|β| * Real.sqrt (h/(N:ℝ)))^4 := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by positivity) 4)
      exact add_le_add (mul_le_mul_of_nonneg_left hud (by norm_num))
        (mul_le_mul_of_nonneg_left huc (by positivity))
    _ = _ := by
      have hs : Real.sqrt (h/(N:ℝ))^4 = (h/(N:ℝ))^2 := by
        rw [show (4:ℕ)=2*2 from rfl,pow_mul,Real.sq_sqrt (div_nonneg hh.le hn.le)]
      have hb : |β|^4=β^4 := by
        calc
          _ = (|β|^2)^2 := by ring
          _ = (β^2)^2 := by rw [sq_abs]
          _ = _ := by ring
      rw [mul_pow,mul_pow,hs,hb]
      ring

def orderedWindowCurve (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) : ℝ → ℝ × E :=
  (windowKCurves β (interpolatedProfile α a lam) s h N).get
    ⟨j.val,by rw [windowKCurves_length]; exact j.isLt⟩

theorem orderedWindowCurve_mem (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) :
    orderedWindowCurve β α a s h N lam j ∈
      windowKCurves β (interpolatedProfile α a lam) s h N := by
  exact List.get_mem _ _

theorem orderedWindowCurve_apply (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (hh : 0≤h) (k : ℝ) :
    orderedWindowCurve β α a s h N lam j k =
      (windowEntryMass β α a (1/2) s h k N lam (windowEntryIndex β α a (1/2) s h k N j),
        ((windowMassPath β α a (1/2) s h k N).get
          (windowEntryIndex β α a (1/2) s h k N j)).2.2) := by
  have H := congrArg (fun l : List (ℝ × E) => l.getD j.val (0,0))
    (windowKCurves_apply β (interpolatedProfile α a lam) s h k N hh)
  rw [← massPath_window_eq β α a lam (1/2) s h k N] at H
  have hc : j.val < ((windowKCurves β (interpolatedProfile α a lam) s h N).map
      (fun p => p k)).length := by
    rw [List.length_map,windowKCurves_length]
    exact j.isLt
  have hm : j.val < (massPath (windowMassPath β α a (1/2) s h k N) lam).length := by
    rw [massPath,List.length_map,windowMassPath_length]
    exact j.isLt
  rw [List.getD_eq_getElem _ _ hc,List.getD_eq_getElem _ _ hm] at H
  simpa only [List.getElem_map,orderedWindowCurve,List.get_eq_getElem,massPath,
    windowEntryMass,windowEntryIndex] using H

def orderedPathSelfInteraction (β : ℝ) (α : ℝ → ℝ) (a p s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (z k : ℝ) : ℝ :=
  let jj := windowEntryIndex β α a p s h k N j
  pathEnergySelfInteraction 1 (jet β α 1 (s+4*h) z) (jet β α 2 (s+4*h) z)
    (jet β α 3 (s+4*h) z) (windowEntryMass β α a p s h k N lam jj)
    ((windowMassPath β α a p s h k N).get jj).2.2

theorem scalarData_orderedPathSelfInteraction_c2BoundAt {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0<l) (hu : u<D.q) :
    ∃ K h0 : ℝ, 0≤K ∧ 0<h0 ∧
      ∀ r ∈ Icc l u, ∀ h : ℝ, 0<h → h≤h0 → ∀ N : ℕ, 1≤N →
        ∀ lam ∈ Icc (0:ℝ) 1, ∀ z : ℝ, ∀ j : Fin (12*N),
          ∀ k : ℝ, |k|≤1/2 →
            C2BoundAt (K*h^2/(N:ℝ)^2)
              (orderedPathSelfInteraction β (cdf (D.μ : Measure ℝ))
                (cdf (D.μ : Measure ℝ) (r-h)) (1/2) (r-h) h N lam j z) k := by
  by_cases hlu : l≤u
  swap
  · refine ⟨0,1,le_rfl,by norm_num,?_⟩
    intro r hr
    exact (hlu (hr.1.trans hr.2)).elim
  obtain ⟨K,h0,hK,hh0,hself⟩ := scalarData_windowSelfInteraction_c2BoundAt D hl hlu hu
  refine ⟨K,h0,hK,hh0,?_⟩
  intro r hr h hh hh0' N hN lam hlam z j k hk
  have H := hself r hr h hh hh0' N hN lam hlam
    (orderedWindowCurve β (cdf (D.μ : Measure ℝ)) (cdf (D.μ : Measure ℝ) (r-h))
      (r-h) h N lam j) (orderedWindowCurve_mem _ _ _ _ _ _ _ _) z k hk
  have he : orderedPathSelfInteraction β (cdf (D.μ : Measure ℝ))
      (cdf (D.μ : Measure ℝ) (r-h)) (1/2) (r-h) h N lam j z =
      fun t => pathEnergySelfInteraction 1
        (jet β (cdf (D.μ : Measure ℝ)) 1 ((r-h)+4*h) z)
        (jet β (cdf (D.μ : Measure ℝ)) 2 ((r-h)+4*h) z)
        (jet β (cdf (D.μ : Measure ℝ)) 3 ((r-h)+4*h) z)
        (orderedWindowCurve β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h N lam j t).1
        (orderedWindowCurve β (cdf (D.μ : Measure ℝ))
          (cdf (D.μ : Measure ℝ) (r-h)) (r-h) h N lam j t).2 := by
    funext t
    rw [orderedWindowCurve_apply _ _ _ _ _ _ _ _ hh.le]
    rfl
  rw [he]
  exact H

theorem entropyPathRemainder_value_quartic_of_entropyInputs
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ} (hA : UniformWindowEntropyInputs β α I) :
    ∃ K h0 kap : ℝ, 0 ≤ K ∧ 0 < h0 ∧ 0 < kap ∧
      ∀ r ∈ I, ∀ h : ℝ, 0 < h → h ≤ h0 → ∀ᶠ N : ℕ in atTop,
        ∀ lam ∈ Icc (0:ℝ) 1, ∀ z : ℝ, ∀ j : Fin (12*N),
          ∀ k : ℝ, |k| ≤ kap →
            |entropyPathRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z k| ≤
              K*h^2/(N:ℝ)^2 := by
  obtain ⟨B,a0,D,h0,kap,hB,ha0,hD,hh0,hkap,hA⟩ := hA
  let K := 2*B*StepCalculus.pathExpansionConstant B/a0
  have hK : 0 ≤ K := div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) hB)
      (StepCalculus.pathExpansionConstant_nonneg hB)) ha0.le
  refine ⟨K*D^2,h0,kap,by positivity,hh0,hkap,?_⟩
  intro r hr h hh hh0'
  have hlim : Tendsto (fun N : ℕ => D*h/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1)),
    eventually_ge_atTop (1:ℕ)] with N hsmall hN
  intro lam hlam z j k hk
  obtain ⟨hf,hjets⟩ := hA r hr h hh hh0' k hk N hN
  obtain ⟨hinner,hstep⟩ := hjets lam hlam
  let jj := windowEntryIndex β α (α (r-h)) (1/2) (r-h) h k N j
  let v := ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get jj).2.2
  have hinner' : QPotential 4 B (vectorIncrementChain
      (massPath ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).drop (jj.val+1)) lam)
      (massVariationTerminal β α (r-h) h)) := by
    simpa only [massPath, List.map_drop] using (hinner jj.val jj.isLt).of_le (by norm_num : 4≤10)
  have hdir : ‖v‖^2 ≤ D*h/(N:ℝ) := (hstep jj).2
  have hv : ‖v‖ ≤ 1 := by nlinarith [norm_nonneg v]
  have H := massPathSensitivity_first_order _ hf lam jj hinner' ha0 (hstep jj).1 hv (fun _ => z)
  change |entropyPathRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z k| ≤ K*‖v‖^4 at H
  have hfour : ‖v‖^4 ≤ (D*h/(N:ℝ))^2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hdir 2
  exact H.trans ((mul_le_mul_of_nonneg_left hfour hK).trans_eq (by ring))

def orderedPathExpansionRemainder (β : ℝ) (α : ℝ → ℝ) (a p s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (z k : ℝ) : ℝ :=
  let jj := windowEntryIndex β α a p s h k N j
  let l := massPath (windowMassPath β α a p s h k N) lam
  (windowGradientEnergy β α a p s h k N lam jj z-
    StepCalculus.firstOrderPathEnergy (l.take j.val) (l.drop (j.val+1))
      (massVariationTerminal β α s h)
      ((windowMassPath β α a p s h k N).get jj).2.2 (fun _ => z))/2

private theorem selfInteraction_scaled (β u chi d m : ℝ) (v : E) :
    pathEnergySelfInteraction (β^2) u chi d m v =
      pathEnergySelfInteraction 1 u chi d m (β • v) := by
  simp only [pathEnergySelfInteraction,pathCoordinateSum,Pi.smul_apply,smul_eq_mul,mul_pow,
    ← Finset.mul_sum,one_pow,one_mul]
  ring

theorem orderedPathEnergyRemainder_eq_expansion_sub_self
    (β : ℝ) (α : ℝ → ℝ) (a s h : ℝ) {N : ℕ} (hN : 0<N)
    (lam : ℝ) (j : Fin (12*N)) (z k : ℝ) (hh : 0≤h) (hk : |k|≤1/2)
    (hφ : ContDiff ℝ 5 (Phi β α (s+4*h))) :
    orderedPathEnergyRemainder β α a (1/2) s h N lam j z k =
      orderedPathExpansionRemainder β α a (1/2) s h N lam j z k-
        orderedPathSelfInteraction β α a (1/2) s h N lam j z k/2 := by
  let jj := windowEntryIndex β α a (1/2) s h k N j
  have H := firstOrderPathEnergy_window_eq β α a (1/2) s h k
    hN hh (by norm_num) (OW.repairLength_mem (by norm_num) hk) lam z hφ jj
  dsimp only at H
  rw [selfInteraction_scaled] at H
  have hv : β • windowRawDirection β α a (1/2) s h k N jj =
      ((windowMassPath β α a (1/2) s h k N).get jj).2.2 := by
    symm
    rw [List.get_eq_getElem]
    unfold windowRawDirection
    rw [List.get_eq_getElem]
    simp only [windowMassPath,List.getElem_map]
  rw [hv] at H
  dsimp only [orderedPathEnergyRemainder,orderedPathExpansionRemainder,
    orderedPathSelfInteraction,jj,windowEntryIndex] at H ⊢
  rw [H]
  ring

def FirstOrderPathEnergyC2 (β : ℝ) (α : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∃ C h0 kap : ℝ, 0≤C ∧ 0<h0 ∧ 0<kap ∧
    ∀ r ∈ I, ∀ h : ℝ, 0<h → h≤h0 → ∀ᶠ N : ℕ in atTop,
      ∀ lam ∈ Icc (0:ℝ) 1, ∀ z : ℝ, ∀ j : Fin (12*N),
        ∀ k : ℝ, |k|≤kap →
          let R := orderedPathExpansionRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z
          ContDiffAt ℝ 2 R k ∧ |iteratedDeriv 2 R k|≤C*h^3/(N:ℝ)

theorem pathEnergyC2_of_firstOrderPathEnergyC2 {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0<l) (hu : u<D.q)
    (hfirst : FirstOrderPathEnergyC2 β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    PathEnergyC2 β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  let α : ℝ → ℝ := cdf (D.μ : Measure ℝ)
  obtain ⟨C,hP,kap,hC,hhP,hkap,hfirst⟩ := hfirst
  obtain ⟨K,hS,hK,hhS,hself⟩ := scalarData_orderedPathSelfInteraction_c2BoundAt D hl hu
  let h0 := min hP (min hS (kStabilityInteriorRadius D.q l u))
  refine ⟨C,h0,min kap (1/4),hC,
    lt_min hhP (lt_min hhS (kStabilityInteriorRadius_pos hl hu)),
    lt_min hkap (by norm_num),?_⟩
  intro r hr h hh hh0 eps heps
  have hhP' : h≤hP := hh0.trans (min_le_left _ _)
  have hhS' : h≤hS := hh0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhI : h≤kStabilityInteriorRadius D.q l u :=
    hh0.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hh1 : h≤1 := hhI.trans (min_le_left _ _)
  have ht : (r-h)+4*h ∈ Icc (0:ℝ) 1 := by
    have H := kStability_time_mem hr hh.le hhI (show (4:ℝ)∈Icc (0:ℝ) 4 by norm_num)
    constructor <;> linarith [H.1,H.2,D.q_mem.2]
  have hφ : ContDiff ℝ 5 (Phi β α ((r-h)+4*h)) :=
    (scalarData_phi_contDiff D ht).of_le (by simp)
  have hlim : Tendsto (fun N : ℕ => K*h^2/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [hfirst r hr h hh hhP',
    hlim.eventually (eventually_le_nhds heps),eventually_ge_atTop (1:ℕ)] with N hfirstN hsmall hN
  intro lam hlam z j k hk
  let R := orderedPathExpansionRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z
  let S := orderedPathSelfInteraction β α (α (r-h)) (1/2) (r-h) h N lam j z
  let P := orderedPathEnergyRemainder β α (α (r-h)) (1/2) (r-h) h N lam j z
  obtain ⟨hRc,hRb⟩ := hfirstN lam hlam z j k (hk.trans (min_le_left _ _))
  have hkhalf : |k|≤1/2 := (hk.trans (min_le_right _ _)).trans (by norm_num)
  have hSjet := hself r hr h hh hhS' N hN lam hlam z j k hkhalf
  have he : P =ᶠ[𝓝 k] (fun t => R t-S t/2) := by
    have hkh : |k|<1/2 := lt_of_le_of_lt (hk.trans (min_le_right _ _)) (by norm_num)
    filter_upwards [continuous_abs.continuousAt.eventually (gt_mem_nhds hkh)] with t ht'
    exact orderedPathEnergyRemainder_eq_expansion_sub_self β α (α (r-h)) (r-h) h
      (by omega) lam j z t hh.le ht'.le hφ
  have hSc : ContDiffAt ℝ 2 (fun t => S t/2) k := hSjet.smooth.div_const 2
  have hPc : ContDiffAt ℝ 2 P k := (hRc.sub hSc).congr_of_eventuallyEq he
  refine ⟨hPc,?_⟩
  rw [he.iteratedDeriv_eq 2,iteratedDeriv_fun_sub hRc hSc]
  have hSder : |iteratedDeriv 2 (fun t => S t/2) k|≤K*h^2/(N:ℝ)^2 := by
    have heS : (fun t => S t/2) = fun t => (1/2:ℝ)*S t := by funext t; ring
    rw [heS,iteratedDeriv_const_mul_field,abs_mul]
    norm_num
    exact (mul_le_mul_of_nonneg_left (hSjet.bound 2 le_rfl) (by norm_num : (0:ℝ)≤1/2)).trans
      (mul_le_of_le_one_left (by positivity) (by norm_num))
  have hn : (0:ℝ)<N := Nat.cast_pos.mpr hN
  have hSsmall : K*h^2/(N:ℝ)^2≤eps/(N:ℝ) := by
    have H := (div_le_div_iff_of_pos_right hn).mpr hsmall
    simpa only [div_div,← pow_two] using H
  have hsqrt : h≤Real.sqrt h := by
    nlinarith [Real.sq_sqrt hh.le,Real.sqrt_nonneg h,
      mul_le_of_le_one_right hh.le hh1]
  have hmain : C*h^3/(N:ℝ)≤C*(Real.sqrt h*h^2)/(N:ℝ) := by
    apply div_le_div_of_nonneg_right _ hn.le
    have H := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsqrt (sq_nonneg h)) hC
    convert H using 1
    ring
  exact (abs_sub _ _).trans (add_le_add (hRb.trans hmain) (hSder.trans hSsmall))

theorem massSensitivityC2_of_differentiatedExpansions {β : ℝ} (D : ScalarData β)
    {l u : ℝ} (hl : 0<l) (hu : u<D.q)
    (hfirst : FirstOrderPathEnergyC2 β (cdf (D.μ : Measure ℝ)) (Icc l u))
    (hentropy : EntropyPathC2Small β (cdf (D.μ : Measure ℝ)) (Icc l u)) :
    MassSensitivityC2 β (cdf (D.μ : Measure ℝ)) (Icc l u) := by
  exact massSensitivityC2_of_pathEnergyC2_of_entropyPathC2Small
    (pathEnergyC2_of_firstOrderPathEnergyC2 D hl hu hfirst) hentropy

end SKBarriers2.Corner

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def tiltedGeneratorDefect (m : ℝ) (v : E) (f g : E → ℝ) (x : E) : ℝ :=
  tiltedAverage m v f g x-g x-pathGenerator m v f g x

private theorem directionalJet_mul_two {C D : ℝ} {g a : E → ℝ}
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 4 D a) (v x : E) :
    directionalJet v 2 (fun y => g y*a y) x =
      g x*directionalJet v 2 a x+a x*directionalJet v 2 g x+
        2*fderiv ℝ g x v*fderiv ℝ a x v := by
  have hgc : Differentiable ℝ g := hg.smooth.differentiable (by norm_num)
  have hac : Differentiable ℝ a := ha.smooth.differentiable (by norm_num)
  have hdg := hg.derivativeJets.apply_const v
  have hda := ha.derivativeJets.apply_const v
  have hdgc : Differentiable ℝ (fun y => fderiv ℝ g y v) :=
    hdg.smooth.differentiable (by norm_num)
  have hdac : Differentiable ℝ (fun y => fderiv ℝ a y v) :=
    hda.smooth.differentiable (by norm_num)
  have he : directionalJet v 1 (fun y => g y*a y) =
      fun y => g y*fderiv ℝ a y v+a y*fderiv ℝ g y v := by
    funext y
    change fderiv ℝ (fun y => g y*a y) y v = _
    rw [fderiv_fun_mul (hgc y) (hac y)]
    rfl
  change fderiv ℝ (directionalJet v 1 (fun y => g y*a y)) x v = _
  rw [he,fderiv_fun_add
    (f := fun y => g y*fderiv ℝ a y v) (g := fun y => a y*fderiv ℝ g y v)
    ((hgc x).mul (hdac x)) ((hac x).mul (hdgc x)),
    fderiv_fun_mul (hgc x) (hdac x),fderiv_fun_mul (hac x) (hdgc x)]
  simp only [add_apply,smul_apply,smul_eq_mul,directionalJet]
  ring

theorem pathGenerator_mul {C D : ℝ} {g a : E → ℝ}
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 4 D a)
    (m : ℝ) (v : E) (f : E → ℝ) (x : E) :
    pathGenerator m v f (fun y => g y*a y) x =
      g x*pathGenerator m v f a x+a x*pathGenerator m v f g x+
        fderiv ℝ g x v*fderiv ℝ a x v := by
  rw [pathGenerator,directionalJet_mul_two hg ha,
    fderiv_fun_mul (hg.smooth.differentiable (by norm_num) x)
      (ha.smooth.differentiable (by norm_num) x)]
  simp only [add_apply,smul_apply,smul_eq_mul,pathGenerator]
  ring

theorem spatialCovariance_sub_gradient_eq_defects {C D : ℝ} {g a : E → ℝ}
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 4 D a)
    (m : ℝ) (v : E) (f : E → ℝ) (x : E) :
    spatialCovariance m v f g a x-fderiv ℝ g x v*fderiv ℝ a x v =
      tiltedGeneratorDefect m v f (fun y => g y*a y) x-
        g x*tiltedGeneratorDefect m v f a x-
        a x*tiltedGeneratorDefect m v f g x-
        (tiltedAverage m v f g x-g x)*(tiltedAverage m v f a x-a x) := by
  unfold tiltedGeneratorDefect spatialCovariance
  rw [pathGenerator_mul hg ha]
  ring

theorem abs_spatialCovariance_sub_gradient_le {r : ℕ} {B C D : ℝ}
    {f g a : E → ℝ} (hf : QPotential r B f) (hr : 4≤r)
    (hg : QBoundedJets 4 C g) (ha : QBoundedJets 4 D a)
    {m : ℝ} (hm : m∈Icc (0:ℝ) 1) (v x : E) (hv : ‖v‖≤1) :
    |spatialCovariance m v f g a x-fderiv ℝ g x v*fderiv ℝ a x v| ≤
      C*D*(18*pathExpansionConstant B+(1+B)^4)*‖v‖^4 := by
  have hB := hf.nonneg
  have hC := hg.nonneg
  have hD := ha.nonneg
  have hP := pathExpansionConstant_nonneg hB
  have hga : QBoundedJets 4 (16*C*D) (fun y => g y*a y) := by
    convert hg.mul ha using 1
    norm_num
  have hlocal {A : ℝ} {b : E → ℝ} (hb : QBoundedJets 4 A b) :
      |tiltedGeneratorDefect m v f b x|≤A*pathExpansionConstant B*‖v‖^4 := by
    have H := abs_noiseMean_generator_remainder_le hf (by omega)
      (qBoundedJets_iff_qBddSmooth.mp hb).potential (by norm_num) hm v x hv
    convert H using 1
    congr 1
    dsimp only [tiltedGeneratorDefect,pathGenerator,tiltedAverage,noiseMean]
    ring
  have hweak {A : ℝ} {b : E → ℝ} (hb : QBoundedJets 4 A b) :
      |tiltedAverage m v f b x-b x|≤A*(1+B)^2*‖v‖^2 :=
    abs_noiseMean_sub_le hf (by omega)
      (qBoundedJets_iff_qBddSmooth.mp hb).potential (by norm_num) hm v x hv
  have hgaR := hlocal hga
  have hgR := hlocal hg
  have haR := hlocal ha
  have hgweak := hweak hg
  have haweak := hweak ha
  have hg0 : |g x|≤C := by simpa only [Real.norm_eq_abs] using hg.norm_le x
  have ha0 : |a x|≤D := by simpa only [Real.norm_eq_abs] using ha.norm_le x
  rw [spatialCovariance_sub_gradient_eq_defects hg ha]
  calc
    _ ≤ |tiltedGeneratorDefect m v f (fun y => g y*a y) x|+
        |g x*tiltedGeneratorDefect m v f a x|+
        |a x*tiltedGeneratorDefect m v f g x|+
        |(tiltedAverage m v f g x-g x)*(tiltedAverage m v f a x-a x)| := by
      exact (abs_sub _ _).trans (add_le_add
        ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
    _ ≤ (16*C*D)*pathExpansionConstant B*‖v‖^4+
        C*(D*pathExpansionConstant B*‖v‖^4)+
        D*(C*pathExpansionConstant B*‖v‖^4)+
        (C*(1+B)^2*‖v‖^2)*(D*(1+B)^2*‖v‖^2) := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add hgaR
          rw [abs_mul]
          exact mul_le_mul hg0 haR (abs_nonneg _) hC
        · rw [abs_mul]
          exact mul_le_mul ha0 hgR (abs_nonneg _) hD
      · rw [abs_mul]
        exact mul_le_mul hgweak haweak (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem local_terminalTest_expSet {r : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 2≤r) (hg : QBoundedJets 4 C g) (m : ℝ) (v x : E) :
    integrableExpSet (fun t : ℝ => g (x+t • v)) (stepLaw m v f x) = univ := by
  let _ := stepLaw_probability hf hr m v x
  ext a
  simp only [mem_univ,iff_true]
  apply Integrable.of_bound
    (Real.continuous_exp.comp (continuous_const.mul
      (hg.smooth.continuous.comp (continuous_const.add
        (continuous_id.smul continuous_const))))).aestronglyMeasurable (Real.exp (|a| * C))
  apply ae_of_all
  intro t
  change ‖Real.exp (a*g (x+t • v))‖≤Real.exp (|a| * C)
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self _).trans ((abs_mul _ _).trans_le
    (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hg.norm_le (x+t • v))
      (abs_nonneg a)))

private theorem local_terminalStep_contDiff {r : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 2≤r) (hg : QBoundedJets 4 C g)
    {m : ℝ} (hm : m≠0) (v x : E) :
    ContDiff ℝ 2 (fun k : ℝ => vectorStep m v (fun y => f y+k*g y) x) := by
  have ht (a : ℝ) : a∈interior (integrableExpSet
      (fun t : ℝ => g (x+t • v)) (stepLaw m v f x)) := by
    rw [local_terminalTest_expSet hf hr hg,interior_univ]
    exact mem_univ a
  have hc : ContDiff ℝ 2 (cgf (fun t : ℝ => g (x+t • v)) (stepLaw m v f x)) :=
    contDiff_iff_contDiffAt.mpr (fun a => (analyticAt_cgf (ht a)).contDiffAt)
  rw [terminalTilt_step_eq_cgf hf hr (qBoundedJets_iff_qBddSmooth.mp hg) (by norm_num) hm]
  exact contDiff_const.add ((hc.comp (contDiff_const.mul contDiff_id)).div_const m)

private theorem local_terminalStep_second_deriv {r : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 2≤r) (hg : QBoundedJets 4 C g)
    {m : ℝ} (hm : m≠0) (v x : E) :
    iteratedDeriv 2 (fun k : ℝ => vectorStep m v (fun y => f y+k*g y) x) 0 =
      m*spatialCovariance m v f g g x := by
  rw [iteratedDeriv_succ,iteratedDeriv_one,
    terminalTilt_second_deriv hf hr (qBoundedJets_iff_qBddSmooth.mp hg) (by norm_num) hm v x,
    spatialCovariance_eq hf hr (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num)))
      (qBoundedJets_iff_qBddSmooth.mp (hg.of_le (by norm_num)))]

theorem abs_terminalStep_second_deriv_remainder_le {r : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 4≤r) (hg : QBoundedJets 4 C g)
    {m : ℝ} (hm : m∈Ioc (0:ℝ) 1) (v x : E) (hv : ‖v‖≤1) :
    |iteratedDeriv 2 (fun k : ℝ => vectorStep m v (fun y => f y+k*g y) x) 0-
      m*(fderiv ℝ g x v)^2| ≤
      C^2*(18*pathExpansionConstant B+(1+B)^4)*‖v‖^4 := by
  rw [local_terminalStep_second_deriv hf (by omega) hg hm.1.ne']
  have H := abs_spatialCovariance_sub_gradient_le hf hr hg hg ⟨hm.1.le,hm.2⟩ v x hv
  have hnonneg : 0≤C^2*(18*pathExpansionConstant B+(1+B)^4)*‖v‖^4 := by
    have hP := pathExpansionConstant_nonneg hf.nonneg
    positivity
  calc
    _ = |m| * |spatialCovariance m v f g g x-fderiv ℝ g x v*fderiv ℝ g x v| := by
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ m*(C^2*(18*pathExpansionConstant B+(1+B)^4)*‖v‖^4) := by
      rw [abs_of_pos hm.1]
      apply mul_le_mul_of_nonneg_left _ hm.1.le
      exact H.trans_eq (by ring)
    _ ≤ _ := mul_le_of_le_one_left hnonneg hm.2

def terminalStepTaylorDefect (m : ℝ) (v : E) (f g : E → ℝ) (x : E) (k : ℝ) : ℝ :=
  vectorStep m v (fun y => f y+k*g y) x-
    (f x+k*g x+m*(fderiv ℝ f x v+k*fderiv ℝ g x v)^2/2+
      (directionalJet v 2 f x+k*directionalJet v 2 g x)/2)

theorem terminalStepTaylorDefect_c2BoundAt {r : ℕ} {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential r B f) (hr : 4≤r) (hg : QBoundedJets 4 C g)
    {m : ℝ} (hm : m∈Ioc (0:ℝ) 1) (v x : E) (hv : ‖v‖≤1) :
    Corner.C2BoundAt
      ((B*pathExpansionConstant B+C*pathExpansionConstant B+
        C^2*(18*pathExpansionConstant B+(1+B)^4))*‖v‖^4)
      (terminalStepTaylorDefect m v f g x) 0 := by
  let P : ℝ → ℝ := fun k => f x+k*g x+m*(fderiv ℝ f x v+k*fderiv ℝ g x v)^2/2+
    (directionalJet v 2 f x+k*directionalJet v 2 g x)/2
  let D : ℝ → ℝ := fun k => g x+m*(fderiv ℝ f x v+k*fderiv ℝ g x v)*fderiv ℝ g x v+
    directionalJet v 2 g x/2
  have hP (k : ℝ) : HasDerivAt P (D k) k := by
    convert! ((((hasDerivAt_const k (f x)).add ((hasDerivAt_id k).mul_const (g x))).add
      (((((hasDerivAt_id k).mul_const (fderiv ℝ g x v)).const_add
        (fderiv ℝ f x v)).pow 2).const_mul m |>.div_const 2)).add
      (((((hasDerivAt_id k).mul_const (directionalJet v 2 g x)).const_add
        (directionalJet v 2 f x))).div_const 2)) using 1
    simp only [D,id_eq]
    ring
  have hD (k : ℝ) : HasDerivAt D (m*(fderiv ℝ g x v)^2) k := by
    convert! ((((((hasDerivAt_id k).mul_const (fderiv ℝ g x v)).const_add
      (fderiv ℝ f x v)).const_mul m).mul_const (fderiv ℝ g x v)).const_add (g x)).add_const
      (directionalJet v 2 g x/2) using 1
    ring
  have hPc : ContDiff ℝ 2 P := by dsimp only [P]; fun_prop
  have hTc := local_terminalStep_contDiff hf (by omega) hg hm.1.ne' v x
  have hP2 : iteratedDeriv 2 P 0 = m*(fderiv ℝ g x v)^2 := by
    rw [iteratedDeriv_succ,iteratedDeriv_one,show deriv P=D from funext (fun t => (hP t).deriv)]
    exact (hD 0).deriv
  have hBP : 0≤B*pathExpansionConstant B := mul_nonneg hf.nonneg
    (pathExpansionConstant_nonneg hf.nonneg)
  have hCP : 0≤C*pathExpansionConstant B := mul_nonneg hg.nonneg
    (pathExpansionConstant_nonneg hf.nonneg)
  have hCC : 0≤C^2*(18*pathExpansionConstant B+(1+B)^4) := by
    have hP0 := pathExpansionConstant_nonneg hf.nonneg
    positivity
  refine ⟨by positivity,hTc.contDiffAt.sub hPc.contDiffAt,?_⟩
  intro c hc
  interval_cases c
  · have H := abs_step_generator_remainder_le hf hr ⟨hm.1.le,hm.2⟩ v x hv
    have he : terminalStepTaylorDefect m v f g x 0 =
        vectorStep m v f x-f x-m*(fderiv ℝ f x v)^2/2-directionalJet v 2 f x/2 := by
      simp only [terminalStepTaylorDefect,zero_mul,add_zero]
      ring
    rw [iteratedDeriv_zero,he]
    exact H.trans (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (norm_nonneg v) 4))
  · have H := abs_terminal_tilt_deriv_remainder_le hf (by omega)
      (qBoundedJets_iff_qBddSmooth.mp hg) (by norm_num) hm v x hv
    have hd := (hasDerivAt_terminal_tilt hf (by omega)
      (qBoundedJets_iff_qBddSmooth.mp hg) (by norm_num) hm.1.ne' v x).sub (hP 0)
    change HasDerivAt (terminalStepTaylorDefect m v f g x) _ 0 at hd
    rw [iteratedDeriv_one,hd.deriv]
    have he : |noiseMean m v f x (fun t => g (x+t • v))-D 0| =
        |deriv (fun k : ℝ => vectorStep m v (fun y => f y+k*g y) x) 0-g x-
          m*fderiv ℝ f x v*fderiv ℝ g x v-directionalJet v 2 g x/2| := by
      rw [(hasDerivAt_terminal_tilt hf (by omega) (qBoundedJets_iff_qBddSmooth.mp hg)
        (by norm_num) hm.1.ne' v x).deriv]
      congr 1
      dsimp only [D]
      ring
    rw [he]
    exact H.trans (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (norm_nonneg v) 4))
  · change |iteratedDeriv 2 (fun k => vectorStep m v (fun y => f y+k*g y) x-P k) 0|≤_
    rw [iteratedDeriv_fun_sub hTc.contDiffAt hPc.contDiffAt,hP2]
    exact (abs_terminalStep_second_deriv_remainder_le hf hr hg hm v x hv).trans
      (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg (norm_nonneg v) 4))

end SKBarriers2.StepCalculus

namespace SKBarriers2.Corner

open SKBarriers2.StepCalculus
local notation "E" => (Fin 3 → ℝ)

def orderedInnerChain (β : ℝ) (α : ℝ → ℝ) (a p s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (k : ℝ) : E → ℝ :=
  vectorIncrementChain
    ((massPath (windowMassPath β α a p s h k N) lam).drop (j.val+1))
    (massVariationTerminal β α s h)

def orderedInnerVariation (β : ℝ) (α : ℝ → ℝ) (a p s h : ℝ) (N : ℕ)
    (lam : ℝ) (j : Fin (12*N)) (c : ℕ) (k : ℝ) (x : E) : ℝ :=
  iteratedDeriv c (fun t => orderedInnerChain β α a p s h N lam j t x) k

theorem KStabilityInputs.terminalVariation_remainders
    {β : ℝ} {α : ℝ → ℝ} {I : Set ℝ} (hK : KStabilityInputs β α I)
    (hA : UniformWindowEntropyInputs β α I) :
    ∃ K h0 kap : ℝ, 0≤K ∧ 0<h0 ∧ 0<kap ∧
      ∀ r ∈ I, ∀ h : ℝ, 0<h → h≤h0 → ∀ᶠ N : ℕ in atTop,
        ∀ lam ∈ Icc (0:ℝ) 1, ∀ j : Fin (12*N), ∀ k : ℝ, |k|≤kap → ∀ x : E,
          let jj := windowEntryIndex β α (α (r-h)) (1/2) (r-h) h k N j
          let m := windowEntryMass β α (α (r-h)) (1/2) (r-h) h k N lam jj
          let v := ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get jj).2.2
          let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
          let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
          (∀ c : ℕ, c=1 ∨ c=2 →
            |deriv (fun t : ℝ => vectorStep m v (fun y => F y+t*G c y) x) 0-G c x-
              m*fderiv ℝ F x v*fderiv ℝ (G c) x v-directionalJet v 2 (G c) x/2| ≤
                K*h^3/(N:ℝ)^2) ∧
          |iteratedDeriv 2 (fun t : ℝ => vectorStep m v (fun y => F y+t*G 1 y) x) 0-
            m*(fderiv ℝ (G 1) x v)^2| ≤ K*h^4/(N:ℝ)^2 := by
  obtain ⟨B,hK0,kapK,hB,hhK,hkapK,hK⟩ := hK
  obtain ⟨A,a0,D,hA0,kapA,hApos,ha0,hD,hhA,hkapA,hA⟩ := hA
  let P := pathExpansionConstant A
  let Q := 18*P+(1+A)^4
  let K1 := B*P*D^2
  let K2 := B^2*Q*D^2
  have hP : 0≤P := pathExpansionConstant_nonneg hApos
  have hQ : 0≤Q := by dsimp only [Q]; positivity
  have hK1 : 0≤K1 := by dsimp only [K1]; positivity
  have hK2 : 0≤K2 := by dsimp only [K2]; positivity
  refine ⟨K1+K2,min hK0 hA0,min kapK kapA,add_nonneg hK1 hK2,
    lt_min hhK hhA,lt_min hkapK hkapA,?_⟩
  intro r hr h hh hh0
  have hlim : Tendsto (fun N : ℕ => D*h/(N:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))] with N hN hsmall
  intro lam hlam j k hk x
  dsimp only
  let jj := windowEntryIndex β α (α (r-h)) (1/2) (r-h) h k N j
  let m := windowEntryMass β α (α (r-h)) (1/2) (r-h) h k N lam jj
  let v := ((windowMassPath β α (α (r-h)) (1/2) (r-h) h k N).get jj).2.2
  let F := orderedInnerChain β α (α (r-h)) (1/2) (r-h) h N lam j k
  let G := fun c => orderedInnerVariation β α (α (r-h)) (1/2) (r-h) h N lam j c k
  change (∀ c : ℕ, c=1 ∨ c=2 →
    |deriv (fun t : ℝ => vectorStep m v (fun y => F y+t*G c y) x) 0-G c x-
      m*fderiv ℝ F x v*fderiv ℝ (G c) x v-directionalJet v 2 (G c) x/2|≤
        (K1+K2)*h^3/(N:ℝ)^2) ∧
    |iteratedDeriv 2 (fun t : ℝ => vectorStep m v (fun y => F y+t*G 1 y) x) 0-
      m*(fderiv ℝ (G 1) x v)^2|≤(K1+K2)*h^4/(N:ℝ)^2
  obtain ⟨_,hAi⟩ := hA r hr h hh (hh0.trans (min_le_right _ _)) k
    (hk.trans (min_le_right _ _)) N hN
  obtain ⟨hinner,hentry⟩ := hAi lam hlam
  have hF : QPotential 4 A F := by
    simpa only [F,orderedInnerChain,massPath,List.map_drop,jj,windowEntryIndex] using
      (hinner jj.val jj.isLt).of_le (by norm_num : 4≤10)
  have hm : m∈Ioc (0:ℝ) 1 := ⟨ha0.trans_le (hentry jj).1.1,(hentry jj).1.2⟩
  have hdir : ‖v‖^2≤D*h/(N:ℝ) := (hentry jj).2
  have hv : ‖v‖≤1 := by nlinarith [norm_nonneg v]
  have hv4 : ‖v‖^4≤(D*h/(N:ℝ))^2 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg _) hdir 2
  have hjets := (hK r hr h hh (hh0.trans (min_le_left _ _)) N hN lam hlam).1
  have hG (c : ℕ) (hc : c=1 ∨ c=2) : QBoundedJets 4 (B*h) (G c) := by
    have H := (hjets k (hk.trans (min_le_left _ _)) jj.val jj.isLt c hc).of_le (by norm_num : 4≤8)
    exact qBoundedJets_iff_qBddSmooth.mpr H
  constructor
  · intro c hc
    have H := abs_terminal_tilt_deriv_remainder_le hF (by norm_num)
      (qBoundedJets_iff_qBddSmooth.mp (hG c hc)) (by norm_num) hm v x hv
    calc
      _ ≤ (B*h)*P*‖v‖^4 := H
      _ ≤ (B*h)*P*(D*h/(N:ℝ))^2 := mul_le_mul_of_nonneg_left hv4 (by positivity)
      _ = K1*h^3/(N:ℝ)^2 := by dsimp only [K1]; ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hK2) (pow_nonneg hh.le 3)) (sq_nonneg _)
  · have H := abs_terminalStep_second_deriv_remainder_le hF (by norm_num)
      (hG 1 (Or.inl rfl)) hm v x hv
    calc
      _ ≤ (B*h)^2*Q*‖v‖^4 := H
      _ ≤ (B*h)^2*Q*(D*h/(N:ℝ))^2 := mul_le_mul_of_nonneg_left hv4 (by positivity)
      _ = K2*h^4/(N:ℝ)^2 := by dsimp only [K2]; ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK1) (pow_nonneg hh.le 4)) (sq_nonneg _)

end SKBarriers2.Corner

namespace SKBarriers2.StepCalculus

local notation "E" => (Fin 3 → ℝ)

def tiltedPathTaylorDefect (l : List (ℝ × E)) (f g : E → ℝ) (x : E) : ℝ :=
  vectorIncrementAverage l f g x-g x-pathGeneratorSum f g l x

def tiltedPathDefectTerms (p : ℝ × E) (l : List (ℝ × E)) (f g : E → ℝ)
    (x : E) : Fin 4 → ℝ :=
  let F := vectorIncrementChain l f
  let S := pathGeneratorSum f g l
  ![tiltedAverage p.1 p.2 F (tiltedPathTaylorDefect l f g) x,
    tiltedGeneratorDefect p.1 p.2 F g x,
    pathGenerator p.1 p.2 F g x-pathGenerator p.1 p.2 f g x,
    tiltedAverage p.1 p.2 F S x-S x]

theorem tiltedPathTaylorDefect_cons_eq_sum {B C : ℝ} {f g : E → ℝ}
    (hf : QPotential 5 B f) (hg : QBoundedJets 4 C g)
    (p : ℝ × E) (l : List (ℝ × E))
    (hm : ∀ q∈l, q.1∈Icc (0:ℝ) 1) (x : E) :
    tiltedPathTaylorDefect (p::l) f g x = ∑ i : Fin 4, tiltedPathDefectTerms p l f g x i := by
  let F := vectorIncrementChain l f
  let S := pathGeneratorSum f g l
  let R := tiltedPathTaylorDefect l f g
  have hfb := hf.boundedDerivs (by norm_num)
  have hF : BoundedDerivs F := vectorIncrementChain_regular l hfb
  have hS : QBoundedJets 2 ((4*B+1)*C*chainEnergy l) S :=
    qBoundedJets_pathGeneratorSum (hf.of_le (by norm_num)) hg l hm
  have hgE : HasExpGrowth g :=
    ((qBoundedJets_iff_qBddSmooth.mp hg).potential.boundedDerivs (by norm_num)).hasExpGrowth
  have hSE : HasExpGrowth S :=
    ((qBoundedJets_iff_qBddSmooth.mp hS).potential.boundedDerivs (by norm_num)).hasExpGrowth
  have hA := vectorIncrementAverage_regular l hfb hg.smooth.continuous hgE
  have hRc : Continuous R := (hA.1.sub hg.smooth.continuous).sub hS.smooth.continuous
  have hRE : HasExpGrowth R := by
    convert (hA.2.add ((HasExpGrowth.const (-1)).mul hgE)).add
      ((HasExpGrowth.const (-1)).mul hSE) using 1
    funext y
    dsimp only [R,tiltedPathTaylorDefect,S]
    ring
  have hsplit : vectorIncrementAverage l f g = fun y => R y+(g y+S y) := by
    funext y
    dsimp only [R,tiltedPathTaylorDefect,S]
    ring
  have H := congrFun (vectorStepAverage_add hF hRc (hg.smooth.continuous.add hS.smooth.continuous)
    hRE (hgE.add hSE) p.1 p.2) x
  simp only [Pi.add_apply] at H
  rw [← hsplit] at H
  change vectorStepAverage p.1 p.2 F (vectorIncrementAverage l f g) x =
    vectorStepAverage p.1 p.2 F R x+vectorStepAverage p.1 p.2 F (fun y => g y+S y) x at H
  rw [vectorStepAverage_add hF hg.smooth.continuous hS.smooth.continuous hgE hSE p.1 p.2] at H
  change tiltedAverage p.1 p.2 F (vectorIncrementAverage l f g) x =
    tiltedAverage p.1 p.2 F R x+
      (tiltedAverage p.1 p.2 F g x+tiltedAverage p.1 p.2 F S x) at H
  simp only [tiltedPathDefectTerms,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.sum_univ_zero,add_zero]
  change tiltedAverage p.1 p.2 F (vectorIncrementAverage l f g) x-g x-
    (pathGenerator p.1 p.2 f g x+S x) = _
  rw [H]
  dsimp only [tiltedGeneratorDefect,R,S,F]
  ring

theorem tiltedPathTaylorDefect_cons_iteratedDeriv_two {B C k : ℝ} {f : E → ℝ}
    (hf : QPotential 5 B f) (p : ℝ → ℝ × E) (l : ℝ → List (ℝ × E)) (g : ℝ → E → ℝ)
    (hgood : ∀ᶠ t in 𝓝 k, QBoundedJets 4 C (g t) ∧ ∀ q∈l t, q.1∈Icc (0:ℝ) 1)
    (x : E)
    (hterms : ∀ i : Fin 4, ContDiffAt ℝ 2 (fun t => tiltedPathDefectTerms (p t) (l t) f (g t) x i) k) :
    ContDiffAt ℝ 2 (fun t => tiltedPathTaylorDefect (p t::l t) f (g t) x) k ∧
      iteratedDeriv 2 (fun t => tiltedPathTaylorDefect (p t::l t) f (g t) x) k =
        ∑ i : Fin 4, iteratedDeriv 2 (fun t => tiltedPathDefectTerms (p t) (l t) f (g t) x i) k := by
  have he : (fun t => tiltedPathTaylorDefect (p t::l t) f (g t) x) =ᶠ[𝓝 k]
      fun t => ∑ i : Fin 4, tiltedPathDefectTerms (p t) (l t) f (g t) x i := by
    filter_upwards [hgood] with t ht
    exact tiltedPathTaylorDefect_cons_eq_sum hf ht.1 (p t) (l t) ht.2 x
  have hs : ContDiffAt ℝ 2 (fun t => ∑ i : Fin 4, tiltedPathDefectTerms (p t) (l t) f (g t) x i) k :=
    ContDiffAt.sum (fun i _ => hterms i)
  refine ⟨hs.congr_of_eventuallyEq he,?_⟩
  rw [he.iteratedDeriv_eq 2,iteratedDeriv_fun_sum (fun i _ => hterms i)]

end SKBarriers2.StepCalculus
