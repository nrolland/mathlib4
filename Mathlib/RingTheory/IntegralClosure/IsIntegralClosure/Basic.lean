/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# # Integral closure as a characteristic predicate

We prove basic properties of `IsIntegralClosure`.

-/

open scoped Classical
open Polynomial Submodule

section

variable {R A B S : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S]
variable [Algebra R A] [Algebra R B] (f : R →+* S)

theorem IsIntegral.map_of_comp_eq {R S T U : Type*} [CommRing R] [Ring S]
    [CommRing T] [Ring U] [Algebra R S] [Algebra T U] (φ : R →+* T) (ψ : S →+* U)
    (h : (algebraMap T U).comp φ = ψ.comp (algebraMap R S)) {a : S} (ha : IsIntegral R a) :
    IsIntegral T (ψ a) :=
  let ⟨p, hp⟩ := ha
  ⟨p.map φ, hp.1.map _, by
    rw [← eval_map, map_map, h, ← map_map, eval_map, eval₂_at_apply, eval_map, hp.2, ψ.map_zero]⟩

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
variable (f : A →ₐ[R] B)

theorem Algebra.IsIntegral.of_injective (hf : Function.Injective f) [Algebra.IsIntegral R B] :
    Algebra.IsIntegral R A :=
  ⟨fun _ ↦ (isIntegral_algHom_iff f hf).mp (isIntegral _)⟩

end

@[simp]
theorem isIntegral_algEquiv {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]
    (f : A ≃ₐ[R] B) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x :=
  ⟨fun h ↦ by simpa using h.map f.symm, IsIntegral.map f⟩

/-- If `R → A → B` is an algebra tower,
then if the entire tower is an integral extension so is `A → B`. -/
theorem IsIntegral.tower_top [Algebra A B] [IsScalarTower R A B] {x : B}
    (hx : IsIntegral R x) : IsIntegral A x :=
  let ⟨p, hp, hpx⟩ := hx
  ⟨p.map <| algebraMap R A, hp.map _, by rw [← aeval_def, aeval_map_algebraMap, aeval_def, hpx]⟩

theorem map_isIntegral_int {B C F : Type*} [Ring B] [Ring C] {b : B}
    [FunLike F B C] [RingHomClass F B C] (f : F)
    (hb : IsIntegral ℤ b) : IsIntegral ℤ (f b) :=
  hb.map (f : B →+* C).toIntAlgHom

theorem IsIntegral.of_subring {x : B} (T : Subring R) (hx : IsIntegral T x) : IsIntegral R x :=
  hx.tower_top

protected theorem IsIntegral.algebraMap [Algebra A B] [IsScalarTower R A B] {x : A}
    (h : IsIntegral R x) : IsIntegral R (algebraMap A B x) := by
  rcases h with ⟨f, hf, hx⟩
  use f, hf
  rw [IsScalarTower.algebraMap_eq R A B, ← hom_eval₂, hx, RingHom.map_zero]

theorem isIntegral_algebraMap_iff [Algebra A B] [IsScalarTower R A B] {x : A}
    (hAB : Function.Injective (algebraMap A B)) :
    IsIntegral R (algebraMap A B x) ↔ IsIntegral R x :=
  isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) hAB

theorem isIntegral_iff_isIntegral_closure_finite {r : B} :
    IsIntegral R r ↔ ∃ s : Set R, s.Finite ∧ IsIntegral (Subring.closure s) r := by
  constructor <;> intro hr
  · rcases hr with ⟨p, hmp, hpr⟩
    refine ⟨_, Finset.finite_toSet _, p.restriction, monic_restriction.2 hmp, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap R r p.restriction, map_restriction, aeval_def, hpr]
  rcases hr with ⟨s, _, hsr⟩
  exact hsr.of_subring _

theorem fg_adjoin_of_finite {s : Set A} (hfs : s.Finite) (his : ∀ x ∈ s, IsIntegral R x) :
    (Algebra.adjoin R s).toSubmodule.FG :=
  Set.Finite.induction_on hfs
    (fun _ =>
      ⟨{1},
        Submodule.ext fun x => by
          rw [Algebra.adjoin_empty, Finset.coe_singleton, ← one_eq_span, Algebra.toSubmodule_bot]⟩)
    (fun {a s} _ _ ih his => by
      rw [← Set.union_singleton, Algebra.adjoin_union_coe_submodule]
      exact
        FG.mul (ih fun i hi => his i <| Set.mem_insert_of_mem a hi)
          (his a <| Set.mem_insert a s).fg_adjoin_singleton)
    his

theorem isNoetherian_adjoin_finset [IsNoetherianRing R] (s : Finset A)
    (hs : ∀ x ∈ s, IsIntegral R x) : IsNoetherian R (Algebra.adjoin R (s : Set A)) :=
  isNoetherian_of_fg_of_noetherian _ (fg_adjoin_of_finite s.finite_toSet hs)

theorem isIntegral_of_noetherian (_ : IsNoetherian R B) (x : B) : IsIntegral R x :=
  .of_finite R x

theorem isIntegral_of_submodule_noetherian (S : Subalgebra R B)
    (H : IsNoetherian R (Subalgebra.toSubmodule S)) (x : B) (hx : x ∈ S) : IsIntegral R x :=
  .of_mem_of_fg _ ((fg_top _).mp <| H.noetherian _) _ hx

/-- Suppose `A` is an `R`-algebra, `M` is an `A`-module such that `a • m ≠ 0` for all non-zero `a`
and `m`. If `x : A` fixes a nontrivial f.g. `R`-submodule `N` of `M`, then `x` is `R`-integral. -/
theorem isIntegral_of_smul_mem_submodule {M : Type*} [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] [NoZeroSMulDivisors A M] (N : Submodule R M) (hN : N ≠ ⊥) (hN' : N.FG)
    (x : A) (hx : ∀ n ∈ N, x • n ∈ N) : IsIntegral R x := by
  let A' : Subalgebra R A :=
    { carrier := { x | ∀ n ∈ N, x • n ∈ N }
      mul_mem' := fun {a b} ha hb n hn => smul_smul a b n ▸ ha _ (hb _ hn)
      one_mem' := fun n hn => (one_smul A n).symm ▸ hn
      add_mem' := fun {a b} ha hb n hn => (add_smul a b n).symm ▸ N.add_mem (ha _ hn) (hb _ hn)
      zero_mem' := fun n _hn => (zero_smul A n).symm ▸ N.zero_mem
      algebraMap_mem' := fun r n hn => (algebraMap_smul A r n).symm ▸ N.smul_mem r hn }
  let f : A' →ₐ[R] Module.End R N :=
    AlgHom.ofLinearMap
      { toFun := fun x => (DistribMulAction.toLinearMap R M x).restrict x.prop
        -- Porting note: was
                -- `fun x y => LinearMap.ext fun n => Subtype.ext <| add_smul x y n`
        map_add' := by intros x y; ext; exact add_smul _ _ _
        -- Porting note: was
                --  `fun r s => LinearMap.ext fun n => Subtype.ext <| smul_assoc r s n`
        map_smul' := by intros r s; ext; apply smul_assoc }
      -- Porting note: the next two lines were
      --`(LinearMap.ext fun n => Subtype.ext <| one_smul _ _) fun x y =>`
      --`LinearMap.ext fun n => Subtype.ext <| mul_smul x y n`
      (by ext; apply one_smul)
      (by intros x y; ext; apply mul_smul)
  obtain ⟨a, ha₁, ha₂⟩ : ∃ a ∈ N, a ≠ (0 : M) := by
    by_contra! h'
    apply hN
    rwa [eq_bot_iff]
  have : Function.Injective f := by
    show Function.Injective f.toLinearMap
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro s hs
    have : s.1 • a = 0 := congr_arg Subtype.val (LinearMap.congr_fun hs ⟨a, ha₁⟩)
    exact Subtype.ext ((eq_zero_or_eq_zero_of_smul_eq_zero this).resolve_right ha₂)
  show IsIntegral R (A'.val ⟨x, hx⟩)
  rw [isIntegral_algHom_iff A'.val Subtype.val_injective, ← isIntegral_algHom_iff f this]
  haveI : Module.Finite R N := by rwa [Module.finite_def, Submodule.fg_top]
  apply Algebra.IsIntegral.isIntegral

variable {f}

theorem RingHom.Finite.to_isIntegral (h : f.Finite) : f.IsIntegral :=
  letI := f.toAlgebra
  fun _ ↦ IsIntegral.of_mem_of_fg ⊤ h.1 _ trivial

alias RingHom.IsIntegral.of_finite := RingHom.Finite.to_isIntegral

/-- The [Kurosh problem](https://en.wikipedia.org/wiki/Kurosh_problem) asks to show that
  this is still true when `A` is not necessarily commutative and `R` is a field, but it has
  been solved in the negative. See https://arxiv.org/pdf/1706.02383.pdf for criteria for a
  finitely generated algebraic (= integral) algebra over a field to be finite dimensional.

This could be an `instance`, but we tend to go from `Module.Finite` to `IsIntegral`/`IsAlgebraic`,
and making it an instance will cause the search to be complicated a lot.
-/
theorem Algebra.IsIntegral.finite [Algebra.IsIntegral R A] [h' : Algebra.FiniteType R A] :
    Module.Finite R A :=
  have ⟨s, hs⟩ := h'
  ⟨by apply hs ▸ fg_adjoin_of_finite s.finite_toSet fun x _ ↦ Algebra.IsIntegral.isIntegral x⟩

/-- finite = integral + finite type -/
theorem Algebra.finite_iff_isIntegral_and_finiteType :
    Module.Finite R A ↔ Algebra.IsIntegral R A ∧ Algebra.FiniteType R A :=
  ⟨fun _ ↦ ⟨⟨.of_finite R⟩, inferInstance⟩, fun ⟨h, _⟩ ↦ h.finite⟩

theorem RingHom.IsIntegral.to_finite (h : f.IsIntegral) (h' : f.FiniteType) : f.Finite :=
  let _ := f.toAlgebra
  let _ : Algebra.IsIntegral R S := ⟨h⟩
  Algebra.IsIntegral.finite (h' := h')

alias RingHom.Finite.of_isIntegral_of_finiteType := RingHom.IsIntegral.to_finite

/-- finite = integral + finite type -/
theorem RingHom.finite_iff_isIntegral_and_finiteType : f.Finite ↔ f.IsIntegral ∧ f.FiniteType :=
  ⟨fun h ↦ ⟨h.to_isIntegral, h.to_finiteType⟩, fun ⟨h, h'⟩ ↦ h.to_finite h'⟩

variable (f : R →+* S) (R A)

theorem mem_integralClosure_iff_mem_fg {r : A} :
    r ∈ integralClosure R A ↔ ∃ M : Subalgebra R A, M.toSubmodule.FG ∧ r ∈ M :=
  ⟨fun hr =>
    ⟨Algebra.adjoin R {r}, hr.fg_adjoin_singleton, Algebra.subset_adjoin rfl⟩,
    fun ⟨M, Hf, hrM⟩ => .of_mem_of_fg M Hf _ hrM⟩

variable {R A}

theorem adjoin_le_integralClosure {x : A} (hx : IsIntegral R x) :
    Algebra.adjoin R {x} ≤ integralClosure R A := by
  rw [Algebra.adjoin_le_iff]
  simp only [SetLike.mem_coe, Set.singleton_subset_iff]
  exact hx

theorem le_integralClosure_iff_isIntegral {S : Subalgebra R A} :
    S ≤ integralClosure R A ↔ Algebra.IsIntegral R S :=
  SetLike.forall.symm.trans <|
    (forall_congr' fun x =>
      show IsIntegral R (algebraMap S A x) ↔ IsIntegral R x from
        isIntegral_algebraMap_iff Subtype.coe_injective).trans
      Algebra.isIntegral_def.symm

theorem Algebra.isIntegral_sup {S T : Subalgebra R A} :
    Algebra.IsIntegral R (S ⊔ T : Subalgebra R A) ↔
      Algebra.IsIntegral R S ∧ Algebra.IsIntegral R T := by
  simp only [← le_integralClosure_iff_isIntegral, sup_le_iff]

/-- Mapping an integral closure along an `AlgEquiv` gives the integral closure. -/
theorem integralClosure_map_algEquiv [Algebra R S] (f : A ≃ₐ[R] S) :
    (integralClosure R A).map (f : A →ₐ[R] S) = integralClosure R S := by
  ext y
  rw [Subalgebra.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx.map f
  · intro hy
    use f.symm y, hy.map (f.symm : S →ₐ[R] A)
    simp

/-- An `AlgHom` between two rings restrict to an `AlgHom` between the integral closures inside
them. -/
def AlgHom.mapIntegralClosure [Algebra R S] (f : A →ₐ[R] S) :
    integralClosure R A →ₐ[R] integralClosure R S :=
  (f.restrictDomain (integralClosure R A)).codRestrict (integralClosure R S) (fun ⟨_, h⟩ => h.map f)

@[simp]
theorem AlgHom.coe_mapIntegralClosure [Algebra R S] (f : A →ₐ[R] S)
    (x : integralClosure R A) : (f.mapIntegralClosure x : S) = f (x : A) := rfl

/-- An `AlgEquiv` between two rings restrict to an `AlgEquiv` between the integral closures inside
them. -/
def AlgEquiv.mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S) :
    integralClosure R A ≃ₐ[R] integralClosure R S :=
  AlgEquiv.ofAlgHom (f : A →ₐ[R] S).mapIntegralClosure (f.symm : S →ₐ[R] A).mapIntegralClosure
    (AlgHom.ext fun _ ↦ Subtype.ext (f.right_inv _))
    (AlgHom.ext fun _ ↦ Subtype.ext (f.left_inv _))

@[simp]
theorem AlgEquiv.coe_mapIntegralClosure [Algebra R S] (f : A ≃ₐ[R] S)
    (x : integralClosure R A) : (f.mapIntegralClosure x : S) = f (x : A) := rfl

theorem integralClosure.isIntegral (x : integralClosure R A) : IsIntegral R x :=
  let ⟨p, hpm, hpx⟩ := x.2
  ⟨p, hpm,
    Subtype.eq <| by
      rwa [← aeval_def, ← Subalgebra.val_apply, aeval_algHom_apply] at hpx⟩

instance integralClosure.AlgebraIsIntegral : Algebra.IsIntegral R (integralClosure R A) :=
  ⟨integralClosure.isIntegral⟩

theorem IsIntegral.of_mul_unit {x y : B} {r : R} (hr : algebraMap R B r * y = 1)
    (hx : IsIntegral R (x * y)) : IsIntegral R x := by
  obtain ⟨p, p_monic, hp⟩ := hx
  refine ⟨scaleRoots p r, (monic_scaleRoots_iff r).2 p_monic, ?_⟩
  convert scaleRoots_aeval_eq_zero hp
  rw [Algebra.commutes] at hr ⊢
  rw [mul_assoc, hr, mul_one]; rfl

theorem RingHom.IsIntegralElem.of_mul_unit (x y : S) (r : R) (hr : f r * y = 1)
    (hx : f.IsIntegralElem (x * y)) : f.IsIntegralElem x :=
  letI : Algebra R S := f.toAlgebra
  IsIntegral.of_mul_unit hr hx

/-- Generalization of `IsIntegral.of_mem_closure` bootstrapped up from that lemma -/
theorem IsIntegral.of_mem_closure' (G : Set A) (hG : ∀ x ∈ G, IsIntegral R x) :
    ∀ x ∈ Subring.closure G, IsIntegral R x := fun _ hx ↦
  Subring.closure_induction hx hG isIntegral_zero isIntegral_one (fun _ _ ↦ IsIntegral.add)
    (fun _ ↦ IsIntegral.neg) fun _ _ ↦ IsIntegral.mul

theorem IsIntegral.of_mem_closure'' {S : Type*} [CommRing S] {f : R →+* S} (G : Set S)
    (hG : ∀ x ∈ G, f.IsIntegralElem x) : ∀ x ∈ Subring.closure G, f.IsIntegralElem x := fun x hx =>
  @IsIntegral.of_mem_closure' R S _ _ f.toAlgebra G hG x hx

theorem IsIntegral.pow {x : B} (h : IsIntegral R x) (n : ℕ) : IsIntegral R (x ^ n) :=
  .of_mem_of_fg _ h.fg_adjoin_singleton _ <|
    Subalgebra.pow_mem _ (by exact Algebra.subset_adjoin rfl) _

theorem IsIntegral.nsmul {x : B} (h : IsIntegral R x) (n : ℕ) : IsIntegral R (n • x) :=
  h.smul n

theorem IsIntegral.zsmul {x : B} (h : IsIntegral R x) (n : ℤ) : IsIntegral R (n • x) :=
  h.smul n

theorem IsIntegral.multiset_prod {s : Multiset A} (h : ∀ x ∈ s, IsIntegral R x) :
    IsIntegral R s.prod :=
  (integralClosure R A).multiset_prod_mem h

theorem IsIntegral.multiset_sum {s : Multiset A} (h : ∀ x ∈ s, IsIntegral R x) :
    IsIntegral R s.sum :=
  (integralClosure R A).multiset_sum_mem h

theorem IsIntegral.prod {α : Type*} {s : Finset α} (f : α → A) (h : ∀ x ∈ s, IsIntegral R (f x)) :
    IsIntegral R (∏ x ∈ s, f x) :=
  (integralClosure R A).prod_mem h

theorem IsIntegral.sum {α : Type*} {s : Finset α} (f : α → A) (h : ∀ x ∈ s, IsIntegral R (f x)) :
    IsIntegral R (∑ x ∈ s, f x) :=
  (integralClosure R A).sum_mem h

theorem IsIntegral.det {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n A}
    (h : ∀ i j, IsIntegral R (M i j)) : IsIntegral R M.det := by
  rw [Matrix.det_apply]
  exact IsIntegral.sum _ fun σ _hσ ↦ (IsIntegral.prod _ fun i _hi => h _ _).zsmul _

@[simp]
theorem IsIntegral.pow_iff {x : A} {n : ℕ} (hn : 0 < n) : IsIntegral R (x ^ n) ↔ IsIntegral R x :=
  ⟨IsIntegral.of_pow hn, fun hx ↦ hx.pow n⟩

open TensorProduct

theorem IsIntegral.tmul (x : A) {y : B} (h : IsIntegral R y) : IsIntegral A (x ⊗ₜ[R] y) := by
  rw [← mul_one x, ← smul_eq_mul, ← smul_tmul']
  exact smul _ (h.map_of_comp_eq (algebraMap R A)
    (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)).toRingHom
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap)

section

variable (p : R[X]) (x : S)

/-- The monic polynomial whose roots are `p.leadingCoeff * x` for roots `x` of `p`. -/
noncomputable def normalizeScaleRoots (p : R[X]) : R[X] :=
  ∑ i ∈ p.support,
    monomial i (if i = p.natDegree then 1 else p.coeff i * p.leadingCoeff ^ (p.natDegree - 1 - i))

theorem normalizeScaleRoots_coeff_mul_leadingCoeff_pow (i : ℕ) (hp : 1 ≤ natDegree p) :
    (normalizeScaleRoots p).coeff i * p.leadingCoeff ^ i =
      p.coeff i * p.leadingCoeff ^ (p.natDegree - 1) := by
  simp only [normalizeScaleRoots, finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq', one_mul,
    zero_mul, mem_support_iff, ite_mul, Ne, ite_not]
  split_ifs with h₁ h₂
  · simp [h₁]
  · rw [h₂, leadingCoeff, ← pow_succ', tsub_add_cancel_of_le hp]
  · rw [mul_assoc, ← pow_add, tsub_add_cancel_of_le]
    apply Nat.le_sub_one_of_lt
    rw [lt_iff_le_and_ne]
    exact ⟨le_natDegree_of_ne_zero h₁, h₂⟩

theorem leadingCoeff_smul_normalizeScaleRoots (p : R[X]) :
    p.leadingCoeff • normalizeScaleRoots p = scaleRoots p p.leadingCoeff := by
  ext
  simp only [coeff_scaleRoots, normalizeScaleRoots, coeff_monomial, coeff_smul, Finset.smul_sum,
    Ne, Finset.sum_ite_eq', finset_sum_coeff, smul_ite, smul_zero, mem_support_iff]
  -- Porting note: added the following `simp only`
  simp only [tsub_le_iff_right, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', mem_support_iff, ne_eq, ite_not]
  split_ifs with h₁ h₂
  · simp [*]
  · simp [*]
  · rw [mul_comm, mul_assoc, ← pow_succ, tsub_right_comm,
      tsub_add_cancel_of_le]
    rw [Nat.succ_le_iff]
    exact tsub_pos_of_lt (lt_of_le_of_ne (le_natDegree_of_ne_zero h₁) h₂)

theorem normalizeScaleRoots_support : (normalizeScaleRoots p).support ≤ p.support := by
  intro x
  contrapose
  simp only [not_mem_support_iff, normalizeScaleRoots, finset_sum_coeff, coeff_monomial,
    Finset.sum_ite_eq', mem_support_iff, Ne, Classical.not_not, ite_eq_right_iff]
  intro h₁ h₂
  exact (h₂ h₁).elim

theorem normalizeScaleRoots_degree : (normalizeScaleRoots p).degree = p.degree := by
  apply le_antisymm
  · exact Finset.sup_mono (normalizeScaleRoots_support p)
  · rw [← degree_scaleRoots, ← leadingCoeff_smul_normalizeScaleRoots]
    exact degree_smul_le _ _

theorem normalizeScaleRoots_eval₂_leadingCoeff_mul (h : 1 ≤ p.natDegree) (f : R →+* S) (x : S) :
    (normalizeScaleRoots p).eval₂ f (f p.leadingCoeff * x) =
      f p.leadingCoeff ^ (p.natDegree - 1) * p.eval₂ f x := by
  rw [eval₂_eq_sum_range, eval₂_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr
  · rw [natDegree_eq_of_degree_eq (normalizeScaleRoots_degree p)]
  intro n _hn
  rw [mul_pow, ← mul_assoc, ← f.map_pow, ← f.map_mul,
    normalizeScaleRoots_coeff_mul_leadingCoeff_pow _ _ h, f.map_mul, f.map_pow]
  ring

theorem normalizeScaleRoots_monic (h : p ≠ 0) : (normalizeScaleRoots p).Monic := by
  delta Monic leadingCoeff
  rw [natDegree_eq_of_degree_eq (normalizeScaleRoots_degree p)]
  suffices p = 0 → (0 : R) = 1 by simpa [normalizeScaleRoots, coeff_monomial]
  exact fun h' => (h h').elim

/-- Given a `p : R[X]` and a `x : S` such that `p.eval₂ f x = 0`,
`f p.leadingCoeff * x` is integral. -/
theorem RingHom.isIntegralElem_leadingCoeff_mul (h : p.eval₂ f x = 0) :
    f.IsIntegralElem (f p.leadingCoeff * x) := by
  by_cases h' : 1 ≤ p.natDegree
  · use normalizeScaleRoots p
    have : p ≠ 0 := fun h'' => by
      rw [h'', natDegree_zero] at h'
      exact Nat.not_succ_le_zero 0 h'
    use normalizeScaleRoots_monic p this
    rw [normalizeScaleRoots_eval₂_leadingCoeff_mul p h' f x, h, mul_zero]
  · by_cases hp : p.map f = 0
    · apply_fun fun q => coeff q p.natDegree at hp
      rw [coeff_map, coeff_zero, coeff_natDegree] at hp
      rw [hp, zero_mul]
      exact f.isIntegralElem_zero
    · rw [Nat.one_le_iff_ne_zero, Classical.not_not] at h'
      rw [eq_C_of_natDegree_eq_zero h', eval₂_C] at h
      suffices p.map f = 0 by exact (hp this).elim
      rw [eq_C_of_natDegree_eq_zero h', map_C, h, C_eq_zero]

/-- Given a `p : R[X]` and a root `x : S`,
then `p.leadingCoeff • x : S` is integral over `R`. -/
theorem isIntegral_leadingCoeff_smul [Algebra R S] (h : aeval x p = 0) :
    IsIntegral R (p.leadingCoeff • x) := by
  rw [aeval_def] at h
  rw [Algebra.smul_def]
  exact (algebraMap R S).isIntegralElem_leadingCoeff_mul p x h

end

end

section IsIntegralClosure

instance integralClosure.isIntegralClosure (R A : Type*) [CommRing R] [CommRing A] [Algebra R A] :
    IsIntegralClosure (integralClosure R A) R A where
  algebraMap_injective' := Subtype.coe_injective
  isIntegral_iff {x} := ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨⟨_, h⟩, rfl⟩; exact h⟩

namespace IsIntegralClosure

-- Porting note: added to work around missing infer kind support
theorem algebraMap_injective (A R B : Type*) [CommRing R] [CommSemiring A] [CommRing B]
    [Algebra R B] [Algebra A B] [IsIntegralClosure A R B] : Function.Injective (algebraMap A B) :=
  algebraMap_injective' R

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R B] [Algebra A B] [IsIntegralClosure A R B]
variable (R B)

protected theorem isIntegral [Algebra R A] [IsScalarTower R A B] (x : A) : IsIntegral R x :=
  (isIntegral_algebraMap_iff (algebraMap_injective A R B)).mp <|
    show IsIntegral R (algebraMap A B x) from isIntegral_iff.mpr ⟨x, rfl⟩

theorem isIntegral_algebra [Algebra R A] [IsScalarTower R A B] : Algebra.IsIntegral R A :=
  ⟨fun x => IsIntegralClosure.isIntegral R B x⟩

theorem noZeroSMulDivisors [Algebra R A] [IsScalarTower R A B] [NoZeroSMulDivisors R B] :
    NoZeroSMulDivisors R A := by
  refine
    Function.Injective.noZeroSMulDivisors _ (IsIntegralClosure.algebraMap_injective A R B)
      (map_zero _) fun _ _ => ?_
  simp only [Algebra.algebraMap_eq_smul_one, IsScalarTower.smul_assoc]

variable {R} (A) {B}

/-- If `x : B` is integral over `R`, then it is an element of the integral closure of `R` in `B`. -/
noncomputable def mk' (x : B) (hx : IsIntegral R x) : A :=
  Classical.choose (isIntegral_iff.mp hx)

@[simp]
theorem algebraMap_mk' (x : B) (hx : IsIntegral R x) : algebraMap A B (mk' A x hx) = x :=
  Classical.choose_spec (isIntegral_iff.mp hx)

@[simp]
theorem mk'_one (h : IsIntegral R (1 : B) := isIntegral_one) : mk' A 1 h = 1 :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', RingHom.map_one]

@[simp]
theorem mk'_zero (h : IsIntegral R (0 : B) := isIntegral_zero) : mk' A 0 h = 0 :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', RingHom.map_zero]

-- Porting note: Left-hand side does not simplify @[simp]
theorem mk'_add (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
    mk' A (x + y) (hx.add hy) = mk' A x hx + mk' A y hy :=
  algebraMap_injective A R B <| by simp only [algebraMap_mk', RingHom.map_add]

-- Porting note: Left-hand side does not simplify @[simp]
theorem mk'_mul (x y : B) (hx : IsIntegral R x) (hy : IsIntegral R y) :
    mk' A (x * y) (hx.mul hy) = mk' A x hx * mk' A y hy :=
  algebraMap_injective A R B <| by simp only [algebraMap_mk', RingHom.map_mul]

@[simp]
theorem mk'_algebraMap [Algebra R A] [IsScalarTower R A B] (x : R)
    (h : IsIntegral R (algebraMap R B x) := isIntegral_algebraMap) :
    IsIntegralClosure.mk' A (algebraMap R B x) h = algebraMap R A x :=
  algebraMap_injective A R B <| by rw [algebraMap_mk', ← IsScalarTower.algebraMap_apply]

section lift

variable (B) {S : Type*} [CommRing S] [Algebra R S]
-- split from above, since otherwise it does not synthesize `Semiring S`
variable [Algebra S B] [IsScalarTower R S B]
variable [Algebra R A] [IsScalarTower R A B] [isIntegral : Algebra.IsIntegral R S]
variable (R)

/-- If `B / S / R` is a tower of ring extensions where `S` is integral over `R`,
then `S` maps (uniquely) into an integral closure `B / A / R`. -/
noncomputable def lift : S →ₐ[R] A where
  toFun x := mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))
  map_one' := by simp only [RingHom.map_one, mk'_one]
  map_zero' := by simp only [RingHom.map_zero, mk'_zero]
  map_add' x y := by simp_rw [← mk'_add, map_add]
  map_mul' x y := by simp_rw [← mk'_mul, RingHom.map_mul]
  commutes' x := by simp_rw [← IsScalarTower.algebraMap_apply, mk'_algebraMap]

@[simp]
theorem algebraMap_lift (x : S) : algebraMap A B (lift R A B x) = algebraMap S B x :=
  algebraMap_mk' A (algebraMap S B x) (IsIntegral.algebraMap
    (Algebra.IsIntegral.isIntegral (R := R) x))

end lift

section Equiv

variable (R B) (A' : Type*) [CommRing A']
variable [Algebra A' B] [IsIntegralClosure A' R B]
variable [Algebra R A] [Algebra R A'] [IsScalarTower R A B] [IsScalarTower R A' B]

/-- Integral closures are all isomorphic to each other. -/
noncomputable def equiv : A ≃ₐ[R] A' :=
  AlgEquiv.ofAlgHom
    (lift _ B (isIntegral := isIntegral_algebra R B))
    (lift _ B (isIntegral := isIntegral_algebra R B))
    (by ext x; apply algebraMap_injective A' R B; simp)
    (by ext x; apply algebraMap_injective A R B; simp)

@[simp]
theorem algebraMap_equiv (x : A) : algebraMap A' B (equiv R A B A' x) = algebraMap A B x :=
  algebraMap_lift A' B (isIntegral := isIntegral_algebra R B) x

end Equiv

end IsIntegralClosure

end IsIntegralClosure

section Algebra

open Algebra

variable {R A B S T : Type*}
variable [CommRing R] [CommRing A] [Ring B] [CommRing S] [CommRing T]
variable [Algebra A B] [Algebra R B] (f : R →+* S) (g : S →+* T)
variable [Algebra R A] [IsScalarTower R A B]

/-- If A is an R-algebra all of whose elements are integral over R,
and x is an element of an A-algebra that is integral over A, then x is integral over R. -/
theorem isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx : IsIntegral A x) :
    IsIntegral R x := by
  rcases hx with ⟨p, pmonic, hp⟩
  let S := adjoin R (p.coeffs : Set A)
  have : Module.Finite R S := ⟨(Subalgebra.toSubmodule S).fg_top.mpr <|
    fg_adjoin_of_finite p.coeffs.finite_toSet fun a _ ↦ Algebra.IsIntegral.isIntegral a⟩
  let p' : S[X] := p.toSubring S.toSubring subset_adjoin
  have hSx : IsIntegral S x := ⟨p', (p.monic_toSubring _ _).mpr pmonic, by
    rw [IsScalarTower.algebraMap_eq S A B, ← eval₂_map]
    convert hp; apply p.map_toSubring S.toSubring⟩
  let Sx := Subalgebra.toSubmodule (adjoin S {x})
  let MSx : Module S Sx := SMulMemClass.toModule _ -- the next line times out without this
  have : Module.Finite S Sx := ⟨(Submodule.fg_top _).mpr hSx.fg_adjoin_singleton⟩
  refine .of_mem_of_fg ((adjoin S {x}).restrictScalars R) ?_ _
    ((Subalgebra.mem_restrictScalars R).mpr <| subset_adjoin rfl)
  rw [← Submodule.fg_top, ← Module.finite_def]
  letI : SMul S Sx := { MSx with } -- need this even though MSx is there
  have : IsScalarTower R S Sx :=
    Submodule.isScalarTower Sx -- Lean looks for `Module A Sx` without this
  exact Module.Finite.trans S Sx

variable (A) in
/-- If A is an R-algebra all of whose elements are integral over R,
and B is an A-algebra all of whose elements are integral over A,
then all elements of B are integral over R. -/
protected theorem Algebra.IsIntegral.trans
    [Algebra.IsIntegral R A] [Algebra.IsIntegral A B] : Algebra.IsIntegral R B :=
  ⟨fun x ↦ isIntegral_trans x (Algebra.IsIntegral.isIntegral (R := A) x)⟩

protected theorem RingHom.IsIntegral.trans
    (hf : f.IsIntegral) (hg : g.IsIntegral) : (g.comp f).IsIntegral :=
  let _ := f.toAlgebra; let _ := g.toAlgebra; let _ := (g.comp f).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsIntegral R S := ⟨hf⟩
  have : Algebra.IsIntegral S T := ⟨hg⟩
  have : Algebra.IsIntegral R T := Algebra.IsIntegral.trans S
  Algebra.IsIntegral.isIntegral

/-- If `R → A → B` is an algebra tower, `C` is the integral closure of `R` in `B`
and `A` is integral over `R`, then `C` is the integral closure of `A` in `B`. -/
lemma IsIntegralClosure.tower_top {B C : Type*} [CommRing C] [CommRing B]
    [Algebra R B] [Algebra A B] [Algebra C B] [IsScalarTower R A B]
    [IsIntegralClosure C R B] [Algebra.IsIntegral R A] :
    IsIntegralClosure C A B :=
  ⟨IsIntegralClosure.algebraMap_injective _ R _,
   fun hx => (IsIntegralClosure.isIntegral_iff).mp (isIntegral_trans (R := R) _ hx),
   fun hx => ((IsIntegralClosure.isIntegral_iff (R := R)).mpr hx).tower_top⟩

theorem RingHom.isIntegral_of_surjective (hf : Function.Surjective f) : f.IsIntegral :=
  fun x ↦ (hf x).recOn fun _y hy ↦ hy ▸ f.isIntegralElem_map

theorem Algebra.isIntegral_of_surjective (h : Function.Surjective (algebraMap R A)) :
    Algebra.IsIntegral R A :=
  ⟨(algebraMap R A).isIntegral_of_surjective h⟩

/-- If `R → A → B` is an algebra tower with `A → B` injective,
then if the entire tower is an integral extension so is `R → A` -/
theorem IsIntegral.tower_bot (H : Function.Injective (algebraMap A B)) {x : A}
    (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x :=
  (isIntegral_algHom_iff (IsScalarTower.toAlgHom R A B) H).mp h

nonrec theorem RingHom.IsIntegral.tower_bot (hg : Function.Injective g)
    (hfg : (g.comp f).IsIntegral) : f.IsIntegral :=
  letI := f.toAlgebra; letI := g.toAlgebra; letI := (g.comp f).toAlgebra
  haveI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  fun x ↦ IsIntegral.tower_bot hg (hfg (g x))

theorem IsIntegral.tower_bot_of_field {R A B : Type*} [CommRing R] [Field A]
    [CommRing B] [Nontrivial B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    {x : A} (h : IsIntegral R (algebraMap A B x)) : IsIntegral R x :=
  h.tower_bot (algebraMap A B).injective

theorem RingHom.isIntegralElem.of_comp {x : T} (h : (g.comp f).IsIntegralElem x) :
    g.IsIntegralElem x :=
  let ⟨p, hp, hp'⟩ := h
  ⟨p.map f, hp.map f, by rwa [← eval₂_map] at hp'⟩

theorem RingHom.IsIntegral.tower_top (h : (g.comp f).IsIntegral) : g.IsIntegral :=
  fun x ↦ RingHom.isIntegralElem.of_comp f g (h x)

theorem RingHom.IsIntegral.quotient {I : Ideal S} (hf : f.IsIntegral) :
    (Ideal.quotientMap I f le_rfl).IsIntegral := by
  rintro ⟨x⟩
  obtain ⟨p, p_monic, hpx⟩ := hf x
  refine ⟨p.map (Ideal.Quotient.mk _), p_monic.map _, ?_⟩
  simpa only [hom_eval₂, eval₂_map] using congr_arg (Ideal.Quotient.mk I) hpx

instance Algebra.IsIntegral.quotient {I : Ideal A} [Algebra.IsIntegral R A] :
    Algebra.IsIntegral (R ⧸ I.comap (algebraMap R A)) (A ⧸ I) :=
  ⟨RingHom.IsIntegral.quotient (algebraMap R A) Algebra.IsIntegral.isIntegral⟩

theorem isIntegral_quotientMap_iff {I : Ideal S} :
    (Ideal.quotientMap I f le_rfl).IsIntegral ↔
      ((Ideal.Quotient.mk I).comp f : R →+* S ⧸ I).IsIntegral := by
  let g := Ideal.Quotient.mk (I.comap f)
  -- Porting note: added type ascription
  have : (Ideal.quotientMap I f le_rfl).comp g = (Ideal.Quotient.mk I).comp f :=
    Ideal.quotientMap_comp_mk le_rfl
  refine ⟨fun h => ?_, fun h => RingHom.IsIntegral.tower_top g _ (this ▸ h)⟩
  refine this ▸ RingHom.IsIntegral.trans g (Ideal.quotientMap I f le_rfl) ?_ h
  exact g.isIntegral_of_surjective Ideal.Quotient.mk_surjective

/-- If the integral extension `R → S` is injective, and `S` is a field, then `R` is also a field. -/
theorem isField_of_isIntegral_of_isField {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S]
    (hRS : Function.Injective (algebraMap R S)) (hS : IsField S) : IsField R := by
  have := hS.nontrivial; have := Module.nontrivial R S
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {a} ha ↦ ?_⟩
  -- Let `a_inv` be the inverse of `algebraMap R S a`,
  -- then we need to show that `a_inv` is of the form `algebraMap R S b`.
  obtain ⟨a_inv, ha_inv⟩ := hS.mul_inv_cancel fun h ↦ ha (hRS (h.trans (RingHom.map_zero _).symm))
  letI : Invertible a_inv := (Units.mkOfMulEqOne a_inv _ <| mul_comm _ a_inv ▸ ha_inv).invertible
  -- Let `p : R[X]` be monic with root `a_inv`,
  obtain ⟨p, p_monic, hp⟩ := Algebra.IsIntegral.isIntegral (R := R) a_inv
  -- and `q` be `p` with coefficients reversed (so `q(a) = q'(a) * a + 1`).
  -- We have `q(a) = 0`, so `-q'(a)` is the inverse of `a`.
  use -p.reverse.divX.eval a -- -q'(a)
  nth_rewrite 1 [mul_neg, ← eval_X (x := a), ← eval_mul, ← p_monic, ← coeff_zero_reverse,
    ← add_eq_zero_iff_neg_eq, ← eval_C (a := p.reverse.coeff 0), ← eval_add, X_mul_divX_add,
    ← (injective_iff_map_eq_zero' _).mp hRS, ← aeval_algebraMap_apply_eq_algebraMap_eval]
  rwa [← eval₂_reverse_eq_zero_iff] at hp

theorem isField_of_isIntegral_of_isField' {R S : Type*} [CommRing R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] (hR : IsField R) : IsField S := by
  refine ⟨⟨0, 1, zero_ne_one⟩, mul_comm, fun {x} hx ↦ ?_⟩
  have : Module.Finite R (adjoin R {x}) := ⟨(Submodule.fg_top _).mpr
    (Algebra.IsIntegral.isIntegral x).fg_adjoin_singleton⟩
  letI := hR.toField
  obtain ⟨y, hy⟩ := FiniteDimensional.exists_mul_eq_one R
    (K := adjoin R {x}) (x := ⟨x, subset_adjoin rfl⟩) (mt Subtype.ext_iff.mp hx)
  exact ⟨y, Subtype.ext_iff.mp hy⟩

theorem Algebra.IsIntegral.isField_iff_isField {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain S] [Algebra R S] [Algebra.IsIntegral R S]
    (hRS : Function.Injective (algebraMap R S)) : IsField R ↔ IsField S :=
  ⟨isField_of_isIntegral_of_isField', isField_of_isIntegral_of_isField hRS⟩

end Algebra

theorem integralClosure_idem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] :
    integralClosure (integralClosure R A : Set A) A = ⊥ :=
  letI := (integralClosure R A).algebra
  eq_bot_iff.2 fun x hx ↦ Algebra.mem_bot.2
    ⟨⟨x, isIntegral_trans (A := integralClosure R A) x hx⟩, rfl⟩

section IsDomain

variable {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [Algebra R S]

instance : IsDomain (integralClosure R S) :=
  inferInstance

theorem roots_mem_integralClosure {f : R[X]} (hf : f.Monic) {a : S}
    (ha : a ∈ f.aroots S) : a ∈ integralClosure R S :=
  ⟨f, hf, (eval₂_eq_eval_map _).trans <| (mem_roots <| (hf.map _).ne_zero).1 ha⟩

end IsDomain
