import algebraic_geometry.AffineScheme
import sheaves_of_modules.defs
import algebra.category.Module.limits
import algebra.module.localized_module

/-

# Sheaf of modules associated to a module over a ring

This was *practice* for the 2nd alg geom lecture
-/

--open Module.category_theory -- puzzle

variables {R : CommRing.{0}} (M : Module.{0} R)

open algebraic_geometry

open Top

open algebraic_geometry.Scheme

--@[derive [comm_ring, local_ring]]
--def localizations (P : prime_spectrum.Top R) : Type u := localization.at_prime P.as_ideal

-- protected abbreviation localization.at_prime := localization I.prime_compl

variable (P : prime_spectrum.Top R)

-- #check P.as_ideal.prime_compl -- submonoid R

--#check localized_module (P.as_ideal.prime_compl) M

-- works
example : module (localization (P.as_ideal.prime_compl)) 
  (localized_module (P.as_ideal.prime_compl) M) := infer_instance

namespace Module

@[derive add_comm_group]
def localizations (P : prime_spectrum.Top R) := localized_module (P.as_ideal.prime_compl) M

--instance (P : prime_spectrum.Top R) : module (localization (P.as_ideal.prime_compl))
--  (M.localizations P) := by unfold Module.localizations; apply_instance

/-
/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`r / s` in each of the stalks (which are localizations at various prime ideals).
-/
def is_fraction {U : opens (prime_spectrum.Top R)} (f : Π x : U, localizations R x) : Prop :=
∃ (r s : R), ∀ x : U,
  ¬ (s ∈ x.1.as_ideal) ∧ f x * algebra_map _ _ s = algebra_map _ _ r

lemma is_fraction.eq_mk' {U : opens (prime_spectrum.Top R)} {f : Π x : U, localizations R x}
  (hf : is_fraction f) :
  ∃ (r s : R) , ∀ x : U, ∃ (hs : s ∉ x.1.as_ideal), f x =
    is_localization.mk' (localization.at_prime _) r
      (⟨s, hs⟩ : (x : prime_spectrum.Top R).as_ideal.prime_compl) :=
begin
  rcases hf with ⟨r, s, h⟩,
  refine ⟨r, s, λ x, ⟨(h x).1, (is_localization.mk'_eq_iff_eq_mul.mpr _).symm⟩⟩,
  exact (h x).2.symm,
end

variables (R)

/--
The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (localizations R) :=
{ pred := λ U f, is_fraction f,
  res := by { rintro V U i f ⟨r, s, w⟩, exact ⟨r, s, λ x, w (i x)⟩ } }
-/

--#check structure_sheaf.is_fraction 
/-
def is_fraction {U : opens (prime_spectrum.Top R)} (f : Π x : U, localizations R x) : Prop :=
∃ (r s : R), ∀ x : U,
  ¬ (s ∈ x.1.as_ideal) ∧ f x * algebra_map _ _ s = algebra_map _ _ r
-/

example : module (localization (P.as_ideal.prime_compl)) 
  (localized_module (P.as_ideal.prime_compl) M) := infer_instance


/--
The predicate saying that a dependent function on an open `U` valued in localisations of
a module `M` is realised as a fixed fraction `m / s` in each of the stalks (which are 
localizations at various prime ideals).
-/
def is_fraction {U : topological_space.opens ↥(prime_spectrum.Top R)}
  (f : Π (x : ↥U), M.localizations ↑x) : Prop :=
∃ (m : M) (s : R), ∀ x : U, ¬ (s ∈ x.1.as_ideal) ∧
  (algebra_map _ (localization (x.1.as_ideal.prime_compl)) s) • 
  (id (f x) : localized_module (x.1.as_ideal.prime_compl) M) = 
  localized_module.mk_linear_map (x.1.as_ideal.prime_compl) M m

/--
The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (M.localizations) :=
{ pred := λ U f, M.is_fraction f,
  res := by { rintro V U i f ⟨r, s, w⟩, exact ⟨r, s, λ x, w (i x)⟩ } }

def is_locally_fraction : local_predicate (M.localizations) :=
(M.is_fraction_prelocal).sheafify

/-
def structure_presheaf_in_CommRing : presheaf CommRing (prime_spectrum.Top R) :=
{ obj := λ U, CommRing.of ((structure_sheaf_in_Type R).1.obj U),
  map := λ U V i,
  { to_fun := ((structure_sheaf_in_Type R).1.map i),
    map_zero' := rfl,
    map_add' := λ x y, rfl,
    map_one' := rfl,
    map_mul' := λ x y, rfl, }, }
-/

/-
/--
The structure sheaf (valued in `Type`, not yet `CommRing`) is the subsheaf consisting of
functions satisfying `is_locally_fraction`.
-/
def structure_sheaf_in_Type : sheaf (Type u) (prime_spectrum.Top R):=
subsheaf_to_Types (is_locally_fraction R)
-/

--instance (x : prime_spectrum.Top R) : add_comm_group (M.localizations x) := infer_instance

def sheaf_in_Type : sheaf (Type) (prime_spectrum.Top R):=
subsheaf_to_Types (M.is_locally_fraction)

open topological_space opposite

--#check structure_presheaf_in_CommRing
def sections_add_subgroup (U : (opens (prime_spectrum.Top R))ᵒᵖ) :
  add_subgroup (Π x : unop U, M.localizations x) :=
{ carrier := { f | (M.is_locally_fraction).pred f },
  zero_mem' := begin
    rintro ⟨x, hx⟩,
    use [unop U, hx, 𝟙 _, 0, 1],
    intro y,
    refine ⟨_, _⟩,
    { rw ←ideal.ne_top_iff_one, exact y.1.is_prime.1, },
    { simp only [pi.zero_apply, id.def, smul_zero, localized_module.mk_linear_map_apply, 
        localized_module.zero_mk]},
  end,
  neg_mem' := begin
    intros f hf x,
    obtain ⟨V, hV, i, m, s, hmfs⟩ := hf x,
    refine ⟨V, hV, i, -m, s, λ y, _⟩,
    obtain ⟨h1, h2⟩ := hmfs y,
    refine ⟨h1, _⟩,
    simp only [id.def, pi.neg_apply, algebra_map_smul, smul_neg, 
      localized_module.mk_linear_map_apply] at h2 ⊢,
    rw h2,
    refl,
  end,
  add_mem' := begin
    intros a b ha hb x,
    obtain ⟨V, hV, i, m, s, hms⟩ := ha x,
    obtain ⟨W, hW, j, n, t, hnt⟩ := hb x,
    use V ⊓ W,
    refine ⟨⟨hV,hW⟩, opens.inf_le_left _ _ ≫ i, t • m + s • n, s * t, λ y, _⟩,
    obtain ⟨hs, hsa⟩ := hms ⟨y.1, y.2.1⟩,
    obtain ⟨ht, htb⟩ := hnt ⟨y.1, y.2.2⟩,
    split,
    { intro H, cases y.1.is_prime.mem_or_mem H; contradiction, },
    { simp only [pi.add_apply, id.def, smul_add, algebra_map_smul],
      rw [mul_smul _ _ (b _), mul_comm, mul_smul, linear_map.map_add, linear_map.map_smul,
        linear_map.map_smul],
      congr', },
  end,
}


instance (U) : add_comm_group ((M.sheaf_in_Type).1.obj U) :=
(M.sections_add_subgroup U).to_add_comm_group

/-
/--
The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type` valued
structure presheaf.
-/
@[simps]
def structure_presheaf_in_CommRing : presheaf CommRing (prime_spectrum.Top R) :=
{ obj := λ U, CommRing.of ((structure_sheaf_in_Type R).1.obj U),
  map := λ U V i,
  { to_fun := ((structure_sheaf_in_Type R).1.map i),
    map_zero' := rfl,
    map_add' := λ x y, rfl,
    map_one' := rfl,
    map_mul' := λ x y, rfl, }, }

-/

def presheaf_in_Ab : presheaf Ab.{0} (prime_spectrum.Top R):=
{ obj := λ U, AddCommGroup.of ((M.sheaf_in_Type).1.obj U),
  map := λ U V i, 
  { to_fun := (M.sheaf_in_Type).1.map i,
    map_zero' := rfl,
    map_add' := λ x y, rfl, }, }

open _root_.category_theory

def presheaf_comp_forget :
  M.presheaf_in_Ab ⋙ (forget Ab) ≅ (M.sheaf_in_Type).1 :=
nat_iso.of_components
  (λ U, iso.refl _)
  (by tidy)

/--
The abelian sheaf on $Spec R$ associated to an R-module M, valued in `Ab`.
-/
def ab_sheaf : sheaf Ab (prime_spectrum.Top R) :=
⟨M.presheaf_in_Ab, (presheaf.is_sheaf_iff_is_sheaf_comp _ _).mpr 
    (presheaf.is_sheaf_of_iso (M.presheaf_comp_forget).symm
      (M.sheaf_in_Type).cond)⟩

def ab_sheaf.global_section_map : M →+ M.ab_sheaf.1.obj (opposite.op ⊤) :=
{ to_fun := λ m, ⟨λ x, localized_module.mk_linear_map _ _ m, begin
    intro x,
    use [⊤, by simp only [subtype.val_eq_coe, localized_module.mk_linear_map_apply, exists_prop]],
    use 𝟙 _,
    use m,
    use 1,
    intro y,
    split,
    { rw ←ideal.ne_top_iff_one, exact y.1.is_prime.1, },
    { simp only [map_one, localized_module.mk_linear_map_apply, id.def, one_smul], },
  end⟩,
  map_zero' := rfl,
  map_add' :=λ a b, begin
    ext,
    simp only [localized_module.mk_linear_map_apply, subtype.coe_mk],
    congr';
    simp,
  end }

def sheaf_of_modules: SHEAF_OF_MODULES (Spec.obj (opposite.op R)).to_LocallyRingedSpace.to_RingedSpace :=
{ ab_sheaf := M.ab_sheaf,
  module_structure := λ U, 
  { smul := λ r m, ⟨λ y, begin
      let foo := r.1 y,
      delta Module.localizations,
      delta structure_sheaf.localizations at foo,
      exact foo • (m.1 y),
    end, begin
--      simp only [subtype.val_eq_coe, id.def],
      intro y,
      obtain ⟨W ,hmW, iW, rW, sW, hW⟩ := r.2 y,
      obtain ⟨X ,hmX, iX, mX, rX, hX⟩ := m.2 y,
      use W ⊓ X,
      refine ⟨⟨hmW, hmX⟩, _⟩,
      use opens.inf_le_left _ _ ≫ iW,
      refine ⟨rW • mX, _⟩,
      use sW * rX,
      rintro ⟨y, hWy, hXy⟩,
      obtain ⟨hsW1, hsW2⟩ := hW ⟨y, hWy⟩,
      obtain ⟨hrX1, hrX2⟩ := hX ⟨y, hXy⟩,
      split,
      { intro H, cases y.is_prime.mem_or_mem H; contradiction },
      simp at hsW2 hrX2 ⊢,
      rw smul_comm,
      --swap, simp,
      --simp at hW,
      /-
      Exists s ∈ R such that s non-vanishing on W ∩ X
      and ∀ x ∈ W ∩ X, s • r(x) • m(x) = ?m_1 ∈ M
      know hsW2: r(x)*sW=rW
      and hrX2 : rX•m(x)=mX ∈ M
      let's try sW*rX?
      rW*mX
      -/
      sorry,
    end⟩,
    one_smul := sorry,
    mul_smul := sorry,
    smul_zero := sorry,
    smul_add := sorry,
    add_smul := sorry,
    zero_smul := sorry },
  compatibility_bit := sorry }

end Module

