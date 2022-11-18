import algebraic_geometry.AffineScheme
import sheaves_of_modules.defs
import algebra.category.Module.limits
import algebra.module.localized_module

/-

# Sheaf of modules associated to a module over a ring

-/

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
example : module (localization (P.as_ideal.prime_compl)) (localized_module (P.as_ideal.prime_compl) M) := infer_instance

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

example : module (localization (P.as_ideal.prime_compl)) (localized_module (P.as_ideal.prime_compl) M) := infer_instance


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
def Module.is_fraction_prelocal : prelocal_predicate (M.localizations) :=
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

def sections_subring (U : (opens (prime_spectrum.Top R))ᵒᵖ) :
  add_subgroup (Π x : unop U, M.localizations x) :=
{ carrier := { f | (M.is_locally_fraction).pred f },
  zero_mem' := begin
    rintro ⟨x, hx⟩,
    use [unop U, hx, 𝟙 _, 0, 1],
    intro y,
    refine ⟨_, by squeeze_simp⟩ ,
  end,
  neg_mem' := sorry,
  add_mem' := begin
    intros a b ha hb x,
    sorry,
  end,
}


instance (U) : add_comm_group ((M.sheaf_in_Type).1.obj U) :=
begin
  delta sheaf_in_Type,
  delta subsheaf_to_Types,
  dsimp only,
  delta subpresheaf_to_Types,
  dsimp only,
  apply_instance,
end

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
  map := _,
  map_id' := _,
  map_comp' := _ }

#exit
def Module.to_presheaf_in_Type
def  Module.to_presheaf : presheaf.{0} Ab.{0} (forget_to_Top.obj (Spec.obj (opposite.op R)) : Top.{0}) :=
{ obj := λ U, _,
  map := _,
  map_id' := _,
  map_comp' := _ }