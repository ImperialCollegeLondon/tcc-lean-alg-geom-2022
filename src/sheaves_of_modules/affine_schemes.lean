import algebra.category.Module.abelian
import sheaves_of_modules.defs
import algebraic_geometry.AffineScheme
import algebra.module.localized_module


/-

# Construction of sheaf of modules on Spec(R) associated to a module

-/

-- last week we defined sheaves of modules on a sheaf of rings
-- and "proved" they were a category
-- this week let's make an example

-- remark: there's a Lean repository where I push stuff
-- git@github.com:ImperialCollegeLondon/tcc-lean-alg-geom-2022.git

-- `leanproject get ImperialCollegeLondon/tcc-lean-alg-geom-2022`
-- should get it you

-- Let R be a ring and let M be an R-module

-- this says "let R be a commutative ring which is also a set"
variables {R : CommRing.{0}} -- zero means "it's a set"
-- let M be a module over R which is also a set
variable (M : Module.{0} R)

-- goal: to make a sheaf of modules over Spec(R)

-- two distinct (as far as I know) constructions.
/-

-- (1) (Stacks project, EGA) : If U=D(f) is a basic open subset
-- then define 𝓜(U) := M[1/f]
-- Now use some formal nonsense to extend to all open subsets

Problem with (1) is that can have U=D(f)=D(g) but strictly speaking
M[1/f] ≠ M[1/g]

  (2) (Hartshorne): define on all open sets at once:
  𝓜(U) := {f : U → disjoint union of M_P such that 
   (a) f(P) ∈ M_P (i.e. f is a dependent function: f : Π (P : U), M_P )
   (b) f is "locally a fraction" i.e. for all P there exists some nhd V
   of P and elements m ∈ M and r ∈ R non-vanishing on V such that
   f(Q)=m/r for all Q in V
   
   Hartshorne defines structure sheaf on Spec(R) in this way
  }

We're going to go for (2) becuase it avoids "canonical isomorphism"
  nonsense which is hard to make rigorous in Lean's type theory

NB variant (1') : If U is a basic open then you can define
 𝓜(U)=M[1/S] where S is all the elements of R which are nonvanishing on U
 and this avoids the problem; it's much more functorial

-/

-- let's see how they do it for rings

open algebraic_geometry

--#check AffineScheme

/-

First we'll define the sheaf of functions sending U to {f : U -> disjoint union of M_P
such that F(P) ∈ M_P}
-/

--#check localized_module

open category_theory

namespace Module

/--
The type family over `prime_spectrum R` consisting of the localization of a module
over each point.
-/
@[derive add_comm_group]
def localizations (P : prime_spectrum.Top R) : Type := localized_module (P.as_ideal.prime_compl) M

instance (P : prime_spectrum.Top R) : module (structure_sheaf.localizations R P) (M.localizations P) := 
localized_module.is_module

/-
Then we'll define a predicate called "is_locally_fraction"
-/

open topological_space

/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`m / s` in each of the stalks (which are localizations of a fixed module at various prime ideals).
-/
def is_fraction {U : opens (prime_spectrum.Top R)} (f : Π (P : U), M.localizations P) : Prop :=
∃ (m : M) (s : R), ∀ P : U, ∃ (hs : s ∈ (prime_spectrum.as_ideal (P.1 : prime_spectrum R)).prime_compl),
  f P = localized_module.mk m ⟨s, hs⟩

open Top

/--
The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (M.localizations) :=
{ pred := λ U f, M.is_fraction f,
  res := by { rintro V U i f ⟨r, s, w⟩, exact ⟨r, s, λ x, w (i x)⟩ } }

/-- A dependent section f : Π (P : U), M_P is locally a fraction
if U has an open cover such that the restriction of f to the cover
is a fraction m/s -/
def is_locally_fraction : local_predicate (M.localizations) :=
(M.is_fraction_prelocal).sheafify

/-
Then we'll make a sheaf of tyhpes
-/
/--
The sheaf of modules associated to M (valued in `Type`, not yet `Ab`) is the subsheaf consisting of
functions satisfying `is_locally_fraction`.
-/
def sheaf_in_Type : sheaf (Type) (prime_spectrum.Top R):=
subsheaf_to_Types (M.is_locally_fraction)

open opposite

/-
Then we'll show that each of these types is an abelian group
-/

instance sections_module (U : (opens (prime_spectrum.Top R))ᵒᵖ) :
  module ((structure_presheaf_in_CommRing R).obj U) (Π P : unop U, M.localizations P) :=
{ smul := λ f m P, (f.1 P) • m P,
  one_smul := sorry,
  mul_smul := sorry,
  smul_zero := sorry,
  smul_add := sorry,
  add_smul := sorry,
  zero_smul := sorry }

/--
The functions satisfying `is_locally_fraction` form a subgroup.
-/
def sections_submodule' (U : (opens (prime_spectrum.Top R))ᵒᵖ) :
  submodule ((structure_presheaf_in_CommRing R).obj U) (Π P : unop U, M.localizations P) :=
{ carrier := { f | (M.is_locally_fraction).pred f },
  zero_mem' :=
  begin
    refine λ x, ⟨unop U, x.2, 𝟙 _, 0, 1, λ y, ⟨_, _⟩⟩,
    { change (1 : R) ∉ prime_spectrum.as_ideal y.val,
      rw ←ideal.ne_top_iff_one, exact y.1.is_prime.1, },
    { simp, },
  end,
  -- neg_mem' :=
  -- begin
  --   intros a ha x,
  --   rcases ha x with ⟨V, hxV, i, m, s, hm⟩,
  --   refine ⟨V, hxV, i, -m, s, _⟩,
  --   intro y,
  --   rcases hm y with ⟨hs, w⟩,
  --   use hs,
  --   dsimp only at w ⊢,
  --   simp only [w, pi.neg_apply],
  --   apply localized_module.mk_neg,
  -- end,
  add_mem' :=
  begin
    intros a b ha hb x,
    rcases ha x with ⟨Va, ma, ia, ra, sa, wa⟩,
    rcases hb x with ⟨Vb, mb, ib, rb, sb, wb⟩,
    refine ⟨Va ⊓ Vb, ⟨ma, mb⟩, opens.inf_le_left _ _ ≫ ia, sb • ra + sa • rb, sa * sb, _⟩,
    intro y,
    rcases wa (opens.inf_le_left _ _ y) with ⟨nma, wa'⟩,
    rcases wb (opens.inf_le_right _ _ y) with ⟨nmb, wb'⟩,
    fsplit,
    { intro H, cases y.1.is_prime.mem_or_mem H; contradiction, },
    dsimp only at wa' wb' ⊢,
    change a (ia ((Va.inf_le_left Vb) y)) + b (ib ((Va.inf_le_right Vb) y)) = _,
    rw [wa', wb'],
    refl,
  end,
  smul_mem' :=
  begin 
    sorry
  end, }

instance add_comm_group_sheaf_in_Type_obj (U : (opens (prime_spectrum.Top R))ᵒᵖ) :
  add_comm_group ((M.sheaf_in_Type).1.obj U) :=
(M.sections_submodule' U).to_add_subgroup.to_add_comm_group

instance module_sheaf_in_Type_obj (U : (opens (prime_spectrum.Top R))ᵒᵖ) :
  module ((structure_presheaf_in_CommRing R).obj U) ((M.sheaf_in_Type).1.obj U) :=
submodule_class.to_module (M.sections_submodule' U)

/-
Then we'll make a presheaf of abelian groups
-/

/--
The presheaf, valued in `Ab`, constructed by dressing up the `Type` valued
presheaf associated to an R-module.
-/
@[simps] 
def presheaf_in_Ab : presheaf Ab (prime_spectrum.Top R) :=
{ obj := λ U, AddCommGroup.of ((M.sheaf_in_Type).1.obj U),
  map := λ U V i,
  { to_fun := ((M.sheaf_in_Type).1.map i),
    map_zero' := rfl,
    map_add' := λ x y, rfl, }, }


/--
Some glue, verifying that that structure presheaf valued in `CommRing` agrees
with the `Type` valued structure presheaf.
-/
def presheaf_comp_forget :
  M.presheaf_in_Ab ⋙ (category_theory.forget Ab) ≅ (M.sheaf_in_Type).1 :=
nat_iso.of_components
  (λ U, iso.refl _)
  (by tidy)

open Top.presheaf

/--
The structure sheaf on $Spec R$, valued in `CommRing`.

This is provided as a bundled `SheafedSpace` as `Spec.SheafedSpace R` later.
-/
def sheaf : sheaf Ab (prime_spectrum.Top R) :=
⟨M.presheaf_in_Ab,
  -- We check the sheaf condition under `forget CommRing`.
  (is_sheaf_iff_is_sheaf_comp _ _).mpr
    (is_sheaf_of_iso (M.presheaf_comp_forget).symm
      (M.sheaf_in_Type).cond)⟩

/-
and then we'll beef it up into a sheaf of modules
-/

#check Scheme

def sheaf_of_modules: SHEAF_OF_MODULES (Spec.to_LocallyRingedSpace.obj (op R)).to_SheafedSpace :=
{ ab_sheaf := M.sheaf,
  module_structure := M.module_sheaf_in_Type_obj,
  compatibility_bit := sorry
}

end Module