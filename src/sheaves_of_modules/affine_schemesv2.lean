import algebra.category.Module.abelian
import sheaves_of_modules.defs
import algebraic_geometry.AffineScheme
import algebra.module.localized_module


/-

# Construction of sheaf of modules on Spec(R) associated to a module

-/

-- last week we defined sheaves of modules on a sheaf of rings
-- and gave them the structure of a category
-- this week let's make an example of a sheaf of modules

-- remark: there's a Lean repository where I push stuff
-- git@github.com:ImperialCollegeLondon/tcc-lean-alg-geom-2022.git

-- `leanproject get ImperialCollegeLondon/tcc-lean-alg-geom-2022`
-- should get it you

-- Let R be a ring and let M be an R-module

-- this says "let R be a commutative ring which is also a set"
variables {R : Type} [comm_ring R] -- zero means "it's a set"
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
   and mathlib defines it like this too.
  }

We're going to go for (2) becuase it avoids "canonical isomorphism"
  nonsense which is hard to make rigorous in Lean's type theory

NB variant (1') : If U is a basic open then you can define
 𝓜(U)=M[1/S] where S is all the elements of R which are nonvanishing on U
 and this avoids the problem; it's much more functorial and this
 is what we did in the initial schemes project.

-/

-- In the below we just copy what they do for rings

-- apparently this API is missing from mathlib
def prime_spectrum.prime_compl (Q : prime_spectrum R) : submonoid R := Q.as_ideal.prime_compl

open algebraic_geometry category_theory

namespace Module

/--
`M.localizations P` : The type family over `(P : prime_spectrum.Top R)` consisting of the localization 
`M_P` of the module `R`-module `M` over each point.
-/
@[reducible, derive add_comm_group]
def localizations (P : prime_spectrum R) : Type := localized_module (P.prime_compl) M

-- Jujian says
-- * Redefine `localization` for monoids and rings to coincide with `localized_module`.
-- is a project

/-
protected abbreviation localization.at_prime := localization I.prime_compl
-/

/-- Let type class inference see through the `M.localizations` definition and
  recognise the `R_P`-module structure on `M.localizations P := M_P` -/
instance (P : prime_spectrum R) : module (structure_sheaf.localizations R P) (M.localizations P) := 
localized_module.is_module -- definitional equality.

/-
Then we'll define a predicate called "is_locally_fraction"
-/

open topological_space

/--
The predicate saying that a dependent function on an open `U` is realised as a fixed fraction
`m / s` in each of the stalks (which are localizations of a fixed module at various prime ideals).
-/
def is_fraction {U : opens (prime_spectrum R)} (f : Π (P : U), M.localizations P) : Prop :=
∃ (m : M) (s : R), ∀ P : U, ∃ (hs : s ∈ (P.1 : prime_spectrum R).prime_compl),
  f P = localized_module.mk m ⟨s, hs⟩

open Top

/--
The predicate `is_fraction` is "prelocal",
in the sense that if it holds on `U` it holds on any open subset `V` of `U`.
-/
def is_fraction_prelocal : prelocal_predicate (id (M.localizations) : (prime_spectrum.Top R : Type) → Type) :=
{ pred := λ U f, M.is_fraction f,
  res := by { rintro V U i f ⟨r, s, w⟩, exact ⟨r, s, λ x, w (i x)⟩ } }

/-- A dependent section f : Π (P : U), M_P is locally a fraction
if U has an open cover such that the restriction of f to the cover
is a fraction m/s -/
def is_locally_fraction : local_predicate (id (M.localizations): (prime_spectrum.Top R : Type) → Type) :=
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

def Spec.structure_sheaf' (R : Type) [comm_ring R] : sheaf CommRing (bundled.mk (prime_spectrum R) : Top.{0}) := 
Spec.structure_sheaf R

noncomputable def algebraic_geometry.structure_sheaf.to_stalk' (R : Type*) [comm_ring R] 
  (x : prime_spectrum R) :
  CommRing.of R ⟶ (Spec.structure_sheaf R).presheaf.stalk x :=
algebraic_geometry.structure_sheaf.to_stalk R x

--#print algebraic_geometry.structure_sheaf.to_stalk
-- : Π (R : Type u) [_inst_1 : comm_ring R] (x : ↥(prime_spectrum.Top R)), CommRing.of R ⟶ (structure_sheaf R).presheaf.stalk x


--#check comm_ring
--#check CommRing.comm_ring

--set_option pp.all true
instance sections_module (U : (opens (prime_spectrum R))ᵒᵖ) :
  module ((Spec.structure_sheaf' R).val.obj U) (Π P : unop U, M.localizations P) :=
{ smul := λ f m P, (f.1 P) • m P,
--begin 
--  change ↥((Spec.structure_sheaf' R).val.obj U) at f,
--  let moo : _ →+* _ := algebraic_geometry.structure_sheaf.to_stalk' R P,
  --simp at moo,
  -- exact (f.stalk P) • m P,
--  sorry,
--end,
  one_smul := begin
    intro f,
    ext,
    simp,
--    norm_cast,
--    simp only [subtype.val_eq_coe],
    let foo : structure_sheaf.localizations R (x.1 : (prime_spectrum R)) := 1,
    --change foo • f x = f x,--    simp,
    delta has_one.one,
    sorry,
  end,
  mul_smul := sorry,
  smul_zero := sorry,
  smul_add := sorry,
  add_smul := sorry,
  zero_smul := sorry }

/--
The functions satisfying `is_locally_fraction` form a subgroup.
-/
def sections_submodule' (U : (opens (prime_spectrum R))ᵒᵖ) :
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

--#check Scheme

def sheaf_of_modules: SHEAF_OF_MODULES (Spec.to_LocallyRingedSpace.obj (op R)).to_SheafedSpace :=
{ ab_sheaf := M.sheaf,
  module_structure := M.module_sheaf_in_Type_obj,
  compatibility_bit := sorry
}

end Module