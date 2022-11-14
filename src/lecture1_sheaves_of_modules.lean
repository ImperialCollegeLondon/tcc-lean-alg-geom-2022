import algebraic_geometry.ringed_space
import algebraic_geometry.Scheme
import algebra.category.Group.abelian

/-

# Sheaves of modules


Let `X` be a ringed space, with sheaf of rings `𝓞 X`. We define a large category
`SHEAF_OF_MODULES X` whose objects are the sheaves of 𝓞_ X -modules for this sheaf of rings.

-/

/-

## Making some large categories

We attach all-caps names to various large categories we'll use.

-/

open algebraic_geometry topological_space category_theory

-- We will use ALL_CAPS in the type theory names for concepts which a ZFC person would call
-- a "large category", i.e. a category where there might be more than a set's worth of objects,
-- but all the hom sets are sets
abbreviation RINGED_SPACE := RingedSpace.{0}
-- Objects are `X : RINGED_SPACE`, and if `X Y : RINGED_SPACE` then the hom type
-- `X ⟶ Y : Type` is indeed in `Type`. This says "If X,Y are objects, Hom(X,Y) is a set".
-- Note that `RINGED_SPACE` itself has type `Type 1`, because its objects do not form a set.
abbreviation TOP := Top.{0} -- large cat of top spaces
abbreviation AB := Ab.{0} -- large cat of ab gps

-- this should be hidden
@[derive category]
def TOP.sheaf := Top.sheaf.{0}

notation `𝓞_ ` X := λ (U : (opens (X : TOP))ᵒᵖ), X.presheaf.obj U

section examples
-- Thanks to the genius of Scott Morrison, this stuff now *just works*.
-- Except we have to keep track of the universes to prove we're doing set theory.

variables (X : RINGED_SPACE) (U : (opens (X :  TOP))ᵒᵖ) (r : (𝓞_ X) U)
-- don't know how to do
-- 𝓞_X notation. Ideally I want 𝓞ₐ but with `X` not `a`. Can it be done in Lean 4?
-- And I don't care if there's no unicode subscript capital X, it's what we want
-- to write and if we can't then can we please have LaTeX somehow?

variables (f : (𝓞_ X) U →+* (𝓞_ X) U)
variables (V : (opens (X :  TOP))ᵒᵖ)  (i : U ⟶ V)
example : (𝓞_ X) U ⟶ (𝓞_ X) V := X.presheaf.map i

end examples

-- This should be hidden and probably PR'ed
namespace category_theory.Sheaf.hom

open category_theory

@[simp] lemma neg_app {C : Type*} [category C] {J : grothendieck_topology C} {A : Type*}
  [category A] [preadditive A] {P Q : Sheaf J A} (f : P ⟶ Q) (U : Cᵒᵖ) :
    (-f).val.app U = -f.val.app U := rfl

@[simp] lemma zero_app {C : Type*} [category C] {J : grothendieck_topology C} {A : Type*}
  [category A] [preadditive A] {P Q : Sheaf J A} (U : Cᵒᵖ) :
    (0 : P ⟶ Q).val.app U = (0 : P.val.obj U ⟶ Q.val.obj U) := rfl

end category_theory.Sheaf.hom

-- can't find a sensible constructor for `add_comm_group`
-- this needs hiding
namespace add_comm_group

def mk' {G : Type*} [has_add G] [has_zero G] [has_neg G]
  (ax1 : ∀ a b c : G, (a + b) + c = a + (b + c))
  (ax2 : ∀ a b : G, a + b = b + a)
  (ax3 : ∀ a : G, 0 + a = a)
  (ax4 : ∀ a : G, -a + a = 0) : add_comm_group G :=
{ add := (+),
  add_assoc := ax1,
  zero := 0,
  zero_add := ax3,
  add_zero := λ a, by {rw ax2, exact ax3 a},
  neg := has_neg.neg,
  add_left_neg := ax4,
  add_comm := ax2 }

def mk'' {G : Type*} [has_add G] [has_zero G] [has_neg G] : add_comm_group G :=
{ add := (+), zero := 0, neg := has_neg.neg,
  add_assoc := sorry, -- happy to prove this
  add_comm := sorry,  -- and this
  zero_add := sorry,  -- and this
  add_left_neg := sorry,  -- and this
  add_zero := λ a, by sorry,-- but now I want to cheat and can't get this to work:
  -- `by{rw add_comm, apply add_left_neg }, -- I mean "the proofs I just did above"`
}

end add_comm_group

namespace AddCommGroup

-- this needs hiding and probably PR'ing
lemma ext_iff (G H : AddCommGroup) (f₁ f₂ : G ⟶ H) : f₁ = f₂ ↔ ∀ (x : ↥G), f₁ x = f₂ x :=
begin
  split,
  { rintro rfl, intros, refl, },
  { apply AddCommGroup.ext, },
end

end AddCommGroup

open category_theory

-- value of a sheaf is the functor, object of the functor is the function on objects.

/-
Tell them that
structure RINGED_SPACE :=
(X : TOP)
(𝓞_ X : TOP.sheaf COMM_RING ↑X)
-/
-- category of sheaves of modules on a ringed space
structure SHEAF_OF_MODULES (X : RINGED_SPACE) :=
-- now we have 𝓞_ X, a sheaf of rings on `X`.
(ab_sheaf : TOP.sheaf AB X) -- let ab_sheaf be a sheaf of abelian groups on X
-- An O_X-module structure on `ab_sheaf` is:
-- "an action of the ring `O_ X` on the (presheaf) abelian group `𝓜 := ab_sheaf.val`"?
-- Now work with presheaves only.
-- Now what does the action *mean*?
-- This is a bit which relates the value of `𝓞_X` on *objects*
-- to the value of `𝓜` on *objects*
(module_bit : ∀ U : (opens (X : TOP))ᵒᵖ, module ((𝓞_ X) U) (ab_sheaf.val.obj U))
-- Is this the part which relates the vcalue of `𝓞_X` on *morphisms*
-- to the value of `𝓜` on morphisms.
(compatibility_bit :
∀ (U V : (opens (X : TOP))ᵒᵖ) (f : U ⟶ V) (r : (𝓞_ X) U) (m : ab_sheaf.val.obj U), -- V ⊆ U
  -- need to get the value of the functor `𝓞_X` on morphism `f` and this is `α`
  X.presheaf.map f r • ab_sheaf.val.map f m = ab_sheaf.val.map f (r • m))
  -- need to state α(r) •V β(m) = β(r •U m)
  /-

coming from the values of the functors on the morphisms.

  α : O_X(U) --> O_X(V)

  β : M(U) -> M(V)

  choose r in O_X(U)
  choose m in M(U)
  r•m in M(U)
  β(r•m) in M(V)
  α(r) in O_X(V)
  β(m) in M(V)

  α(r)•β(m) in M(V)
α(r) •V β(m) = β(r •U m)
  -/

-- This is some weird algebraic geometry way of saying "let M be an R-module"



-- TODO need compatibility under restrictions U ⟶ V `change_of_ring.lean`

/-

## A word on universes.

If you do `#check sheaf_of_modules X`, you see that the output is `Type 1`.

That means `sheaf_of_modules Z` is what set theorists call a "large category".

More precisely, this means that the collection of all the objects in the category of
sheaves of modules for a fixed sheaf of rings may not itself be a set, but every object in
this category is a set, and as usual all the hom sets are also sets.

Let's make that large category instance in the `sheaf_of_modules` namespace.

-/

-- variables (J K : TOP.sheaf AB X)

-- example (J K : TOP.sheaf AB X) : false := begin
-- letI foo : quiver (TOP.sheaf AB X) := infer_instance,
-- sorry
-- end
-- #check J ⟶ K

namespace SHEAF_OF_MODULES

variables {X : RINGED_SPACE} (𝓜 𝓝 : SHEAF_OF_MODULES X)

def obj (𝓜 : SHEAF_OF_MODULES X) (U : (opens (X : TOP))ᵒᵖ) : AB := 𝓜.ab_sheaf.val.obj U

instance (𝓜 : SHEAF_OF_MODULES X) (U : (opens (X : TOP))ᵒᵖ) :
  module ((𝓞_ X) U) (𝓜.obj U) := 𝓜.module_bit U

example (𝓜 : SHEAF_OF_MODULES X) (U : (opens (X : TOP))ᵒᵖ) (r : (𝓞_ X) U)
  (m : 𝓜.ab_sheaf.val.obj U) : 𝓜.obj U := r • m

@[ext]
structure hom (𝓜 𝓝 : SHEAF_OF_MODULES X) : Type :=
(ab_sheaf : 𝓜.ab_sheaf ⟶ 𝓝.ab_sheaf)
(map_smul (U : (opens (X : TOP))ᵒᵖ) (r : (𝓞_ X) U) (m : 𝓜.obj U) :
  ab_sheaf.val.app U (r • m : 𝓜.obj U) =
    (r • ab_sheaf.val.app U m : 𝓝.obj U))

namespace hom

-- notational typeclass `⟶` for `hom`
instance : quiver (SHEAF_OF_MODULES X) := ⟨λ 𝓜 𝓝, hom 𝓜 𝓝⟩

/-- The ring homomorpisms on all open subsets associated to a morphism of sheaves of modules. -/
def sections {𝓜 𝓝 : SHEAF_OF_MODULES X} (φ : 𝓜 ⟶ 𝓝) (U : (opens (X : TOP))ᵒᵖ) :
𝓜.obj U →ₗ[(𝓞_ X) U] 𝓝.obj U :=
{ to_fun := φ.ab_sheaf.val.app U,
  map_add' := (φ.ab_sheaf.val.app U).map_add,
  map_smul' := φ.map_smul U }

-- @[simp]
-- lemma sections.eval (f : 𝓜.ab_sheaf ⟶ 𝓝.ab_sheaf)
--   (φ : Π (U : opens (X : TOP)), 𝓜.obj U →ₗ[(𝓞_ X)U] 𝓝.obj U )
--   (hφ : ∀ (U : opens (X : TOP)), (f, φ).fst.val.app (opposite.op U) = ((f, φ).snd U : 𝓜.obj U →+ 𝓝.obj U))
--   (U: opens (X : TOP)) :
-- hom.sections ⟨(f, φ), hφ⟩ U = φ U := rfl

-- @[simp] lemma aux_thing1 {𝓜 𝓝 : SHEAF_OF_MODULES X} (φ : 𝓜 ⟶ 𝓝) :
--   (↑φ : (𝓜.ab_sheaf ⟶ 𝓝.ab_sheaf) × (Π (U : opens (X : TOP)), 𝓜.obj U →ₗ[(𝓞_ X) U] 𝓝.obj U)).fst
--   = φ.ab_sheaf := by refl

-- @[simp] lemma aux_thing2 {𝓜 𝓝 : SHEAF_OF_MODULES X} (φ : 𝓜 ⟶ 𝓝) :
--   (↑φ : (𝓜.ab_sheaf ⟶ 𝓝.ab_sheaf) × (Π (U : opens (X : TOP)), 𝓜.obj U →ₗ[(𝓞_ X) U] 𝓝.obj U)).snd
--   = φ.sections := by refl

instance : has_zero (𝓜 ⟶ 𝓝) := ⟨
  { ab_sheaf := 0,
  map_smul := λ U r m, begin
    simp only [Sheaf.hom.zero_app, AddCommGroup.zero_apply, smul_zero],
  end }⟩


@[simp] lemma ab_sheaf_zero : (0 : 𝓜 ⟶ 𝓝).ab_sheaf = 0 :=
rfl

instance : has_neg (𝓜 ⟶ 𝓝) := ⟨λ φ,
{ ab_sheaf := -φ.ab_sheaf,
  map_smul := λ U r m, begin
    simp only [φ.map_smul, Sheaf.hom.neg_app, add_monoid_hom.neg_apply, smul_neg],
  end }⟩


@[simp] lemma ab_sheaf_neg (φ : 𝓜 ⟶ 𝓝): (-φ : 𝓜 ⟶ 𝓝).ab_sheaf = -(φ.ab_sheaf) :=
rfl

instance : has_add (𝓜 ⟶ 𝓝) := ⟨λ φ ψ,
{ ab_sheaf := φ.ab_sheaf + ψ.ab_sheaf,
  map_smul := λ U r m, begin
    simp only [φ.map_smul, ψ.map_smul, Sheaf.hom.add_app, add_monoid_hom.add_apply, smul_add],
  end }⟩

@[simp] lemma ab_sheaf_add (φ ψ : 𝓜 ⟶ 𝓝) : (φ+ψ).ab_sheaf =φ.ab_sheaf+ψ.ab_sheaf :=
rfl

def comp {𝓜 𝓝 𝓟 : SHEAF_OF_MODULES X} (φ: 𝓜 ⟶ 𝓝) (ψ:𝓝 ⟶ 𝓟) : (𝓜 ⟶ 𝓟) :=
{ ab_sheaf := φ.ab_sheaf ≫ ψ.ab_sheaf,
  map_smul := λ U r m, begin
    simp only [φ.map_smul, ψ.map_smul, Sheaf.category_theory.category_comp_val,
      nat_trans.comp_app, comp_apply],
  end }

end hom

instance : add_comm_group (𝓜 ⟶ 𝓝) :=
add_comm_group.mk'
begin
  intros,
  ext,
  simp only [add_assoc, hom.ab_sheaf_add],
end
begin
  intros,
  ext,
  simp only [hom.ab_sheaf_add, add_comm],
end
begin
  intros,
  ext,
  simp only [hom.ab_sheaf_add, hom.ab_sheaf_zero, zero_add],
end $
begin
  intros,
  ext,
  simp only [add_left_neg, hom.ab_sheaf_add, hom.ab_sheaf_neg, hom.ab_sheaf_zero],
end
--hom_ext _ _ $ λ U, linear_map.ext $ λ x, add_left_neg _

instance : large_category (SHEAF_OF_MODULES X) :=
{ hom := λ 𝓜 𝓝, hom 𝓜 𝓝,
  id := λ 𝓜 : SHEAF_OF_MODULES X,
  { ab_sheaf := 𝟙 _,
    map_smul := λ U r m, by simp only
      [Sheaf.category_theory.category_id_val, nat_trans.id_app, id_apply], },--⟨(𝟙 𝓜.ab_sheaf, λ U, linear_map.id), λ U, rfl⟩,
  comp := λ 𝓜 𝓝 𝓟 φ ψ,
  { ab_sheaf := φ.ab_sheaf ≫ ψ.ab_sheaf,
    map_smul := λ U r m, begin
      simp only [φ.map_smul, ψ.map_smul, Sheaf.category_theory.category_comp_val,
        nat_trans.comp_app, comp_apply],
  end },
  id_comp' := begin
    intros 𝓜 𝓝 φ,
    ext,
    simp only [category.id_comp],
  end,
  comp_id' := begin
    intros 𝓜 𝓝 φ,
    ext,
    simp only [category.comp_id],
  end,
  assoc' := begin
    intros 𝓜 𝓝 𝓟 𝓠 α β γ,
    ext,
    simp only [category.assoc],
  end, }
.

@[simp] lemma hom.comp_ab_sheaf {𝓟} (φ : 𝓜 ⟶ 𝓝) (ψ : 𝓝 ⟶ 𝓟) :
(φ ≫ ψ).ab_sheaf = φ.ab_sheaf ≫ ψ.ab_sheaf := rfl

/-
class abelian extends preadditive C, normal_mono_category C, normal_epi_category C :=
[has_finite_products : has_finite_products C]
[has_kernels : has_kernels C]
[has_cokernels : has_cokernels C]
-/

--lemma sections_comp_apply {𝓜 𝓝 𝓟 : SHEAF_OF_MODULES X} (φ : 𝓜 ⟶ 𝓝) (ψ : 𝓝 ⟶ 𝓟) (U : opens (X : TOP)) :
--(φ ≫ ψ : 𝓜 ⟶ 𝓟).sections U = (ψ.sections U).comp (φ.sections U) := rfl

--lemma sections_add_apply {𝓜 𝓝 : SHEAF_OF_MODULES X} (φ ψ : 𝓜 ⟶ 𝓝) (U : opens (X : TOP)) :
--(φ + ψ).sections U = (φ.sections U) + (ψ.sections U) := rfl


instance : preadditive (SHEAF_OF_MODULES X) :=
{ hom_group := λ 𝓜 𝓝, infer_instance,
  add_comp' := λ 𝓜 𝓝 𝓟 f f' g,
  begin
    ext,
    simp only [hom.comp_ab_sheaf, hom.ab_sheaf_add, Sheaf.category_theory.category_comp_val,
      nat_trans.comp_app, Sheaf.hom.add_app, preadditive.add_comp],
  end,
  comp_add' := λ 𝓜 𝓝 𝓟 f f' g,
  begin
    ext,
    simp only [hom.comp_ab_sheaf, hom.ab_sheaf_add, Sheaf.category_theory.category_comp_val,
      nat_trans.comp_app, Sheaf.hom.add_app, add_monoid_hom.add_apply, comp_apply],
  end, }
.

open category_theory.limits

instance : has_zero_morphisms (SHEAF_OF_MODULES X) :=
{ comp_zero' := λ 𝓜 𝓝 f 𝓟, by ext; simp only [comp_zero],
  zero_comp' := λ 𝓜 𝓝 f 𝓟, by ext; simp only [zero_comp]}
.

def map (Y : RINGED_SPACE) (f : X ⟶ Y) (𝓜 : SHEAF_OF_MODULES X) : SHEAF_OF_MODULES Y :=
{ ab_sheaf := _,
  module_bit := _,
  compatibility_bit := _ }

def kernel (f : 𝓜 ⟶ 𝓝) : SHEAF_OF_MODULES X :=
{ ab_sheaf :=
  { val :=
    { obj := λ U,
      { α := (f.ab_sheaf.val.app U).ker,
        str := infer_instance },
      map := λ U V i,
      { to_fun := λ s, ⟨𝓜.ab_sheaf.val.map i s.1, begin
          cases s with s hs,
          rw add_monoid_hom.mem_ker at hs ⊢,
          -- how am I supposed to do this?
          change (𝓜.ab_sheaf.val.map i ≫ f.ab_sheaf.val.app V) s = 0,
          rw nat_trans.naturality,
          change 𝓝.ab_sheaf.val.map i _ = 0,
          rw hs,
          apply map_zero,
        end⟩,
        map_zero' := begin
          simp only [map_zero, subtype.val_eq_coe, add_subgroup.coe_zero],
          refl,
        end,
        map_add' := begin
          rintros ⟨x, hx⟩ ⟨y, hy⟩,
          ext,
          exact add_monoid_hom.map_add (𝓜.ab_sheaf.val.map i : 𝓜.ab_sheaf.val.obj U →+ 𝓜.ab_sheaf.val.obj V) x y,
        end },
      map_id' := begin
        intro U,
        ext ⟨x, hx⟩,
        -- becoming painful
        sorry,
      end,
      map_comp' := sorry },
    cond := sorry },
  module_bit := sorry,
  compatibility_bit := sorry }

instance : has_kernels (SHEAF_OF_MODULES X) :=
{ has_limit := λ 𝓜 𝓝 f, { exists_limit := ⟨
  { cone :=
    { X := sorry, -- need the kernel of a morphism as a term of type `SHEAF_OF_MODULES`
      π := sorry },
    is_limit := sorry }⟩ } }

instance : normal_mono_category (SHEAF_OF_MODULES X) :=
{ normal_mono_of_mono := λ 𝓜 𝓝 f hf, sorry }



end SHEAF_OF_MODULES
