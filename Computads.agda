{-
Author : Ioannis Markakis (github.com/jmarkakis)
with significant help by Alex Rice (github.com/alexarice)
-}

module Computads where

open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs
open import Data.Bool renaming (true to tt; false to ff)
open import Data.List
open import Data.Nat renaming (ℕ to Nat)
open import Data.Nat.Properties
open import Data.Product
open import Function
open import Level using (Level; Lift; lift)
  renaming (suc to lsuc; zero to lzero; _⊔_ to lmax)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Relation.Nullary.Decidable

--------------------------------------------------------------------------------
-- This file contains the formalisation of the definition in Section 3.1 of
-- "Computads for weak ω-categories as an inductive type" by C. J. Dean,
-- E. Finster, I. Markakis, D. Reutter, and J. Vicary (arXiv:2208.08719).
-- For the formalisation, we will use function extensionality
-- and uniqueness of identity proofs. We will start by an easy lemma on the
-- identity of iterated Σ-types

postulate
  ExtΠ : {ℓ : Level} → Axiom.Extensionality.Propositional.Extensionality ℓ ℓ
  Ext≡ : {ℓ : Level}{A : Set ℓ} → Axiom.UniquenessOfIdentityProofs.UIP A

cong₃ : {ℓ : Level}{A B D : Set ℓ}{C : (a : A) → B → Set ℓ}{a a' : A}{b b' : B}
  {c : C a b}(f : (a : A) → (b : B) →(c : C a b) → D){c' : C a' b'}(pa : a ≡ a')
  (pb : b ≡ b')(pc : subst₂ C pa pb c ≡ c') → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

ExtΣ : {ℓ : Level}{A B : Set ℓ}{C : A → B → Set ℓ}{a a' : A}{b b' : B}
  {c : C a b}{c' : C a' b'}
  (pa : a ≡ a')(pb : b ≡ b')(pc : subst₂ C pa pb c ≡ c' ) →
  (a , b , c) ≡ (a' , b' , c')
ExtΣ = cong₃ (λ a b c → a , b , c)

{- 1. Batanin Trees -}
--------------------------------------------------------------------------------
-- We start by defining Batanin trees and their dimension. We also give an
-- inductive definition of the globular set of positions of a Batanin tree B,
-- which amounts to the recursive formulae
--        Pos (br []) = D_0
--        Pos (br (B ∷ L)) = (Σ Pos B) ∨ Pos (br L)
-- where D_0 is the globular set with unique 0-cell and no higher cells, and Σ
-- and ∨ denote the suspension and the wedge sum of globular sets respectively.
-- We will denote the source and boundary of a positive-dimensional position p
-- by (bdryPos ff p) and (bdryPos tt p) respectively, and we will show that they
-- satisfy the globularity condition.

data Bat : Set where
  br : List Bat → Bat

dim : Bat → Nat
dim (br []) = zero
dim (br (B ∷ L)) = suc (dim B ) ⊔ dim (br L)

data Pos : Nat → Bat → Set where
  init : (B : Bat) → Pos 0 B
  inl : {n : Nat}(B : Bat)(L : List Bat)(p : Pos n B) → Pos (suc n) (br (B ∷ L))
  inr : {n : Nat}(B : Bat)(L : List Bat)(q : Pos n (br L)) → Pos n (br (B ∷ L))

bdryPos : {n : Nat}{B : Bat} → Bool → Pos (suc n) B → Pos n B
bdryPos b (inr B L q) = inr B L (bdryPos b q)
bdryPos {zero} ff (inl B L p) = init (br (B ∷ L))
bdryPos {zero} tt (inl B L p) = inr B L (init (br L))
bdryPos {suc n} b (inl B L p) = inl B L (bdryPos b p)

globPos : {n : Nat}{B : Bat}(p : Pos (suc (suc n)) B)(b : Bool)
  → bdryPos b (bdryPos ff p) ≡ bdryPos b (bdryPos tt p)
globPos {zero} (inl B L p) ff = refl
globPos {zero} (inl B L p) tt = refl
globPos {suc n} (inl B L p) b = cong (inl B L) (globPos p b)
globPos (inr B L q) b = cong (inr B L) (globPos q b)

--------------------------------------------------------------------------------
-- We introduce the subsets of source boudnary and target boundary positions of
-- a Batanin tree B denoted by (bdryPosSet ff) and (bdryPosSet tt) respectively.
-- Here we encode subsets as predicates on positions. We recall from the paper
-- that the unique position of br [] is both source and target boundary. For the
-- positions of br (B ∷ L), we see from the definition of ∂Pos that
-- (1) init(br (B ∷ L)) is not the target of any position, but it is the source
-- of inl B L (init B), so it is source boundary but not target boundary.
-- (2) a position of the form (inl B L p) can only be the source or target of a
-- position of the same form, so it is source or target boundary if and only if
-- p is source or target boundary respectively.
-- (3) a position of the form (inr B L q) can only be the source of a position
-- of the same form, so it is target boundary if and only if q is target
-- boundary. Similarly it is source boundary if and only if q is source
-- boundary and q ̸= init (br L). The latter condition is necessary because
-- inr B L (init (br L)) is the target of (inl B L (init B)) and hence is not
-- source boundary.

bdryPosSet : {B : Bat}{n : Nat} → Bool → Pos n B → Bool
bdryPosSet {br []} b p = tt
bdryPosSet {br (B ∷ L)} ff (init .(br (B ∷ L))) = tt
bdryPosSet {br (B ∷ L)} tt (init .(br (B ∷ L))) = ff
bdryPosSet {br (B ∷ L)} b (inl .B .L p) = bdryPosSet b p
bdryPosSet {br (B ∷ L)} ff (inr .B .L (init (br .L))) = ff
bdryPosSet {br (B ∷ L)} ff (inr .B .L q) = bdryPosSet ff q
bdryPosSet {br (B ∷ L)} tt (inr .B .L q) = bdryPosSet tt q

--------------------------------------------------------------------------------
-- For the definition of full spheres of a Batanin tree below, we will need to
-- compute the support of terms over computads generated by globular sets of
-- positions of Batanin trees. Those are either singletons or computed
-- recursively as unions of subsets indexed by the positions of some tree. Since
-- we use predicates to encode subsets, we need to show that the sets Pos n B
-- have decidable equality (to define singletons) and to compute suprema of
-- Booleans indexed by positions (to define unions).

injectivity-of-inl : {n : Nat}{B : Bat}{L : List Bat}{p p' : Pos n B}
  → inl B L p ≡ inl B L p' → p ≡ p'
injectivity-of-inl refl = refl

injectivity-of-inr : {n : Nat}{B : Bat}{L : List Bat}{q q' : Pos n (br L)}
  → inr B L q ≡ inr B L q' → q ≡ q'
injectivity-of-inr refl = refl

DecEqPos : {n : Nat}{B : Bat} → DecidableEquality (Pos n B)
DecEqPos (init B) (init .B) = yes refl
DecEqPos (inl B L p) (inl .B .L p') with DecEqPos p p'
... | yes p=p' = yes (cong (inl B L) p=p')
... | no p≠p' = no λ h → p≠p' (injectivity-of-inl h)
DecEqPos (inr B L q) (inr .B .L q') with DecEqPos q q'
... | yes q=q' = yes (cong (inr B L) q=q')
... | no q≠q' = no λ h → q≠q' (injectivity-of-inr h)
DecEqPos (inr B L q) (init .(br (B ∷ L))) = no λ ()
DecEqPos (init .(br (B ∷ L))) (inr B L y) = no λ ()
DecEqPos (inr B L q) (inl .B .L p) = no λ ()
DecEqPos (inl B L p) (inr .B .L q) = no λ ()

Singleton : {n : Nat}{B : Bat}(p : Pos n B) → Pos n B → Bool
Singleton p p' = isYes (DecEqPos p p')

suprBool : {n : Nat}{B : Bat}(f : Pos n B → Bool) → Bool
suprBool {zero} {br []} f = f (init (br []))
suprBool {suc n} {br []} f = ff
suprBool {zero} {br (B ∷ L)} f =
    f (init (br (B ∷ L))) ∨ suprBool (λ q → f (inr B L q))
suprBool {suc n} {br (B ∷ L)} f =
  suprBool (λ p → f (inl B L p)) ∨ suprBool (λ q → f (inl B L q))

Union : {u : Level}{n : Nat}{B : Bat}{X : Set u}(S : Pos n B → X → Bool)
  → X → Bool
Union S x = suprBool (λ p → S p x)

{- 2. Globular Sets -}
--------------------------------------------------------------------------------
-- We will now introduce by induction on the dimension n:
-- (1) the category gSet­ₙ of n-globular sets
-- (2) the truncation functor gSetTrₙ : gSetₙ₊₁ → gSetₙ forgetting the
-- top-dimensional cells of an (n+1)-globular set
-- (3) the functor gSetCell­ₙ : gSetₙ → Set returning the set of top-dimensional
-- cells of an n-globular set
-- (4) the functor gSetSphere­ₙ : gSetₙ → Set returning the set of pairs of
-- top-dimensional cells of an n-globular set
-- (5) the natural transformation gSetBdryₙ : gSetCellₙ₊₁ ⇒ gSetSphereₙ ∘ gSetTrₙ
-- sending a top-dimensional cell to the pair of its source and target cells

-- Before stating the definitions, we observe that an (n+1)­­-globular set is
-- an n-globular set X together with a set Xₙ­₊₁ and a a source/target function
-- Xₙ­₊₁ → gSetSphereₙ X.

{-1-}
gSet : (ℓ : Level)(n : Nat) → Set (lsuc ℓ)
gSetM : {ℓ : Level}{n : Nat}(X Y : gSet ℓ n) → Set ℓ
gSet∘ : {ℓ : Level}{n : Nat}{X Y Z : gSet ℓ n}(f : gSetM Y Z)(g : gSetM X Y)
  → gSetM X Z
gSetId : {ℓ : Level}{n : Nat}{X : gSet ℓ n} → gSetM X X
gSetAss : {ℓ : Level}{n : Nat}{X Y Z W : gSet ℓ n}(f : gSetM Z W)
  (g : gSetM Y Z)(h : gSetM X Y) → gSet∘ f (gSet∘ g h) ≡ gSet∘ (gSet∘ f g) h
gSetLu : {ℓ : Level}{n : Nat}{X Y : gSet ℓ n}(f : gSetM X Y)
  → gSet∘ gSetId f ≡ f
gSetRu : {ℓ : Level}{n : Nat}{X Y : gSet ℓ n}(f : gSetM X Y)
  → gSet∘ f gSetId ≡ f

{-2-}
gSetTr : {ℓ : Level}{n : Nat}(X : gSet ℓ (suc n)) → gSet ℓ n
gSetTrM : {ℓ : Level}{n : Nat}{X Y : gSet ℓ (suc n)}(f : gSetM X Y)
  → gSetM (gSetTr X) (gSetTr Y)
gSetTr∘ : {ℓ : Level}{n : Nat}{X Y Z : gSet ℓ (suc n)}(f : gSetM Y Z)
  (g : gSetM X Y) → gSet∘ (gSetTrM f) (gSetTrM g) ≡ gSetTrM (gSet∘ f g)
gSetTrId : {ℓ : Level}{n : Nat}{X : gSet ℓ (suc n)}
  → gSetTrM (gSetId {X = X}) ≡ gSetId

{-3-}
gSetCell : {ℓ : Level}{n : Nat}(X : gSet ℓ n) → Set ℓ
gSetCellM : {ℓ : Level}{n : Nat}{X Y : gSet ℓ n}(f : gSetM X Y) → gSetCell X
  → gSetCell Y
gSetCell∘ : {ℓ : Level}{n : Nat}{X Y Z : gSet ℓ n}(f : gSetM Y Z)(g : gSetM X Y)
  → (gSetCellM f) ∘ (gSetCellM g) ≡ gSetCellM (gSet∘ f g)
gSetCellId : {ℓ : Level}{n : Nat}{X : gSet ℓ n}
  → gSetCellM (gSetId {X = X}) ≡ id

{-4-}
gSetSphere : {ℓ : Level}{n : Nat}(X : gSet ℓ n) → Set ℓ
gSetSphereM : {ℓ : Level}{n : Nat}{X Y : gSet ℓ n}(f : gSetM X Y) → gSetSphere X
  → gSetSphere Y
gSetSphere∘ : {ℓ : Level}{n : Nat}{X Y Z : gSet ℓ n}(f : gSetM Y Z)
  (g : gSetM X Y) → (gSetSphereM f) ∘ (gSetSphereM g) ≡ gSetSphereM (gSet∘ f g)
gSetSphereId : {ℓ : Level}{n : Nat}{X : gSet ℓ n}
  → gSetSphereM (gSetId {X = X}) ≡ id

{-5-}
gSetBdry : {ℓ : Level}{n : Nat}(X : gSet ℓ (suc n))(x : gSetCell X)
  → gSetSphere (gSetTr X)
gSetBdryM : {ℓ : Level}{n : Nat}{X Y : gSet ℓ (suc n)}(f : gSetM X Y)
  → (gSetBdry Y) ∘ (gSetCellM f) ≡ (gSetSphereM (gSetTrM f)) ∘ (gSetBdry X)

--------------------------------------------------------------------------------
-- Having declared all the data that we will define mutually recursively, we
-- proceed to give their actual definitions.

gSet ℓ zero = Set ℓ
gSet ℓ (suc n) =
  Σ[ X ∈ gSet ℓ n ]
  Σ[ Xₙ₊₁ ∈ Set ℓ ]
  (Xₙ₊₁ → gSetSphere X)
gSetTr (X , _) = X
gSetCell {n = zero} X = X
gSetCell {n = suc n} (_ , Xₙ₊₁ , _) = Xₙ₊₁
gSetBdry (_ , _ , φ)= φ
gSetSphere {n = zero} X = X × X
gSetSphere {n = suc n} X =
  Σ[ s ∈ gSetCell X ]
  Σ[ t ∈ gSetCell X ]
  gSetBdry X s ≡ gSetBdry X t

gSetM {n = zero} X Y = X → Y
gSetM {n = suc n} (X , Xₙ₊₁ , φX) (Y , Yₙ₊₁ , φY) =
  Σ[ f ∈ gSetM X Y ]
  Σ[ fₙ₊₁ ∈ (Xₙ₊₁ → Yₙ₊₁) ]
  φY ∘ fₙ₊₁ ≡ (gSetSphereM f) ∘ φX
gSetTrM (f , _)= f
gSetCellM {n = zero} f = f
gSetCellM {n = suc n} (_ , fₙ₊₁ , _) = fₙ₊₁
gSetSphereM {n = zero} f (s , t) = (f s , f t)
gSetSphereM {n = suc n} {X , Xₙ₊₁ , φX} {Y , Yₙ₊₁ , φY} (f , fₙ₊₁ , f∂)
  (s , t , φs=φt) = (fₙ₊₁ s , fₙ₊₁ t , (begin
    φY (fₙ₊₁ s)
      ≡⟨ cong-app f∂ s ⟩
    (gSetSphereM f) (φX s)
      ≡⟨ cong (gSetSphereM f) φs=φt ⟩
    (gSetSphereM f) (φX t)
      ≡⟨ sym (cong-app f∂ t) ⟩
    φY (fₙ₊₁ t)
      ∎))
gSetBdryM (_ , _ , ∂f) = ∂f

gSet∘ {n = zero} f g = f ∘ g
gSet∘ {n = suc n} {X , Xₙ₊₁ , φX} {Y , Yₙ₊₁ , φY} {Z , Zₙ₊₁ , φZ} (f , fₙ₊₁ , f∂)
  (g , gₙ₊₁ , g∂) =  gSet∘ f g , fₙ₊₁ ∘ gₙ₊₁ , ExtΠ λ x → begin
    φZ (fₙ₊₁ (gₙ₊₁ x))
      ≡⟨ cong-app f∂ (gₙ₊₁ x) ⟩
    gSetSphereM f (φY (gₙ₊₁ x))
      ≡⟨ cong (gSetSphereM f) (cong-app g∂ x) ⟩
    gSetSphereM f (gSetSphereM g (φX x))
      ≡⟨ cong-app (gSetSphere∘ f g) (φX x) ⟩
    gSetSphereM (gSet∘ f g) (φX x)
      ∎
gSetTr∘ f g = refl
gSetCell∘ {n = zero} f g = refl
gSetCell∘ {n = suc n} f g = refl
gSetSphere∘ {n = zero} f g = refl
gSetSphere∘ {n = suc n} f g = ExtΠ λ A → ExtΣ refl refl (Ext≡ _ _)
gSetAss {n = zero} f g h = refl
gSetAss {n = suc n} (f , _) (g , _) (h , _) =
  ExtΣ (gSetAss f g h) refl (Ext≡ _ _)


gSetId {n = zero} {X} = id
gSetId {n = suc n} {X , Xₙ₊₁ , φX} = gSetId , id ,
  ExtΠ λ x → sym (cong-app gSetSphereId (φX x))
gSetTrId = refl
gSetCellId {n = zero} = refl
gSetCellId {n = suc n} = refl
gSetSphereId {n = zero}  = refl
gSetSphereId {n = suc n}  = ExtΠ λ A → ExtΣ refl refl (Ext≡ _ _)

gSetLu {n = zero} f = refl
gSetLu {n = suc n} (f , _) = ExtΣ (gSetLu f) refl (Ext≡ _ _)
gSetRu {n = zero} f = refl
gSetRu {n = suc n} (f , _) = ExtΣ (gSetRu f) refl (Ext≡ _ _)

--------------------------------------------------------------------------------
-- We will now define by induction on a natural number n, an n-globular set
-- (gSetPos n B) for every Batanin tree B. Those n-globular sets are the
-- truncations of the globular set of positions of B. To define (gSetPos n B)
-- we also introduce in the same induction two auxilliary functions.

gSetPos : (ℓ : Level)(n : Nat)(B : Bat) → gSet ℓ n
gSetPosBdry : {ℓ : Level}{n : Nat}{B : Bat}(p : Pos (suc n) B)
  → gSetSphere (gSetPos ℓ n B)
gSetPosGlob : {ℓ : Level}{n : Nat}{B : Bat}(p p' : Pos (suc n) B)
  (par : (b : Bool) → bdryPos b p ≡ bdryPos b p') →
  gSetPosBdry {ℓ} p ≡ gSetPosBdry {ℓ} p'

gSetPos ℓ zero B = Lift ℓ (Pos zero B)
proj₁ (gSetPos ℓ (suc n) B) = gSetPos ℓ n B
proj₁ (proj₂ (gSetPos ℓ (suc n) B)) = Lift ℓ (Pos (suc n) B)
proj₂ (proj₂ (gSetPos ℓ (suc n) B)) (lift p) = gSetPosBdry p

gSetPosBdry {ℓ} {n = zero} p = lift (bdryPos ff p) , lift (bdryPos tt p)
gSetPosBdry {ℓ} {n = suc n} p = lift (bdryPos ff p) , lift (bdryPos tt p) ,
  gSetPosGlob (bdryPos ff p) (bdryPos tt p) (globPos p)

gSetPosGlob {n = zero} p p' par =
    cong₂ _,_ (cong lift (par ff)) (cong lift (par tt))
gSetPosGlob {n = suc n} p p' par =
  ExtΣ (cong lift (par ff)) (cong lift (par tt)) (Ext≡ _ _)

{- 3. Computads -}
-- We will now define by induction on a natural number n:
-- (1) the category Compₙ of n-computads, generating data for ω-categories, and
-- strict ω-functors between the corresponding ω-categories.
-- (2) the functor Cell­ₙ : Comp­ₙ → Set returning the set of n-cells of the free
-- ω-category generated by a computad; cells are either generators (var), or
-- images under some homomorphism of liftings coh(B,A,-) of full spheres
-- (explained below)
-- (3) the functor Sphere­ₙ : Compₙ → Set returning the set of pairs of parallel
-- n-cells of the free ω-category generated by a computad
-- (4) a functor Freeₙ : gSet­ₙ → Comp­ₙ viewing each globular set as a computad,
-- and each morphism of globular sets as a strict ω-functor.
-- (5) an auxilliary natural transformation
-- posSphereₙ : gSetSphereₙ ⇒ Sphereₙ ∘ Freeₙ sending pairs of parallel cells of
-- a globular set to the same pair of parallel cells, seen as generators of the
-- free ω-category on that globular set.
-- (7) a subset Full­ₙ(B) ⊆ Sphere­ₙ(Freeₙ (gSetPos B)) of full spheres for each
-- Batanin tree B encoded as a (non-decidable) predicate on spheres. Those are
-- analogues of the admissible pairs of arrows of Maltsiniotis and will be given
-- a canonical lift coh(B,A,id).

-- We will also define for positive n,
-- (6) a truncation functor uₙ : Compₙ → Compₙ₋₁ forgetting the top-dimensional
-- generators of an n-computad
-- (7) a natural transformation bdryₙ : Cellₙ ⇒ Sphereₙ₋₁ ∘ uₙ sending an
-- n-cell of the free ω-category generated by a computad to its source and
-- target cells.

record IndData (ℓ : Level)(n : Nat) : Set (lsuc (lsuc ℓ)) where
  field
    {-1-}
    Comp : Set (lsuc ℓ)
    CompM : (C D : Comp) → Set ℓ
    Comp∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D) → CompM C E
    CompAss : {C D E F : Comp}(ρ : CompM E F)(σ : CompM D E)(τ : CompM C D)
        → Comp∘ ρ (Comp∘ σ τ) ≡ Comp∘ (Comp∘ ρ σ) τ
    CompId : {C : Comp} → CompM C C
    CompLu : {C D : Comp}(σ : CompM C D) → Comp∘ CompId σ ≡ σ
    CompRu : {C D : Comp}(σ : CompM C D) → Comp∘ σ CompId ≡ σ

    {-2-}
    Cell : (C : Comp) → Set ℓ
    CellM : {C D : Comp}(σ : CompM C D)(c : Cell C) → Cell D
    Cell∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D)
        → (CellM ρ) ∘ (CellM σ) ≡ CellM (Comp∘ ρ σ)
    CellId : {C : Comp} → CellM (CompId {C}) ≡ id

    {-3-}
    Sphere : (C : Comp) → Set ℓ
    SphereM : {C D : Comp}(σ : CompM C D)(A : Sphere C) → Sphere D
    Sphere∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D)
        → (SphereM ρ) ∘ (SphereM σ) ≡ SphereM (Comp∘ ρ σ)
    SphereId : {C : Comp} → SphereM (CompId {C}) ≡ id

    {-4-}
    Free : (X : gSet ℓ n) → Comp
    FreeM : {X Y : gSet ℓ n}(f : gSetM X Y) → CompM (Free X) (Free Y)
    Free∘ : {X Y Z : gSet ℓ n}(f : gSetM Y Z)(g : gSetM X Y)
        → Comp∘ (FreeM f) (FreeM g) ≡ FreeM (gSet∘ f g)
    FreeId : {X : gSet ℓ n} → FreeM (gSetId {X = X}) ≡ CompId

    {-5-}
    posSphere : (X : gSet ℓ n)(A : gSetSphere X) → Sphere (Free X)
    posSphereM : {X Y : gSet ℓ n}(f : gSetM X Y)
      → (posSphere Y) ∘ (gSetSphereM f) ≡ SphereM (FreeM f) ∘ (posSphere X)

    {-6-}
    -- In the presence of Uniqueness of Identity Proofs, one can see that
    -- (Full A) is actually a proposition, but we will not need that.
    Full : {B : Bat}(A : Sphere (Free (gSetPos ℓ n B))) → Set₀

record AllData (ℓ : Level)(n : Nat) : Set (lsuc (lsuc ℓ)) where
  field
    prev : (pos : n > 0) → IndData ℓ (pred n)
    curr : IndData ℓ n
  open IndData curr
  field
    {-7-}
    u : (pos : n > 0) → (C : Comp) → IndData.Comp (prev pos)
    uM : (pos : n > 0){C D : Comp}(σ : CompM C D) →
      IndData.CompM (prev pos) (u pos C) (u pos D)
    u∘ : (pos : n > 0){C D E : Comp}(ρ : CompM D E)(σ : CompM C D)
      → IndData.Comp∘ (prev pos) (uM pos ρ) (uM pos σ) ≡ uM pos (Comp∘ ρ σ)
    uId : (pos : n > 0){C : Comp}
      → uM pos (CompId {C}) ≡ IndData.CompId (prev pos)

    {-8-}
    bdry : (pos : n > 0)(C : Comp) → Cell C
      → IndData.Sphere (prev pos) (u pos C)
    bdryM : (pos : n > 0){C D : Comp}(σ : CompM C D)
      → (bdry pos D) ∘ (CellM σ) ≡
        (IndData.SphereM (prev pos) (uM pos σ)) ∘ (bdry pos C)

{- 3.1 Base Case -}
--------------------------------------------------------------------------------
-- We will define a function Data : (n : Nat) → AllData n recursively on n,
-- whose base step and inductive step contain the definitions of Section 3.1.
-- We begin with the base case n = 0, where Comp = Set, Cell = Free = id and
-- Sphere X = X × X. In order to define full spheres, we will also define the
-- support of a cell of Free (gSetPos B) for Batanin trees B, a subset of the
-- positions of the tree.

module Zero (ℓ : Level) where
  open AllData
  open IndData

  Data : AllData ℓ zero
  supp : {B : Bat}
    (c : Cell (curr Data) (Free (curr Data) (gSetPos ℓ zero B)))
    → Pos zero B → Bool

  prev Data ()
  u Data ()
  uM Data ()
  u∘ Data ()
  uId Data ()
  bdry Data ()
  bdryM Data ()
  Comp (curr Data) = Set ℓ
  CompM (curr Data) C D = C → D
  Comp∘ (curr Data) ρ σ = ρ ∘ σ
  CompAss (curr Data) ρ σ τ = refl
  CompId (curr Data) = id
  CompLu (curr Data) σ = refl
  CompRu (curr Data) σ = refl
  Cell (curr Data) = id
  CellM (curr Data) = id
  Cell∘ (curr Data) ρ σ = refl
  CellId (curr Data) = refl
  Sphere (curr Data) C = C × C
  SphereM (curr Data) σ (s , t)= (σ s , σ t)
  Sphere∘ (curr Data) ρ σ = refl
  SphereId (curr Data) = refl
  Free (curr Data) = id
  FreeM (curr Data) = id
  Free∘ (curr Data) f g = refl
  FreeId (curr Data) = refl
  posSphere (curr Data) X = id
  posSphereM (curr Data) f = refl
  Full (curr Data) (s , t) =
    (supp s ≡ bdryPosSet ff) × (supp t ≡ bdryPosSet tt)
  supp (lift p) = Singleton p

{- 3.2 Inductive Step -}
--------------------------------------------------------------------------------
-- We proceed now with the inductive step. For that, we assume that all data has
-- been defined for some n, and we define it for n+1. We will define the data in
-- the same order as they are presented in Section 3.3 of the paper.

module Step (ℓ : Level)(n : Nat)(prev : IndData ℓ n) where

{- 3.2.1 Computads -}
--------------------------------------------------------------------------------
-- We define first the class of (n+1)-computads and the actions of the forgetful
-- functor and the free functor on objects. We will also define two auxilliary
-- functions returning the top-dimensional generators of a computads, and the
-- function returning their source and target.

  Comp : Set (lsuc ℓ)
  Comp =
    Σ[ C ∈ IndData.Comp prev ]
    Σ[ V ∈ Set ℓ ]
    (V → IndData.Sphere prev C)

  u : Comp → IndData.Comp prev
  u (C , _ , _) = C

  gen : Comp → Set ℓ
  gen (_ , V , _) = V

  bdryVar : (C : Comp) → gen C → IndData.Sphere prev (u C)
  bdryVar (_ , _ , φ) = φ

  Free : gSet ℓ (suc n) → Comp
  Free (X , Xₙ₊₁ , φX) =
    IndData.Free prev X , Xₙ₊₁ , (IndData.posSphere prev X) ∘ φX

{- 3.2.2 Morphisms, cells and their boundary -}
--------------------------------------------------------------------------------
-- We then define inductively-recursively the sets of cells, their boundary
-- spheres, the sets of homomorphisms of computads, and their action of the
-- forgetful functor on morphisms.

  CompM : Comp → Comp → Set ℓ
  uM : {C D : Comp} → CompM C D → IndData.CompM prev (u C) (u D)
  data Cell (C : Comp) : Set ℓ
  bdry : (C : Comp) → Cell C → IndData.Sphere prev (u C)

  CompM C D =
    Σ[ σ ∈ IndData.CompM prev (u C) (u D) ]
    Σ[ σV ∈ (gen C → Cell D) ]
    (bdry D) ∘ σV ≡ (IndData.SphereM prev σ) ∘ (bdryVar C)

  uM (σ , _) = σ

  data Cell C where
    var : gen C → Cell C
    coh : (B : Bat)(A : IndData.Sphere prev (IndData.Free prev (gSetPos ℓ n B)))
      (fl : IndData.Full prev A)(τ : CompM (Free (gSetPos ℓ (suc n) B)) C)
      → Cell C

  bdry C (var v) = bdryVar C v
  bdry C (coh B A fl τ) = IndData.SphereM prev (uM τ) A

{- 3.2.3 Composition -}
--------------------------------------------------------------------------------
-- Having defined homomorphisms and cells, we may define mutually recursively
-- composition of homomorphisms, the action of homomorphisms on cells and prove
-- naturality of the boundary functions.

  Comp∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D) → CompM C E
  CellM : {C D : Comp}(σ : CompM C D) → Cell C → Cell D
  bdryM : {C D : Comp}(σ : CompM C D)(c : Cell C)
    → bdry D (CellM σ c) ≡ IndData.SphereM prev (uM σ) (bdry C c)

  Comp∘ {C} {D} {E} ρ@(ρn , ρV , ∂ρ) σ@(σn , σV , ∂σ) =
    IndData.Comp∘ prev ρn σn , CellM ρ ∘ σV , ExtΠ λ v → begin
      bdry E (CellM ρ (σV v))
        ≡⟨ bdryM ρ (σV v) ⟩
      IndData.SphereM prev ρn (bdry D (σV v))
        ≡⟨ cong (IndData.SphereM prev ρn) (cong-app ∂σ v) ⟩
      IndData.SphereM prev ρn (IndData.SphereM prev σn (bdryVar C v))
        ≡⟨ cong-app (IndData.Sphere∘ prev ρn σn) (bdryVar C v) ⟩
      IndData.SphereM prev (IndData.Comp∘ prev ρn σn) (bdryVar C v)
        ∎
  CellM (_ , σV , _) (var v) = σV v
  CellM σ (coh B A fl τ) = coh B A fl (Comp∘ σ τ)

  bdryM (σ , σV , σ∂) (var v) = cong-app σ∂ v
  bdryM (σ , σV , σ∂) (coh B A fl τ) =
    sym (cong-app (IndData.Sphere∘ prev σ (uM τ)) A)

{- 3.2.4 Axioms of a category -}
--------------------------------------------------------------------------------
-- We prove similarly by mutual induction that composition is associtive and
-- the functor Cell preserves the composition operation

  CompAss : {C D E F : Comp}(ρ : CompM E F)(σ : CompM D E)(τ : CompM C D)
    → Comp∘ ρ (Comp∘ σ τ) ≡ Comp∘ (Comp∘ ρ σ) τ
  Cell∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D)(c : Cell C)
    → CellM ρ (CellM σ c) ≡ CellM (Comp∘ ρ σ) c

  CompAss ρ σ τ@(_ , τV , _) = ExtΣ (IndData.CompAss prev (uM ρ) (uM σ) (uM τ))
    (ExtΠ λ v → Cell∘ ρ σ (τV v)) (Ext≡ _ _)

  Cell∘ ρ σ (var v) = refl
  Cell∘ ρ σ (coh B A fl τ) = cong (coh B A fl) (CompAss ρ σ τ)

--------------------------------------------------------------------------------
-- We can now define identities and show that the right unit law holds. The
-- left unit law is proven by mutually induction with preservation of identities
-- by the functor Cell.

  CompId : {C : Comp} → CompM C C
  CompId {C}= IndData.CompId prev , var ,
    ExtΠ λ v → sym (cong-app (IndData.SphereId prev) (bdryVar C v))

  CompRu : {C D : Comp}(σ : CompM C D) → Comp∘ σ CompId ≡ σ
  CompRu σ = ExtΣ (IndData.CompRu prev (uM σ)) refl (Ext≡ _ _)


  CompLu : {C D : Comp}(σ : CompM C D) → Comp∘ CompId σ ≡ σ
  CellId : {C : Comp}(c : Cell C) → CellM CompId c ≡ c

  CompLu (σ , σV , _) = ExtΣ (IndData.CompLu prev σ)
    (ExtΠ λ v → CellId (σV v)) (Ext≡ _ _)
  CellId (var v) = refl
  CellId (coh B A fl τ) = cong (coh B A fl) (CompLu τ)

--------------------------------------------------------------------------------
-- Having defined both composition and identity operations, we may now show that
-- the forgetful functor is indeed a functor.

  u∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D)
    → IndData.Comp∘ prev (uM ρ) (uM σ) ≡ uM (Comp∘ ρ σ)
  u∘ ρ σ = refl

  uId : {C : Comp} → uM (CompId {C}) ≡ IndData.CompId prev
  uId = refl

{- 3.2.5 Spheres -}
--------------------------------------------------------------------------------
-- We proceed now to define the functor of spheres.

  Sphere : (C : Comp) → Set ℓ
  Sphere C = Σ[ s ∈ Cell C ] Σ[ t ∈ Cell C ] (bdry C s ≡ bdry C t)

  SphereM : {C D : Comp}(σ : CompM C D)(A : Sphere C) → Sphere D
  SphereM {C} {D} σ (s , t , h) = (CellM σ s , CellM σ t , (begin
    bdry D (CellM σ s)
      ≡⟨ bdryM σ s ⟩
    IndData.SphereM prev (uM σ) (bdry C s)
      ≡⟨ cong (IndData.SphereM prev (uM σ)) h ⟩
    IndData.SphereM prev (uM σ) (bdry C t)
      ≡⟨ sym (bdryM σ t) ⟩
    bdry D (CellM σ t)
      ∎))

  Sphere∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D)
    → (SphereM ρ) ∘ (SphereM σ) ≡ SphereM (Comp∘ ρ σ)
  Sphere∘ ρ σ = ExtΠ λ (s , t , h) → ExtΣ (Cell∘ ρ σ s) (Cell∘ ρ σ t) (Ext≡ _ _)

  SphereId : {C : Comp} → SphereM (CompId {C}) ≡ id
  SphereId = ExtΠ λ (s , t , h) → ExtΣ (CellId s) (CellId t) (Ext≡ _ _)

{- 3.2.6 The free functor -}
--------------------------------------------------------------------------------
-- We define now the action of Free on morphisms and show that it is functorial.
-- We then define the auxilliary natural transformation posSphere that is used
-- to define Free.

  FreeM : {X Y : gSet ℓ (suc n)}(f : gSetM X Y) → CompM (Free X) (Free Y)
  FreeM {X} {Y} (f , fₙ₊₁ , f∂) =
    (IndData.FreeM prev f , var ∘ fₙ₊₁ , ExtΠ λ x → begin
      IndData.posSphere prev (gSetTr Y) (gSetBdry Y (fₙ₊₁ x))
        ≡⟨ cong (IndData.posSphere prev (gSetTr Y)) (cong-app f∂ x) ⟩
      IndData.posSphere prev (gSetTr Y) (gSetSphereM f (gSetBdry X x))
        ≡⟨ cong-app (IndData.posSphereM prev f) (gSetBdry X x) ⟩
      IndData.SphereM prev (IndData.FreeM prev f)
      (IndData.posSphere prev (gSetTr X) (gSetBdry X x))
        ∎)

  Free∘ : {X Y Z : gSet ℓ (suc n)}(f : gSetM Y Z)(g : gSetM X Y)
    → Comp∘ (FreeM {Y} {Z} f) (FreeM {X} {Y} g) ≡
    FreeM (gSet∘ {ℓ} {suc n} {X} {Y} {Z} f g)
  Free∘ {X} {Y} {Z} (f , fₙ₊₁ , f∂) (g , gₙ₊₁ , g∂) =
    ExtΣ (IndData.Free∘ prev f g) refl (Ext≡ _ _)

  FreeId : {X : gSet ℓ (suc n)} → FreeM (gSetId {X = X}) ≡ CompId
  FreeId = ExtΣ (IndData.FreeId prev) refl (Ext≡ _ _)

  posSphere : (X : gSet ℓ (suc n))(A : gSetSphere X) → Sphere (Free X)
  posSphere X (s , t , h) =
    (var s , var t , cong (IndData.posSphere prev (gSetTr X)) h)

  posSphereM : {X Y : gSet ℓ (suc n)}(f : gSetM X Y)
    → (posSphere Y) ∘ (gSetSphereM f) ≡ SphereM (FreeM f) ∘ (posSphere X)
  posSphereM {X} {Y} (f , fₙ₊₁ , f∂) =
    ExtΠ λ (s , t , h) → ExtΣ refl refl (Ext≡ _ _)

{- 3.2.7 Support and fullness -}
--------------------------------------------------------------------------------
-- We define now the support of a cell over a Batanin tree, and the set of full
-- spheres.

  supp : {B : Bat}(c : Cell (Free (gSetPos ℓ (suc n) B)))
    → Pos (suc n) B → Bool
  supp (var (lift p)) = Singleton p
  supp (coh B A fl (_ , τV , _)) = Union λ q → supp (τV (lift q))

  Full : {B : Bat}(A : Sphere (Free (gSetPos ℓ (suc n) B))) → Set₀
  Full {B} (s , t , h) =
    (supp s ≡ bdryPosSet ff) ×
    (supp t ≡ bdryPosSet tt) ×
    (IndData.Full prev (bdry (Free (gSetPos ℓ (suc n) B)) s))

{- 3.3 Unpacking the definition -}
--------------------------------------------------------------------------------
-- We finally conclude the inductive step by packing the data above into an
-- instance of AllData.
  Data : AllData ℓ (suc n)
  AllData.prev Data pos = prev
  IndData.Comp (AllData.curr Data) = Comp
  IndData.CompM (AllData.curr Data) = CompM
  IndData.Comp∘ (AllData.curr Data) = Comp∘
  IndData.CompAss (AllData.curr Data) = CompAss
  IndData.CompId (AllData.curr Data) = CompId
  IndData.CompLu (AllData.curr Data) = CompLu
  IndData.CompRu (AllData.curr Data) = CompRu
  IndData.Cell (AllData.curr Data) = Cell
  IndData.CellM (AllData.curr Data) = CellM
  IndData.Cell∘ (AllData.curr Data) ρ σ = ExtΠ (Cell∘ ρ σ)
  IndData.CellId (AllData.curr Data) = ExtΠ CellId
  IndData.Sphere (AllData.curr Data) = Sphere
  IndData.SphereM (AllData.curr Data) = SphereM
  IndData.Sphere∘ (AllData.curr Data) = Sphere∘
  IndData.SphereId (AllData.curr Data) = SphereId
  IndData.Free (AllData.curr Data) = Free
  IndData.FreeM (AllData.curr Data) = FreeM
  IndData.Free∘ (AllData.curr Data) = Free∘
  IndData.FreeId (AllData.curr Data) = FreeId
  IndData.posSphere (AllData.curr Data) = posSphere
  IndData.posSphereM (AllData.curr Data) = posSphereM
  IndData.Full (AllData.curr Data) = Full
  AllData.u Data _ = u
  AllData.uM Data _ = uM
  AllData.u∘ Data _ = u∘
  AllData.uId Data _ {C} = uId {C}
  AllData.bdry Data _ = bdry
  AllData.bdryM Data _ σ = ExtΠ (bdryM σ)

--------------------------------------------------------------------------------
-- Having defined both the base case and the inductive step, we can now define
-- the function Data : (n : Nat) → AllData n containing all the defined data,
-- and for ease of further use, we finally unpack the data of Data n.

Data : (ℓ : Level)(n : Nat) → AllData ℓ n
Data ℓ zero = Zero.Data ℓ
Data ℓ (suc n) = Step.Data ℓ n (AllData.curr (Data ℓ n))

{- The categories of n-computads -}
Comp : (ℓ : Level)(n : Nat) → Set (lsuc ℓ)
CompM : {ℓ : Level}{n : Nat}(C D : Comp ℓ n) → Set ℓ
Comp∘ : {ℓ : Level}{n : Nat}{C D E : Comp ℓ n}(ρ : CompM D E)(σ : CompM C D)
  → CompM C E
CompAss : {ℓ : Level}{n : Nat}{C D E F : Comp ℓ n}(ρ : CompM E F)(σ : CompM D E)
  (τ : CompM C D) → Comp∘ ρ (Comp∘ σ τ) ≡ Comp∘ (Comp∘ ρ σ) τ
CompId : {ℓ : Level}{n : Nat}{C : Comp ℓ n} → CompM C C
CompLu : {ℓ : Level}{n : Nat}{C D : Comp ℓ n}(σ : CompM C D)
  → Comp∘ CompId σ ≡ σ
CompRu : {ℓ : Level}{n : Nat}{C D : Comp ℓ n}(σ : CompM C D)
  → Comp∘ σ CompId ≡ σ

{- The functors of cells -}
Cell : {ℓ : Level}{n : Nat}(C : Comp ℓ n) → Set ℓ
CellM : {ℓ : Level}{n : Nat}{C D : Comp ℓ n}(σ : CompM C D) → Cell C → Cell D
Cell∘ : {ℓ : Level}{n : Nat}{C D E : Comp ℓ n}(ρ : CompM D E)(σ : CompM C D)
  → (CellM ρ) ∘ (CellM σ) ≡ CellM (Comp∘ ρ σ)
CellId : {ℓ : Level}{n : Nat}{C : Comp ℓ n} → CellM (CompId {C = C}) ≡ id

{- The functors of spheres -}
Sphere : {ℓ : Level}{n : Nat}(C : Comp ℓ n) → Set ℓ
SphereM : {ℓ : Level}{n : Nat}{C D : Comp ℓ n}(σ : CompM C D) → Sphere C
  → Sphere D
Sphere∘ : {ℓ : Level}{n : Nat}{C D E : Comp ℓ n}(ρ : CompM D E)(σ : CompM C D)
  → (SphereM ρ) ∘ (SphereM σ) ≡ SphereM (Comp∘ ρ σ)
SphereId : {ℓ : Level}{n : Nat}{C : Comp ℓ n} → SphereM (CompId {C = C}) ≡ id

{- The free functors -}
Free : {ℓ : Level}{n : Nat}(X : gSet ℓ n) → Comp ℓ n
FreeM : {ℓ : Level}{n : Nat}{X Y : gSet ℓ n}(f : gSetM X Y)
  → CompM (Free X) (Free Y)
Free∘ : {ℓ : Level}{n : Nat}{X Y Z : gSet ℓ n}(f : gSetM Y Z)(g : gSetM X Y)
  → Comp∘ (FreeM f) (FreeM g) ≡ FreeM (gSet∘ f g)
FreeId : {ℓ : Level}{n : Nat}{X : gSet ℓ n} → FreeM (gSetId {X = X}) ≡ CompId

{- The truncation functors -}
u : {ℓ : Level}{n : Nat} → (C : Comp ℓ (suc n)) → Comp ℓ n
uM : {ℓ : Level}{n : Nat}{C D : Comp ℓ (suc n)}(σ : CompM C D)
  → CompM (u C) (u D)
u∘ : {ℓ : Level}{n : Nat}{C D E : Comp ℓ (suc n)}(ρ : CompM D E)(σ : CompM C D)
  → Comp∘ (uM ρ) (uM σ) ≡ uM (Comp∘ ρ σ)
uId : {ℓ : Level}{n : Nat}{C : Comp ℓ (suc n)} → uM (CompId {C = C}) ≡ CompId

{- The boundary natural transformation -}
bdry : {ℓ : Level}{n : Nat}(C : Comp ℓ (suc n)) → Cell C → Sphere (u C)
bdryM : {ℓ : Level}{n : Nat}{C D : Comp ℓ (suc n)}(σ : CompM C D)
  → (bdry D) ∘ (CellM σ) ≡ (SphereM (uM σ)) ∘ (bdry C)

--------------------------------------------------------------------------------
Comp ℓ n = IndData.Comp (AllData.curr (Data ℓ n))
CompM {ℓ} {n} = IndData.CompM (AllData.curr (Data ℓ n))
Comp∘ {ℓ} {n} = IndData.Comp∘ (AllData.curr (Data ℓ n))
CompAss {ℓ} {n} = IndData.CompAss (AllData.curr (Data ℓ n))
CompId {ℓ} {n} = IndData.CompId (AllData.curr (Data ℓ n))
CompLu {ℓ} {n} = IndData.CompLu (AllData.curr (Data ℓ n))
CompRu {ℓ} {n} = IndData.CompRu (AllData.curr (Data ℓ n))
Cell {ℓ} {n} = IndData.Cell (AllData.curr (Data ℓ n))
CellM {ℓ} {n} = IndData.CellM (AllData.curr (Data ℓ n))
Cell∘ {ℓ} {n} = IndData.Cell∘ (AllData.curr (Data ℓ n))
CellId {ℓ} {n} = IndData.CellId (AllData.curr (Data ℓ n))
Sphere {ℓ} {n} = IndData.Sphere (AllData.curr (Data ℓ n))
SphereM {ℓ} {n} = IndData.SphereM (AllData.curr (Data ℓ n))
Sphere∘ {ℓ} {n} = IndData.Sphere∘ (AllData.curr (Data ℓ n))
SphereId {ℓ} {n} = IndData.SphereId (AllData.curr (Data ℓ n))
Free {ℓ} {n} = IndData.Free (AllData.curr (Data ℓ n))
FreeM {ℓ} {n} = IndData.FreeM (AllData.curr (Data ℓ n))
Free∘ {ℓ} {n} = IndData.Free∘ (AllData.curr (Data ℓ n))
FreeId {ℓ} {n} = IndData.FreeId (AllData.curr (Data ℓ n))
u {ℓ} {n} = AllData.u (Data ℓ (suc n)) (s≤s z≤n)
uM {ℓ} {n} = AllData.uM (Data ℓ (suc n)) (s≤s z≤n)
u∘ {ℓ} {n} = AllData.u∘ (Data ℓ (suc n)) (s≤s z≤n)
uId {ℓ} {n} {C} = AllData.uId (Data ℓ (suc n)) (s≤s z≤n) {C}
bdry {ℓ} {n} = AllData.bdry (Data ℓ (suc n)) (s≤s z≤n)
bdryM {ℓ} {n} = AllData.bdryM (Data ℓ (suc n)) (s≤s z≤n)
