{- 
Author : Ioannis Markakis (github.com/jmarkakis)
with significant help by Alex Rice (github.com/alexarice)
-}

module Computads where

open import Level using ( 0ℓ )
open import Axiom.Extensionality.Propositional
open import Axiom.UniquenessOfIdentityProofs.WithK

open import Data.Nat renaming (ℕ to Nat)
open import Data.Nat.Properties
open import Data.Bool renaming ( _≤_ to _b≤_ )
open import Data.Product
open import Function
open import Data.Unit using ( ⊤ ; tt)
open import Relation.Binary.Definitions 
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Relation.Binary.PropositionalEquality
open Relation.Binary.PropositionalEquality.≡-Reasoning

postulate Ext : Axiom.Extensionality.Propositional.Extensionality 0ℓ 0ℓ

cong₃ : {A B D : Set}{C : (a : A) → B → Set}{a a' : A}{b b' : B}{c : C a b}
        (f : (a : A) → (b : B) →(c : C a b) → D){c' : C a' b'}(pa : a ≡ a')
        (pb : b ≡ b')(pc : subst₂ C pa pb c ≡ c') → f a b c ≡ f a' b' c'
cong₃ f refl refl refl = refl

ExtΣ : {A B : Set}{C : A → B → Set}{a a' : A}{b b' : B}{c : C a b}{c' : C a' b'}
        (pa : a ≡ a')(pb : b ≡ b')(pc : subst₂ C pa pb c ≡ c' ) → 
        (a , b , c) ≡ (a' , b' , c')
ExtΣ = cong₃ (λ a b c → a , b , c)

--------------------------------------------------------------------------------
-- Batanin Trees
--------------------------------------------------------------------------------

data Tree : Set where
    pt : Tree
    S_∨_ : Tree → Tree → Tree

dim : Tree → Nat
dim pt = zero
dim (S B ∨ B') = suc (dim B) ⊔ dim B'

data Pos : Nat → Tree → Set where
    left : (B : Tree) → Pos 0 B
    up : {n : Nat} (B B' : Tree) → (p : Pos n B) → Pos (suc n) (S B ∨ B')
    right : {n : Nat} (B B' : Tree) → (q : Pos n B') → Pos n (S B ∨ B')

∂Pos : {n : Nat}{B : Tree} → Bool → Pos (suc n) B → Pos n B
∂Pos b (right B B' p) = right B B' (∂Pos b p)
∂Pos {zero} false (up B B' _) = left (S B ∨ B')
∂Pos {zero} true (up B B' _) = right B B' (left B')
∂Pos {suc _} b (up B B' p) = up B B' (∂Pos b p)

globPos : {n : Nat}{B : Tree}(p : Pos (suc (suc n)) B)(b : Bool) → 
    ∂Pos b (∂Pos false p) ≡ ∂Pos b (∂Pos true p) 
globPos {zero} (up _ _ _) false = refl
globPos {zero} (up _ _ _) true = refl
globPos {suc _} (up B B' p) b = cong (up B B') (globPos p b)
globPos (right B B' p) b = cong (right B B') (globPos p b)

bdryPos : {n : Nat}{B : Tree} → Bool → Pos n B → Bool
bdryPos b (up _ _ p) = bdryPos b p
bdryPos false (left _) = true
bdryPos true (left pt) = true
bdryPos true (left (S _ ∨ _)) = false
bdryPos true (right B B' p) = bdryPos true p
bdryPos false (right B B' (left .B')) = false
bdryPos false (right B B' p) = bdryPos false p

--------------------------------------------------------------------------------
-- Auxiliary Functions on Trees
--------------------------------------------------------------------------------
{-
    We show that the sets of positions have decidable equality, and being finite
    we calculate the supremum of a family of booleans indexed
    by positions of a tree.
-}

up-inj : {n : Nat}{B B' : Tree}{p p' : Pos n B}
    → up B B' p ≡ up B B' p' → p ≡ p'
up-inj refl = refl

right-inj : {n : Nat}{B B' : Tree}{p p' : Pos n B'}
    → right B B' p ≡ right B B' p' → p ≡ p'
right-inj refl = refl

equalPos : {n : Nat}{B : Tree} → DecidableEquality (Pos n B)
equalPos (left _) (left _) = yes refl
equalPos (up B B' x) (up B B' y) with equalPos x y
... | yes p = yes (cong (up B B') p)
... | no p = no λ q → p (up-inj q)
equalPos (right B B' x) (right B B' y) with equalPos x y
... | yes p = yes (cong (right B B') p)
... | no p = no λ q → p (right-inj q)
equalPos (up _ _ _) (right _ _ _) = no (λ ())
equalPos (right _ _ _) (left _) = no (λ ())
equalPos (right _ _ _) (up _ _ _) = no (λ ())
equalPos (left _) (right _ _ _) = no (λ ()) 

suprBool : {n : Nat}{B : Tree}(f : Pos n B → Bool) → Bool
suprBool {zero} {pt} f = f (left _)
suprBool {suc n} {pt} f = false
suprBool {zero} {S B ∨ B'} f = f (left _) ∨ suprBool (λ p → f (right B B' p))
suprBool {suc n} {S B ∨ B'} f = 
    suprBool (λ p → f (up B B' p)) ∨ suprBool (λ p → f (right B B' p))

--------------------------------------------------------------------------------
-- Truncated Globular Set
--------------------------------------------------------------------------------

{-
    We introduce truncated globular sets, using that an (n+1)-truncated globular
    set consists of an n-truncated globular set, a set of (n+1)-cells and a pair
    of functions assigning a source and target to the (n+1)-cells, satisfying
    globularity. Hence, we will define categories GSetₙ together with functors
        Topₙ : GSetₙ → Set
        ParTopₙ : GSetₙ → Set    
        TrGSetₙ : GSetₙ₊₁ → GSetₙ
    returning the set of top dimensional cells, the set of pair of parallel top
    dimensional cells and the underlying n-truncated globular set respectively.
    Finally, we will define a natural transformation ∂ₙ : Topₙ₊₁ ⇒ ParTopₙTrGSetₙ
    giving each top dimensional cell a source and target.
-}

GSet : (n : Nat) → Set₁
GSetM : {n : Nat}(X Y : GSet n) → Set
GSet∘ : {n : Nat}{X Y Z : GSet n}(f : GSetM Y Z)(g : GSetM X Y) → GSetM X Z
GSetAss : {n : Nat}{X Y Z W : GSet n}(f : GSetM Z W)(g : GSetM Y Z)
    (h : GSetM X Y) → GSet∘ f (GSet∘ g h) ≡ GSet∘ (GSet∘ f g) h 
GSetId : {n : Nat}{X : GSet n} → GSetM X X
GSetLu : {n : Nat}{X Y : GSet n}(f : GSetM X Y) → GSet∘ GSetId f ≡ f
GSetRu : {n : Nat}{X Y : GSet n}(f : GSetM X Y) → GSet∘ f GSetId ≡ f

Top : {n : Nat}(X : GSet n) → Set
TopM : {n : Nat}{X Y : GSet n}(f : GSetM X Y)(x : Top X) → Top Y
Top∘ : {n : Nat}{X Y Z : GSet n}(f : GSetM Y Z)(g : GSetM X Y)(x : Top X)
    → TopM f (TopM g x) ≡ TopM (GSet∘ f g) x
TopId : {n : Nat}{X : GSet n}(x : Top X) → TopM GSetId x ≡ x

ParTop : {n : Nat}(X : GSet n) → Set
ParTopM : {n : Nat}{X Y : GSet n}(f : GSetM X Y)(A : ParTop X) → ParTop Y
ParTop∘ : {n : Nat}{X Y Z : GSet n}(f : GSetM Y Z)(g : GSetM X Y)(A : ParTop X)
    → ParTopM f (ParTopM g A) ≡ ParTopM (GSet∘ f g) A
ParTopId : {n : Nat}{X : GSet n}(A : ParTop X) → ParTopM GSetId A ≡ A

TrGSet : {n : Nat}(X : GSet (suc n)) → GSet n
TrGSetM : {n : Nat}{X Y : GSet (suc n)}(f : GSetM X Y) 
    → GSetM (TrGSet X) (TrGSet Y)
TrGSet∘ : {n : Nat}{X Y Z : GSet (suc n)}(f : GSetM Y Z)(g : GSetM X Y)
    → GSet∘ (TrGSetM f) (TrGSetM g) ≡ TrGSetM (GSet∘ f g)
TrGSetId : {n : Nat}{X : GSet (suc n)} → TrGSetM (GSetId {X = X}) ≡ GSetId

∂GSet : {n : Nat}(X : GSet (suc n))(x : Top X) → ParTop (TrGSet X)
∂GSetNat : {n : Nat}{X Y : GSet (suc n)}(f : GSetM X Y)(x : Top X)
    → ∂GSet Y (TopM f x) ≡ ParTopM (TrGSetM f) (∂GSet X x)

GSet zero = Set
GSet (suc n) = 
    Σ[ Xn ∈ GSet n ] 
    Σ[ TopX ∈ Set ] 
    (TopX → ParTop Xn)
TrGSet (Xn , _) = Xn
Top {zero} X = X
Top {suc n} (_ , TopX , _) = TopX
∂GSet (_ , _ , ∂X)= ∂X
ParTop {zero} X = Top X × Top X
ParTop {suc n} X = 
    Σ[ s ∈ Top X ]
    Σ[ t ∈ Top X ]
    ∂GSet X s ≡ ∂GSet X t

GSetM {zero} X Y = X → Y
GSetM {suc n} (Xn , TopX , ∂X) (Yn , TopY , ∂Y) = 
    Σ[ fn ∈ GSetM Xn Yn ]
    Σ[ Topf ∈ (TopX → TopY) ]
    ((x : TopX) → ∂Y (Topf x) ≡ ParTopM fn (∂X x))
TrGSetM (fn , _)= fn
TopM {zero} f = f
TopM {suc n} (_ , Topf , _) = Topf
ParTopM {zero} f (s , t) = (f s , f t)
ParTopM {suc n} {Xn , TopX , ∂X} {Yn , TopY , ∂Y} (fn , Topf , ∂f) (s , t , p) = 
    (Topf s , Topf t , (begin 
        ∂Y (Topf s) 
            ≡⟨ ∂f s ⟩ 
        ParTopM fn (∂X s)
            ≡⟨ cong (ParTopM fn) p ⟩ 
        ParTopM fn (∂X t)
            ≡⟨ sym (∂f t) ⟩ 
        ∂Y (Topf t) 
            ∎))
∂GSetNat (fn , Topf , ∂f) = ∂f

GSet∘ {zero} f g = f ∘ g
GSet∘ {suc n} {_ , _ , ∂X} {_ , _ , ∂Y} {_ , _ , ∂Z} 
    (fn , Topf , ∂f) (gn , Topg , ∂g) = 
    GSet∘ fn gn , Topf ∘ Topg , λ x → begin 
        ∂Z (Topf (Topg x)) 
            ≡⟨ ∂f (Topg x) ⟩ 
        ParTopM fn (∂Y (Topg x))
            ≡⟨ cong (ParTopM fn) (∂g x) ⟩
        ParTopM fn (ParTopM gn (∂X x))
            ≡⟨ (ParTop∘ fn gn) (∂X x) ⟩
        ParTopM (GSet∘ fn gn) (∂X x)
            ∎
TrGSet∘ f g = refl
Top∘ {zero} f g x = refl
Top∘ {suc n} f g x = refl
ParTop∘ {zero} f g A = refl
ParTop∘ {suc n} f g A = ExtΣ refl refl (uip _ _)
GSetAss {zero} f g h = refl
GSetAss {suc n} (fn , _) (gn , _) (hn , _) = 
    ExtΣ (GSetAss fn gn hn) refl (Ext λ x → uip _ _)

GSetId {zero} {X} = id
GSetId {suc n} {Xn , TopX , ∂X} = 
    GSetId , id , λ x → sym ((ParTopId) (∂X x))
TrGSetId = refl
TopId {zero} x = refl
TopId {suc n} x = refl
ParTopId {zero} {X} A = refl
ParTopId {suc n} {X} A = ExtΣ refl refl (uip _ _)

GSetLu {zero} f = refl
GSetLu {suc n} (fn , Topf , ∂f) = ExtΣ (GSetLu fn) refl (Ext λ x → uip _ _)
GSetRu {zero} f = refl
GSetRu {suc n} (fn , Topf , ∂f) = ExtΣ (GSetRu fn) refl (Ext λ x → uip _ _)

--------------------------------------------------------------------------------
-- Trees To Globular Sets
--------------------------------------------------------------------------------

treeToGSet : (n : Nat)(B : Tree) → GSet n
treeToGSet∂ : {n : Nat}{B : Tree}(q : Pos (suc n) B) → ParTop (treeToGSet n B)
treeToGSetGlob : {n : Nat}{B : Tree}(q q' : Pos (suc n) B) 
    (gl : (b : Bool) → ∂Pos b q ≡ ∂Pos b q') → treeToGSet∂ q ≡ treeToGSet∂ q'

treeToGSet zero B = Pos zero B
treeToGSet (suc n) B = treeToGSet n B , Pos (suc n) B , treeToGSet∂
treeToGSet∂ {zero} q = ∂Pos false q , ∂Pos true q
treeToGSet∂ {suc n} q = ∂Pos false q , ∂Pos true q , 
    treeToGSetGlob _ _ (globPos q)
treeToGSetGlob {zero} q q' gl = cong₂ _,_ (gl false) (gl true)
treeToGSetGlob {suc n} q q' gl = ExtΣ (gl false) (gl true) (uip _ _)

--------------------------------------------------------------------------------
-- Finite Dimensional Computads
--------------------------------------------------------------------------------

{-
    We define inductively on n, the category Compₙ of computads together with 
    the functors Cellₙ , Sphereₙ : Compₙ → Set returning the n-dimensional cells
    of the free ω-category on a computad, and parallel pairs of cells
    respectively. We define also an inclusion of n-truncated globular sets into
    computads and a collection of Spheres of computads free on a tree, which we
    call full and give a canonical filler in the next dimension. Finally, we
    define for n > 0 a truncation functor and a boundary natural transformation
    TrCompₙ : Compₙ → Compₙ₋₁ and ∂Cellₙ : Cellₙ ⇒ Sphereₙ₋₁TrCompₙ that forget
    the top dimensional generators of a computad, and they assign a source and
    target to every n-dimensional cell respectively. In order to do induction
    on n, we define record types containing that data.
-}

record CompDataBase (n : Nat) : Set₂ where
    field
        Comp : Set₁
        CompM : (C D : Comp) → Set
        Comp∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D) → CompM C E
        CompAss : {C D E F : Comp}(ρ : CompM E F)(σ : CompM D E)(τ : CompM C D)
            → Comp∘ ρ (Comp∘ σ τ) ≡ Comp∘ (Comp∘ ρ σ) τ  
        CompId : {C : Comp} → CompM C C
        CompLu : {C D : Comp}(σ : CompM C D) → Comp∘ CompId σ ≡ σ
        CompRu : {C D : Comp}(σ : CompM C D) → Comp∘ σ CompId ≡ σ
        Cell : (C : Comp) → Set
        CellM : {C D : Comp}(σ : CompM C D)(c : Cell C) → Cell D
        Cell∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D)(c : Cell C)
            → CellM ρ (CellM σ c) ≡ CellM (Comp∘ ρ σ) c
        CellId : {C : Comp}(c : Cell C) → CellM CompId c ≡ c
        Sphere : (C : Comp) → Set
        SphereM : {C D : Comp}(σ : CompM C D)(A : Sphere C) → Sphere D
        Sphere∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D)(A : Sphere C)
            → SphereM ρ (SphereM σ A) ≡ SphereM (Comp∘ ρ σ) A
        SphereId : {C : Comp}(A : Sphere C) → SphereM CompId A ≡ A
        Free : (X : GSet n) → Comp
        FreeM : {X Y : GSet n}(f : GSetM X Y) → CompM (Free X) (Free Y)
        Free∘ : {X Y Z : GSet n}(f : GSetM Y Z)(g : GSetM X Y)
            → Comp∘ (FreeM f) (FreeM g) ≡ FreeM (GSet∘ f g)
        FreeId : {X : GSet n} → FreeM (GSetId {X = X}) ≡ CompId
        Full : {B : Tree}(A : Sphere (Free (treeToGSet n B))) → Set
        ParTopToSphere : {X : GSet n}(A : ParTop X) → Sphere (Free X)
        ParTopToSphereM : {X Y : GSet n}(f : GSetM X Y)(A : ParTop X) 
            → ParTopToSphere (ParTopM f A) ≡ 
                SphereM (FreeM f) (ParTopToSphere A)
record CompDataFull (n : Nat) : Set₂ where
    field
        indStep : (p : n > 0) → CompDataBase (pred n)
        base : CompDataBase n
    open CompDataBase base
    field
        TrComp : (p : n > 0)(C : Comp) → CompDataBase.Comp (indStep p)
        TrCompM : (p : n > 0){C D : Comp}(σ : CompM C D) → 
            CompDataBase.CompM (indStep p) (TrComp p C) (TrComp p D)
        TrComp∘ : (p : n > 0){C D E : Comp}(ρ : CompM D E)(σ : CompM C D)
            → CompDataBase.Comp∘ (indStep p) (TrCompM p ρ) (TrCompM p σ)
                ≡ TrCompM p (Comp∘ ρ σ)
        TrCompId : (p : n > 0){C : Comp} → 
            TrCompM p (CompId {C}) ≡ CompDataBase.CompId (indStep p)

        {- The boundary sphere of a cell -}
        ∂Cell : (p : n > 0)(C : Comp) → Cell C → 
            CompDataBase.Sphere (indStep p) (TrComp p C)
        ∂CellNat : (p : n > 0){C D : Comp}(σ : CompM C D)(c : Cell C) →
            ∂Cell p D (CellM σ c) ≡ 
                CompDataBase.SphereM (indStep p) (TrCompM p σ) (∂Cell p C c)

{- Base Case -}
module _ where
    open CompDataBase
    open CompDataFull
    DataZero : CompDataFull zero
    fvZ : {B : Tree}(c : Cell (base DataZero) 
        (Free (base DataZero) (treeToGSet zero B))) → Pos zero B → Bool

    indStep DataZero = λ ()
    Comp (base DataZero) = Set
    CompM (base DataZero) C D = C → D
    Comp∘ (base DataZero) ρ σ = ρ ∘ σ
    CompAss (base DataZero) ρ σ τ = refl
    CompId (base DataZero) = id
    CompLu (base DataZero) σ = refl
    CompRu (base DataZero) σ = refl
    Cell (base DataZero) = id
    CellM (base DataZero) = id
    Cell∘ (base DataZero) ρ σ c = refl
    CellId (base DataZero) c = refl
    Sphere (base DataZero) C = C × C
    SphereM (base DataZero) σ (s , t) = (σ s , σ t)
    Sphere∘ (base DataZero) ρ σ A = refl
    SphereId (base DataZero) A = refl
    Free (base DataZero) = id
    FreeM (base DataZero) = id
    Free∘ (base DataZero) f g = refl
    FreeId (base DataZero) = refl
    Full (base DataZero) (s , t) = fvZ s ≡ bdryPos false × fvZ t ≡ bdryPos true
    ParTopToSphere (base DataZero) = id
    ParTopToSphereM (base DataZero) f A = refl
    TrComp DataZero = λ ()
    TrCompM DataZero = λ ()
    TrComp∘ DataZero = λ ()
    TrCompId DataZero = λ ()
    ∂Cell DataZero = λ ()
    ∂CellNat DataZero = λ ()
    fvZ q q' = isYes (equalPos q q')

{- Inductive Case -}
module _ {n : Nat}(prev : CompDataBase n) where
    Comp : Set₁ 
    Comp = 
        Σ[ Cn ∈ CompDataBase.Comp prev ] 
        Σ[ V ∈ Set ] 
        (V → CompDataBase.Sphere prev Cn)

    TrComp : (C : Comp) → CompDataBase.Comp prev
    TrComp (Cn , _) = Cn

    TopComp : (C : Comp) → Set
    TopComp (_ , V , _) = V

    ∂Var : (C : Comp)(v : TopComp C) → CompDataBase.Sphere prev (TrComp C)
    ∂Var (_ , _ , ∂C) = ∂C

    Free : GSet (suc n) → Comp
    Free (Xn , TopX , ∂X) = CompDataBase.Free prev Xn , TopX , 
        (CompDataBase.ParTopToSphere prev) ∘ ∂X

    CompM : (C D : Comp) → Set
    data Cell (C : Comp) : Set
    ∂Cell : (C : Comp)(c : Cell C) → CompDataBase.Sphere (prev) (TrComp C)
    TrCompM : {C D : Comp}(σ : CompM C D) → 
        CompDataBase.CompM prev (TrComp C) (TrComp D)

    CompM C D = 
        Σ[ σn ∈ CompDataBase.CompM prev (TrComp C) (TrComp D) ] 
        Σ[ σv ∈ ((TopComp C) → Cell D) ] 
        ((v : TopComp C) → 
            (∂Cell D) (σv v) ≡ CompDataBase.SphereM prev σn (∂Var C v))

    TrCompM (σn , _)= σn

    data Cell C where
        var : (v : TopComp C) → Cell C
        coh : (B : Tree)(dB : dim B ≤ suc n)
            (A : CompDataBase.Sphere prev (CompDataBase.Free prev 
            (treeToGSet n B)))(fl : CompDataBase.Full prev A)
            (τ : CompM (Free (treeToGSet (suc n) B)) C)
            → Cell C

    ∂Cell C (var v) = ∂Var C v
    ∂Cell C (coh B dB A fl τ) = CompDataBase.SphereM prev (TrCompM τ) A

    CellM : {C D : Comp}(σ : CompM C D)(c : Cell C) → Cell D
    Comp∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D) → CompM C E
    ∂CellNat : {C D : Comp}(σ : CompM C D)(c : Cell C) 
        → ∂Cell D (CellM σ c) ≡ 
        (CompDataBase.SphereM (prev) (TrCompM σ)) (∂Cell C c)

    CellM {C} {D} (_ , σv , _) (var v) = σv v
    CellM {C} {D} σ (coh B dB A fl τ) = coh B dB A fl (Comp∘ σ τ)
    
    Comp∘ {C} {D} {E} ρ@(ρn , ρv , ∂ρ) σ@(σn , σv , ∂σ) = 
        CompDataBase.Comp∘ prev ρn σn , CellM ρ ∘ σv , λ v → begin 
        ∂Cell E (CellM ρ (σv v))
            ≡⟨ ∂CellNat ρ (σv v) ⟩
        CompDataBase.SphereM prev ρn (∂Cell D (σv v))
            ≡⟨ cong (CompDataBase.SphereM prev ρn) (∂σ v) ⟩
        CompDataBase.SphereM prev ρn ((CompDataBase.SphereM prev σn) (∂Var C v))
            ≡⟨ CompDataBase.Sphere∘ prev ρn σn _ ⟩
        CompDataBase.SphereM prev (CompDataBase.Comp∘ prev ρn σn) (∂Var C v)
            ∎
                    
    ∂CellNat (σn , σv , ∂σ) (var v) = ∂σ v
    ∂CellNat (σn , σv , ∂σ) (coh B dB A fl (τn , _)) = 
        sym (CompDataBase.Sphere∘ prev σn τn A)

    TrComp∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D)
        → CompDataBase.Comp∘ (prev) (TrCompM ρ) (TrCompM σ)
            ≡ TrCompM (Comp∘ ρ σ)
    TrComp∘ ρ σ = refl

    CompId : {C : Comp} → CompM C C
    CompId {C} = CompDataBase.CompId prev , var , 
        λ v → (sym (CompDataBase.SphereId prev _))

    TrCompId : {C : Comp} → 
        TrCompM (CompId {C}) ≡ CompDataBase.CompId prev
    TrCompId = refl
    
    CompRu : {C D : Comp}(σ : CompM C D) → Comp∘ σ CompId ≡ σ
    CompRu σ = ExtΣ (CompDataBase.CompRu prev (TrCompM σ)) refl 
        (Ext λ v → uip _ _)

    CompAss : {C D E F : Comp}(ρ : CompM E F)(σ : CompM D E)(τ : CompM C D)
        → Comp∘ ρ (Comp∘ σ τ) ≡ Comp∘ (Comp∘ ρ σ) τ  
    Cell∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D)(c : Cell C)
        → CellM ρ (CellM σ c) ≡ CellM (Comp∘ ρ σ) c

    CompAss ρ@(ρn , ρv , ∂ρ) σ@(σn , σv , ∂σ) τ@(τn , τv , ∂τ) = 
        ExtΣ (CompDataBase.CompAss prev ρn σn τn)
        (Ext λ v → Cell∘ ρ σ (τv v)) (Ext λ v' → uip _ _)
    Cell∘ ρ σ (var v) = refl
    Cell∘ ρ σ (coh B dB A fl τ) = cong (coh B dB A fl) (CompAss ρ σ τ)

    CompLu : {C D : Comp}(σ : CompM C D) → Comp∘ CompId σ ≡ σ
    CellId : {C : Comp}(c : Cell C) → CellM (CompId {C}) c ≡ c

    CompLu (σn , σv , _) = ExtΣ ((CompDataBase.CompLu prev σn)) 
        (Ext λ v → CellId (σv v)) 
        (Ext λ v → uip _ _)
    CellId (var v) = refl
    CellId (coh B dB A fl τ) = cong (coh B dB A fl) (CompLu τ)
    
    Sphere : (C : Comp) → Set
    Sphere C = Σ[ s ∈ Cell C ] Σ[ t ∈ Cell C ] (∂Cell C s ≡ ∂Cell C t)

    SphereM : {C D : Comp}(σ : CompM C D)(A : Sphere C) → Sphere D
    SphereM {C} {D} σ@(σn , _ , ∂σ) (s , t , p) = CellM σ s , CellM σ t , (begin
        ∂Cell D (CellM σ s)
            ≡⟨ ∂CellNat σ s ⟩
        CompDataBase.SphereM prev σn (∂Cell C s)
            ≡⟨ cong (CompDataBase.SphereM prev σn) p ⟩
        CompDataBase.SphereM prev σn (∂Cell C t)
            ≡⟨ sym (∂CellNat σ t) ⟩
        ∂Cell D (CellM σ t)
            ∎)

    Sphere∘ : {C D E : Comp}(ρ : CompM D E)(σ : CompM C D)(A : Sphere C)
        → SphereM ρ (SphereM σ A) ≡ SphereM (Comp∘ ρ σ) A
    Sphere∘ ρ σ (s , t , p) = ExtΣ (Cell∘ ρ σ s) (Cell∘ ρ σ t) (uip _ _)

    SphereId : {C : Comp}(A : Sphere C) → SphereM CompId A ≡ A
    SphereId (s , t , p) = ExtΣ (CellId s) (CellId t) (uip _ _)

    fvS : {B : Tree}(c : Cell (Free (treeToGSet (suc n) B)))
        (q : Pos (suc n) B) → Bool
    fvS (var p) q = isYes (equalPos p q)
    fvS (coh B dB A fl (_ , τv , _)) q = suprBool λ p → fvS (τv p) q 

    Full : {B : Tree}(A : Sphere (Free (treeToGSet (suc n) B))) → Set
    Full (s , t , p) = 
        Σ[ fvs ∈ fvS s ≡ bdryPos false ]
        Σ[ fvt ∈ fvS t ≡ bdryPos true ]        
        (CompDataBase.Full prev (∂Cell _ s))

    ParTopToSphere : {X : GSet (suc n)}(A : ParTop X) → Sphere (Free X)
    ParTopToSphere (s , t , p) = var s , var t , 
        cong (CompDataBase.ParTopToSphere prev) p

    FreeM : {X Y : GSet (suc n)}(f : GSetM X Y) → CompM (Free X) (Free Y)
    FreeM {X@(_ , _ , ∂X)} {Y@(_ , _ , ∂Y)} (fn , Topf , ∂f) = 
        CompDataBase.FreeM prev fn , var ∘ Topf ,  λ x → begin
            CompDataBase.ParTopToSphere prev (∂Y (Topf x))
                ≡⟨ cong (CompDataBase.ParTopToSphere prev) (∂f x) ⟩
            CompDataBase.ParTopToSphere prev (ParTopM fn (∂X x))
                ≡⟨ CompDataBase.ParTopToSphereM prev fn (∂X x) ⟩
            CompDataBase.SphereM prev (CompDataBase.FreeM prev fn) 
                (CompDataBase.ParTopToSphere prev (∂X x))
            ∎

    ParTopToSphereM : {X Y : GSet (suc n)}(f : GSetM X Y)(A : ParTop X) 
            → ParTopToSphere (ParTopM f A) ≡ 
                SphereM (FreeM {X} {Y} f) (ParTopToSphere A)
    ParTopToSphereM f A = ExtΣ refl refl (uip _ _)

    Free∘ : {X Y Z : GSet (suc n)}(f : GSetM Y Z)(g : GSetM X Y)
        → Comp∘ (FreeM {Y} {Z} f) (FreeM {X} {Y} g) ≡ 
            FreeM (GSet∘ {_} {X} {Y} {Z} f g)
    Free∘ {X} {Y} {Z} f g = ExtΣ 
        (CompDataBase.Free∘ prev (TrGSetM {_} {Y} {Z} f) 
            (TrGSetM {_} {X} {Y} g)) 
        refl 
        (Ext λ x → uip _ _)
    
    FreeId : {X : GSet (suc n)} → FreeM (GSetId {X = X}) ≡ CompId
    FreeId {X} = ExtΣ (CompDataBase.FreeId prev) refl (Ext λ x → uip _ _)

    DataSuc : CompDataFull (suc n)
    CompDataFull.indStep DataSuc _ = prev
    CompDataBase.Comp (CompDataFull.base DataSuc) = Comp
    CompDataBase.CompM (CompDataFull.base DataSuc) = CompM
    CompDataBase.Comp∘ (CompDataFull.base DataSuc) = Comp∘
    CompDataBase.CompAss (CompDataFull.base DataSuc) = CompAss
    CompDataBase.CompId (CompDataFull.base DataSuc) = CompId
    CompDataBase.CompLu (CompDataFull.base DataSuc) = CompLu
    CompDataBase.CompRu (CompDataFull.base DataSuc) = CompRu
    CompDataBase.Cell (CompDataFull.base DataSuc) = Cell
    CompDataBase.CellM (CompDataFull.base DataSuc) = CellM
    CompDataBase.Cell∘ (CompDataFull.base DataSuc) = Cell∘
    CompDataBase.CellId (CompDataFull.base DataSuc) = CellId
    CompDataBase.Sphere (CompDataFull.base DataSuc) = Sphere
    CompDataBase.SphereM (CompDataFull.base DataSuc) = SphereM
    CompDataBase.Sphere∘ (CompDataFull.base DataSuc) = Sphere∘
    CompDataBase.SphereId (CompDataFull.base DataSuc) = SphereId
    CompDataBase.Free (CompDataFull.base DataSuc) = Free
    CompDataBase.FreeM (CompDataFull.base DataSuc) = FreeM
    CompDataBase.Free∘ (CompDataFull.base DataSuc) = Free∘
    CompDataBase.FreeId (CompDataFull.base DataSuc) = FreeId
    CompDataBase.Full (CompDataFull.base DataSuc) = Full
    CompDataBase.ParTopToSphere (CompDataFull.base DataSuc) = ParTopToSphere
    CompDataBase.ParTopToSphereM (CompDataFull.base DataSuc) = ParTopToSphereM
    CompDataFull.TrComp DataSuc _ = TrComp
    CompDataFull.TrCompM DataSuc _ = TrCompM
    CompDataFull.TrComp∘ DataSuc _ = TrComp∘
    CompDataFull.TrCompId DataSuc _ {C} = TrCompId {C}
    CompDataFull.∂Cell DataSuc _ = ∂Cell
    CompDataFull.∂CellNat DataSuc _ = ∂CellNat

CompData : (n : Nat) → CompDataFull n
CompData 0 = DataZero
CompData (suc n) = DataSuc (CompDataFull.base (CompData n))


   