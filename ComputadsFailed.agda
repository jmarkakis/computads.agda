{-# OPTIONS --no-termination-check --no-positivity-check #-}
module ComputadsFailed where

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
    We define inductively on n, 
        → the category Compₙ of computads
        ­→ the functors Cellₙ : Compₙ → Set returning the n-dimensional cells
          of the free ω-category on a computad
        → the functor Sphereₙ : Compₙ → Set returning the parallel pairs of
          n-dimensional cells of a computad
        → the inclusion Freeₙ : GSetₙ → Compₙ of n-truncated globular sets into
          n-dimensional computads together
        → a collection of 'full' spheres for every computad free on a tree,
          which will be given a filler in the next dimension. Those are
          determined by the 'free variables' of their cells, that is which
          positions are used to define them.
        → a truncation functor TrCompₙ : Compₙ → Compₙ₋₁ for n > 0 forgetting the
          n-dimensional generators of a computad
        → a natural transformation ∂Cellₙ : Cellₙ ⇒ Sphereₙ₋₁TrCompₙ for n > 0
          that assigns a source and target to every n-dimensional cell.
    We will do this in two steps. First we will define a semi-category Compₙ and
    semi-functors, and then define the identity of Compₙ and show that it is
    also preserved by the semi-functors.
-}

Comp : (n : Nat) → Set₁
CompM : {n : Nat}(C D : Comp n) → Set
Comp∘ : {n : Nat}{C D E : Comp n}(ρ : CompM D E)(σ : CompM C D) → CompM C E
CompAss : {n : Nat}{C D E F : Comp n}(ρ : CompM E F)(σ : CompM D E)
    (τ : CompM C D) → Comp∘ ρ (Comp∘ σ τ) ≡ Comp∘ (Comp∘ ρ σ) τ  
Cell : {n : Nat}(C : Comp n) → Set
CellM : {n : Nat}{C D : Comp n}(σ : CompM C D)(c : Cell C) → Cell D
Cell∘ : {n : Nat}{C D E : Comp n}(ρ : CompM D E)(σ : CompM C D)(c : Cell C)
    → CellM ρ (CellM σ c) ≡ CellM (Comp∘ ρ σ) c
Sphere : {n : Nat}(C : Comp n) → Set
SphereM : {n : Nat}{C D : Comp n}(σ : CompM C D)(A : Sphere C) → Sphere D
Sphere∘ : {n : Nat}{C D E : Comp n}(ρ : CompM D E)(σ : CompM C D)(A : Sphere C)
    → SphereM ρ (SphereM σ A) ≡ SphereM (Comp∘ ρ σ) A
Free : {n : Nat}(X : GSet n) → Comp n
ParTopToSphere : {n : Nat}{X : GSet n}(A : ParTop X) → Sphere (Free X)
fv : {n : Nat}{B : Tree}(c : Cell (Free (treeToGSet n B))) → Pos n B → Bool
Full : {n : Nat}{B : Tree}(A : Sphere (Free (treeToGSet n B))) → Set
TrComp : {n : Nat}(n>0 : n > 0)(C : Comp n) → Comp (pred n)
TrCompM : {n : Nat}(n>0 : n > 0){C D : Comp n}(σ : CompM C D) → 
    CompM (TrComp n>0 C) (TrComp n>0 D)
TrComp∘ : {n : Nat}(n>0 : n > 0){C D E : Comp n}(ρ : CompM D E)(σ : CompM C D)
    → Comp∘ (TrCompM n>0 ρ) (TrCompM n>0 σ)
        ≡ TrCompM n>0 (Comp∘ ρ σ)
∂Cell : {n : Nat}(n>0 : n > 0)(C : Comp n)(c : Cell C) → Sphere (TrComp n>0 C)
∂CellNat : {n : Nat}(n>0 : n > 0){C D : Comp n}(σ : CompM C D)(c : Cell C) →
    ∂Cell n>0 D (CellM σ c) ≡ SphereM (TrCompM n>0 σ) (∂Cell n>0 C c)
TopComp : {n : Nat}(C : Comp n) → Set
∂Var : {n : Nat}(n>0 : n > 0)(C : Comp n)(v : TopComp C) → Sphere (TrComp n>0 C)

Comp zero = Set
Comp (suc n) = 
    Σ[ Cn ∈ Comp n ] 
    Σ[ V ∈ Set ] 
    (V → Sphere Cn)
TrComp (s≤s z≤n) (Cn , V , ∂C) = Cn
TopComp {zero} C = C
TopComp {suc n} (Cn , V , ∂C) = V
∂Var (s≤s z≤n) (Cn , V , ∂C)  = ∂C

Free {zero} X = X
Free {suc n} (Xn , TopX , ∂X) = Free Xn , TopX , ParTopToSphere ∘ ∂X 

CompM {zero} C D = C → D
CompM {suc n} C D = 
    Σ[ σn ∈ CompM (TrComp n>0 C) (TrComp n>0 D) ] 
    Σ[ σv ∈ ((TopComp C) → Cell D) ] 
    ((v : TopComp C) → (∂Cell n>0 D) (σv v) ≡ SphereM σn (∂Var n>0 C v))
    where n>0 = s≤s z≤n
TrCompM (s≤s z≤n) (σn , _) = σn

data CellS {n : Nat}(C : Comp (suc n)) : Set where
    var : (v : TopComp C) → CellS C
    coh : (B : Tree)(dB : dim B ≤ suc n)(A : Sphere (Free (treeToGSet n B)))
        (fl : Full A)(τ : CompM (Free (treeToGSet (suc n) B)) C)
        → CellS C
Cell {zero} C = C
Cell {suc n} C = CellS C

∂Cell (s≤s z≤n) C (var v) = ∂Var (s≤s z≤n) C v
∂Cell (s≤s z≤n) C (coh B dB A fl τ) = SphereM (TrCompM (s≤s z≤n) τ) A

CellM {zero} σ c = σ c
CellM {suc n} (_ , σv , _) (var v) = σv v
CellM {suc n} σ (coh B dB A fl τ) = coh B dB A fl (Comp∘ σ τ)

Comp∘ {zero} ρ σ = ρ ∘ σ
Comp∘ {suc n} {C} {D} {E} ρ@(ρn , ρv , ∂ρ) σ@(σn , σv , ∂σ) = 
    Comp∘ ρn σn , CellM ρ ∘ σv , λ v → begin 
        ∂Cell n>0 E (CellM ρ (σv v))
            ≡⟨ ∂CellNat n>0 ρ (σv v) ⟩
        SphereM ρn (∂Cell n>0 D (σv v))
            ≡⟨ cong (SphereM ρn) (∂σ v) ⟩
        SphereM ρn ((SphereM σn) (∂Var n>0 C v))
            ≡⟨ Sphere∘ ρn σn _ ⟩
        SphereM (Comp∘ ρn σn) (∂Var n>0 C v)
            ∎
        where n>0 = s≤s z≤n

∂CellNat (s≤s z≤n) (σn , σv , ∂σ) (var v) = ∂σ v
∂CellNat (s≤s z≤n) (σn , σv , ∂σ) (coh B dB A fl (τn , _)) = 
    sym (Sphere∘ σn τn A)
TrComp∘ (s≤s z≤n) ρ σ = refl

CompAss {zero} ρ σ τ = refl
CompAss {suc n} ρ@(ρn , ρv , ∂ρ) σ@(σn , σv , ∂σ) τ@(τn , τv , ∂τ) = ExtΣ 
    (CompAss ρn σn τn) 
    (Ext λ v → Cell∘ ρ σ (τv v)) 
    (Ext λ v → uip _ _)

Cell∘ {zero} ρ σ c = refl
Cell∘ {suc n} ρ σ (var v) = refl
Cell∘ {suc n} ρ σ (coh B dB A fl τ) = cong (coh B dB A fl) (CompAss ρ σ τ)

Sphere {zero} C = Cell C × Cell C
Sphere {suc n} C = 
    Σ[ s ∈ Cell C ]
    Σ[ t ∈ Cell C ]
    (∂Cell p C s ≡ ∂Cell p C t)
    where p = s≤s z≤n

SphereM {zero} σ (s , t) = (CellM σ s , CellM σ t )
SphereM {suc n} {C} {D} σ@(σn , _ , ∂σ) (s , t , p) = CellM σ s , CellM σ t , 
    ((begin
        ∂Cell n>0 D (CellM σ s)
            ≡⟨ ∂CellNat n>0 σ s ⟩
        SphereM σn (∂Cell n>0 C s)
            ≡⟨ cong (SphereM σn) p ⟩
        SphereM σn (∂Cell n>0 C t)
            ≡⟨ sym (∂CellNat n>0 σ t) ⟩
        ∂Cell n>0 D (CellM σ t)
            ∎))
    where n>0 = s≤s z≤n

Sphere∘ {zero} ρ σ A = refl
Sphere∘ {suc n} ρ σ (s , t , p) = ExtΣ 
    (Cell∘ ρ σ s)
    (Cell∘ ρ σ t)
    (uip _ _)


ParTopToSphere {zero} = id
ParTopToSphere {suc n} (s , t , p) = var s , var t , 
        cong ParTopToSphere p
fv {zero} c q = isYes (equalPos c q)
fv {suc n} (var v) q = isYes (equalPos v q)
fv {suc n} (coh B dB A fl (_ , τv , _)) q = suprBool λ p → fv (τv p) q
Full {zero} {B} (s , t) = 
    fv {zero} {B} s ≡ bdryPos false × fv {zero} {B} t ≡ bdryPos true
Full {suc n} {B} (s , t , p) = Σ[ fvs ∈ fv {suc n} {B} s ≡ bdryPos false ]
        Σ[ fvt ∈ fv {suc n} {B} t ≡ bdryPos true ]        
        (Full (∂Cell (s≤s z≤n) _ s))


CompId : {n : Nat}{C : Comp n} → CompM C C
CompLu : {n : Nat}{C D : Comp n}(σ : CompM C D) → Comp∘ CompId σ ≡ σ
CompRu : {n : Nat}{C D : Comp n}(σ : CompM C D) → Comp∘ σ CompId ≡ σ
CellId : {n : Nat}{C : Comp n}(c : Cell C) → CellM (CompId {C = C}) c ≡ c
SphereId : {n : Nat}{C : Comp n}(A : Sphere C) → SphereM CompId A ≡ A
FreeM : {n : Nat}{X Y : GSet n}(f : GSetM X Y) → CompM (Free X) (Free Y)
Free∘ : {n : Nat}{X Y Z : GSet n}(f : GSetM Y Z)(g : GSetM X Y)
    → Comp∘ (FreeM f) (FreeM g) ≡ FreeM (GSet∘ f g)
FreeId :{n : Nat}{X : GSet n} → FreeM (GSetId {X = X}) ≡ CompId
TrCompId : {n : Nat}(p : n > 0){C : Comp n} → 
    TrCompM p (CompId {C = C}) ≡ CompId 
ParTopToSphereM : {n : Nat}{X Y : GSet n}(f : GSetM X Y)(A : ParTop X) 
    → ParTopToSphere (ParTopM f A) ≡ SphereM (FreeM f) (ParTopToSphere A)

CompId {zero} {C} = id
CompId {suc n} = CompId , var , λ v → sym (SphereId _)
CompLu {zero} σ = refl
CompLu {suc n} {C} {D} (_ , σv , _) = 
    ExtΣ (CompLu _) (Ext λ v → CellId {suc n} {D} (σv v)) (Ext λ v → uip _ _)
CompRu {zero} σ = refl
CompRu {suc n} σ = ExtΣ (CompRu _) refl (Ext λ v → uip _ _)
CellId {zero} c = refl
CellId {suc n} (var v) = refl
CellId {suc n} (coh B dB A fl τ) = cong (coh B dB A fl) (CompLu τ)
SphereId {zero} A = refl
SphereId {suc n} {C} (s , t , p) = 
    ExtΣ (CellId {suc n} {C} s) (CellId {suc n} {C} t) (uip _ _)
FreeM {zero} = id
FreeM {suc n} {X@(_ , _ , ∂X)} {Y@(_ , _ , ∂Y)} (fn , Topf , ∂f) = 
    FreeM fn , var ∘ Topf , λ x → begin
            ParTopToSphere (∂Y (Topf x))
                ≡⟨ cong ParTopToSphere (∂f x) ⟩
            ParTopToSphere (ParTopM fn (∂X x))
                ≡⟨ ParTopToSphereM fn (∂X x) ⟩
            SphereM (FreeM fn) 
                (ParTopToSphere (∂X x))
            ∎

Free∘ {zero} f g = refl
Free∘ {suc n} {X} {Y} {Z} f g = ExtΣ 
        (Free∘  (TrGSetM {_} {Y} {Z} f) (TrGSetM {_} {X} {Y} g)) 
        refl (Ext λ x → uip _ _)
FreeId {zero} = refl
FreeId {suc n} = ExtΣ FreeId refl (Ext λ x → uip _ _)
TrCompId (s≤s z≤n) = refl
ParTopToSphereM {zero} f A = refl
ParTopToSphereM {suc n} f A = ExtΣ refl refl (uip _ _)


 