{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product hiding ( curry ; uncurry )
open import Data.Nat hiding ( fold )
open import Data.List
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Function
module RPE where

----------------------------------------------------------------------

one : ℕ
one = suc zero

----------------------------------------------------------------------

Enum : Set
Enum = List String

data Tag : Enum → Set where
  here : ∀{l E} → Tag (l ∷ E)
  there : ∀{l E} → Tag E → Tag (l ∷ E)

Branches : (E : Enum) (P : Tag E → Set) → Set
Branches [] P = ⊤
Branches (l ∷ E) P = P here × Branches E (λ t → P (there t))

case : {E : Enum} (P : Tag E → Set) (cs : Branches E P) (t : Tag E) → P t
case P (c , cs) here = c
case P (c , cs) (there t) = case (λ t → P (there t)) cs t

----------------------------------------------------------------------

Params : Set
Params = ℕ

Pars  : Params → Set
Pars zero = ⊤
Pars (suc n) = Set × Pars n

----------------------------------------------------------------------

data Desc : Set where
  End : Desc
  Rec : (D : Desc) → Desc
  Arg : (A : Set) (D : Desc) → Desc
  Sum : (E : Enum) (B : Tag E → Desc) → Desc

----------------------------------------------------------------------

caseD : {E : Enum} (cs : Branches E (λ _ → Desc)) (t : Tag E) → Desc
caseD = case (λ _ → Desc)

----------------------------------------------------------------------

El : (D : Desc) → Set → Set
El End X = ⊤
El (Rec D) X = X × El D X
El (Arg A D) X = A × El D X
El (Sum E B) X = Σ (Tag E) (λ t → El (B t) X)

----------------------------------------------------------------------

data μ (D : Desc) : Set where
  init : El D (μ D) → μ D

----------------------------------------------------------------------

Recs : (D : Desc) (X Y : Set) → Set
Recs D X Y = El D (X × Y)

----------------------------------------------------------------------

cata : (D : Desc) (X : Set) (α : Recs D (μ D) X → X)
  → μ D → X

mapCata : (D₁ D₂ : Desc) (X : Set) (α : Recs D₂ (μ D₂) X → X)
  → El D₁ (μ D₂) → El D₁ (μ D₂ × X)

cata D X α (init xs) = α (mapCata D D X α xs)

mapCata End D₂ X α tt = tt
mapCata (Rec D₁) D₂ X α (x , xs) = (x , cata D₂ X α x) , mapCata D₁ D₂ X α xs
mapCata (Arg A D₁) D₂ X α (a , xs) = a , mapCata D₁ D₂ X α xs
mapCata (Sum E B) D₂ X α (t , xs) = t , mapCata (B t) D₂ X α xs

----------------------------------------------------------------------

record Data : Set where
  field
    P : Params
    E : Enum
    B : (A : Pars P) → Branches E (λ _ → Desc)

  C : (A : Pars P) → Tag E → Desc
  C A = caseD (B A)

  D : (A : Pars P) → Desc
  D A = Sum E (C A)

----------------------------------------------------------------------

UncurriedBranches : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
UncurriedBranches E P X = Branches E P → X

CurriedBranches : (E : Enum) (P : Tag E → Set) (X : Set)
  → Set
CurriedBranches [] P X = X
CurriedBranches (l ∷ E) P X = P here → CurriedBranches E (λ t → P (there t)) X

curryBranches : (E : Enum) (P : Tag E → Set) (X : Set)
  → UncurriedBranches E P X → CurriedBranches E P X
curryBranches [] P X f = f tt
curryBranches (l ∷ E) P X f = λ c → curryBranches E (λ t → P (there t)) X (λ cs → f (c , cs))

uncurryBranches : (E : Enum) (P : Tag E → Set) (X : Set)
  → CurriedBranches E P X → UncurriedBranches E P X
uncurryBranches [] P X x tt = x
uncurryBranches (l ∷ E) P X f (c , cs) = uncurryBranches E (λ t → P (there t)) X (f c) cs

----------------------------------------------------------------------

UncurriedPars : (P : Params) (X : Pars P → Set) → Set
UncurriedPars P X = (xs : Pars P) → X xs

CurriedPars : (P : Params) (X : Pars P → Set) → Set
CurriedPars zero X = X tt
CurriedPars (suc n) X = (A : Set) → CurriedPars n (λ As → X (A , As))

curryPars : (P : Params) (X : Pars P → Set)
  → UncurriedPars P X → CurriedPars P X
curryPars zero X f = f tt
curryPars (suc n) X f = λ A → curryPars n (λ As → X (A , As)) (λ As → f (A , As))

ICurriedPars : (P : Params) (X : Pars P → Set) → Set
ICurriedPars zero X = X tt
ICurriedPars (suc n) X = {A : Set} → ICurriedPars n (λ As → X (A , As))

icurryPars : (P : Params) (X : Pars P → Set)
  → UncurriedPars P X → ICurriedPars P X
icurryPars zero X f = f tt
icurryPars (suc n) X f = λ {A} → icurryPars n (λ As → X (A , As)) (λ As → f (A , As))

----------------------------------------------------------------------

UncurriedEl : (D : Desc) (X : Set) → Set
UncurriedEl D X = El D X → X

CurriedEl : (D : Desc) (X : Set) → Set
CurriedEl End X = X
CurriedEl (Rec D) X = X → CurriedEl D X
CurriedEl (Arg A D) X = A → CurriedEl D X
CurriedEl (Sum E B) X = (t : Tag E) → CurriedEl (B t) X

curryEl : (D : Desc) (X : Set)
  → UncurriedEl D X → CurriedEl D X
curryEl End X cn = cn tt
curryEl (Rec D) X cn = λ x → curryEl D X (λ xs → cn (x , xs))
curryEl (Arg A D) X cn = λ a → curryEl D X (λ xs → cn (a , xs))
curryEl (Sum E B) X cn = λ t → curryEl (B t) X (λ xs → cn (t , xs))

uncurryEl : (D : Desc) (X : Set)
  → CurriedEl D X → UncurriedEl D X
uncurryEl End X x tt = x
uncurryEl (Rec D) X f (x , xs) = uncurryEl D X (f x) xs
uncurryEl (Arg A D) X f (a , xs) = uncurryEl D X (f a) xs
uncurryEl (Sum E B) X f (t , xs) = uncurryEl (B t) X (f t) xs

----------------------------------------------------------------------

Form : (R : Data)
  → CurriedPars (Data.P R) λ p
  → Set
Form R =
  curryPars (Data.P R) (λ p → Set) -- Parts 1 & 2
            (λ p → μ (Data.D R p)) -- Part 3

----------------------------------------------------------------------

inj : (R : Data)
  → ICurriedPars (Data.P R) λ p
  → let D = Data.D R p
  in CurriedEl D (μ D)
inj R = icurryPars (Data.P R)
  (λ p → let D = Data.D R p in CurriedEl D (μ D))
  (λ p t → curryEl (Data.C R p t)
    (μ (Data.D R p))
    (λ xs → init (t , xs))
  )

----------------------------------------------------------------------

UncurriedRecs : (D : Desc) (X Y : Set) → Set
UncurriedRecs D X Y = Recs D X Y → Y

CurriedRecs : (D : Desc) (X Y : Set) → Set
CurriedRecs End X Y = Y
CurriedRecs (Rec D) X Y = X → Y → CurriedRecs D X Y
CurriedRecs (Arg A D) X Y = A → CurriedRecs D X Y
CurriedRecs (Sum E B) X Y = (t : Tag E) → CurriedRecs (B t) X Y

curryRecs : (D : Desc) (X Y : Set)
  → UncurriedRecs D X Y → CurriedRecs D X Y
curryRecs End X Y cn = cn tt
curryRecs (Rec D) X Y cn = λ x y → curryRecs D X Y (λ xs → cn ((x , y) , xs))
curryRecs (Arg A D) X Y cn = λ a → curryRecs D X Y (λ xs → cn (a , xs))
curryRecs (Sum E B) X Y cn = λ t → curryRecs (B t) X Y (λ xs → cn (t , xs))

uncurryRecs : (D : Desc) (X Y : Set)
  → CurriedRecs D X Y → UncurriedRecs D X Y
uncurryRecs End X Y y tt = y
uncurryRecs (Rec D) X Y f ((x , y) , xs) = uncurryRecs D X Y (f x y) xs
uncurryRecs (Arg A D) X Y f (a , xs) = uncurryRecs D X Y (f a) xs
uncurryRecs (Sum E B) X Y f (t , xs) = uncurryRecs (B t) X Y (f t) xs

----------------------------------------------------------------------

Convoy : (R : Data) (X : Set)
  → UncurriedPars (Data.P R) λ p
  → let D = Data.D R p in
  Tag (Data.E R) → Set
Convoy R X p t =
  CurriedRecs (Data.C R p t) (μ (Data.D R p)) X

fold : (R : Data) {X : Set}
  → ICurriedPars (Data.P R) λ p
  → let D = Data.D R p in
  CurriedBranches (Data.E R)
    (Convoy R X p)
    (μ D → X)
fold R {X} = icurryPars (Data.P R)
  (λ p → CurriedBranches (Data.E R)
    (Convoy R X p)
    (μ (Data.D R p) → X))
  (λ p → curryBranches (Data.E R) _ _
    (λ cs x → let D = Data.D R p in
      cata D X
        (uncurryRecs D (μ D) X
          (λ t → case (Convoy R X p) cs t)
        ) x
    )
  )

----------------------------------------------------------------------

ℕE : Enum
ℕE = "zero" ∷ "suc" ∷ []

ListE : Enum
ListE = "nil" ∷ "cons" ∷ []

TreeE : Enum
TreeE = "leaf₁" ∷ "leaf₂" ∷ "node" ∷ []

ℕT : Set
ℕT = Tag ℕE

ListT : Set
ListT = Tag ListE

TreeT : Set
TreeT = Tag TreeE

zeroT : ℕT
zeroT = here

sucT : ℕT
sucT = there here

nilT : ListT
nilT = here

consT : ListT
consT = there here

leaf₁T : TreeT
leaf₁T = here

leaf₂T : TreeT
leaf₂T = there here

nodeT : TreeT
nodeT = there (there here)

----------------------------------------------------------------------

module Specialized where

  ℕC : Tag ℕE → Desc
  ℕC = caseD (
      End
    , Rec End
    , tt
    )

  ℕD : Desc
  ℕD = Sum ℕE ℕC

  `ℕ : Set
  `ℕ = μ ℕD

  `zero : `ℕ
  `zero = init (zeroT , tt)
  
  `suc : `ℕ → `ℕ
  `suc n = init (sucT , n , tt)

  AddConvoy : ℕT → Set
  AddConvoy t = Recs (ℕC t) `ℕ X → X
    where X = `ℕ → `ℕ

  zeroBranch : AddConvoy zeroT
  zeroBranch u n = n

  sucBranch : AddConvoy sucT
  sucBranch m-rec-u n =
    let u   = proj₂ m-rec-u
        m   = proj₁ (proj₁ m-rec-u)
        rec = proj₂ (proj₁ m-rec-u)
    in `suc (rec n)

  addα : Recs ℕD `ℕ (`ℕ → `ℕ) → `ℕ → `ℕ
  addα m = case AddConvoy
    (zeroBranch , sucBranch , tt)
    (proj₁ m)
    (proj₂ m)

  `add : `ℕ → `ℕ → `ℕ
  `add = cata ℕD (`ℕ → `ℕ) addα

----------------------------------------------------------------------

  TreeC : Set → Set → Tag TreeE → Desc
  TreeC A B = caseD (
      Arg A End
    , Arg B End
    , Rec (Rec End)
    , tt
    )
  
  TreeD : Set → Set → Desc
  TreeD A B = Sum TreeE (TreeC A B)
  
  `Tree : Set → Set → Set
  `Tree A B = μ (TreeD A B)
  
  `leaf₁ : {A B : Set} → A → `Tree A B
  `leaf₁ a = init (leaf₁T , a , tt)

  `leaf₂ : {A B : Set} → B → `Tree A B
  `leaf₂ b = init (leaf₂T , b , tt)
  
  `node : {A B : Set} → `Tree A B → `Tree A B → `Tree A B
  `node t₁ t₂ = init (nodeT , t₁ , t₂ , tt)

  MapTreeConvoy : (A B X Y : Set) → TreeT → Set
  MapTreeConvoy A B X Y t =
    Recs (TreeC A B t) (`Tree A B) (`Tree X Y) → `Tree X Y

  leaf₁Branch : {A X : Set} (B Y : Set) (f : A → X) → MapTreeConvoy A B X Y leaf₁T
  leaf₁Branch _ _ f a-u = `leaf₁ (f (proj₁ a-u))

  leaf₂Branch : {B Y : Set} (A X : Set) (g : B → Y) → MapTreeConvoy A B X Y leaf₂T
  leaf₂Branch _ _ g b-u = `leaf₂ (g (proj₁ b-u))

  nodeBranch : {A B X Y : Set} → MapTreeConvoy A B X Y nodeT
  nodeBranch t₁-rec₁-t₂-rec₂-u =
    let rec₁ = proj₂ (proj₁ t₁-rec₁-t₂-rec₂-u)
        rec₂ = proj₂ (proj₁ (proj₂ t₁-rec₁-t₂-rec₂-u))
    in `node rec₁ rec₂

  mapTreeα : (A B X Y : Set)
    (f : A → X) (g : B → Y)
    → Recs (TreeD A B) (`Tree A B) (`Tree X Y) → `Tree X Y
  mapTreeα A B X Y f g xs = case (MapTreeConvoy A B X Y)
    (leaf₁Branch B Y f , leaf₂Branch A X g , nodeBranch , tt)
    (proj₁ xs)
    (proj₂ xs)

  `mapTree : {A B X Y : Set}
    (f : A → X) (g : B → Y) → `Tree A B → `Tree X Y
  `mapTree {A} {B} {X} {Y} f g =
    cata (TreeD A B) (`Tree X Y) (mapTreeα A B X Y f g)

----------------------------------------------------------------------

  ListC : Set → Tag ListE → Desc
  ListC A = caseD (
      End
    , Arg A (Rec End)
    , tt
    )

  ListD : Set → Desc
  ListD A = Sum ListE (ListC A)

  `List : Set → Set
  `List A = μ (ListD A)

  `nil : {A : Set} → `List A
  `nil = init (nilT , tt)

  `cons : {A : Set} → A → `List A → `List A
  `cons x xs = init (consT , x , xs , tt)

  postulate append : {A : Set} (xs ys : `List A) → `List A

  ConcatConvoy : Set → ListT → Set
  ConcatConvoy A t = Recs (ListC X t) (`List X) X → X
    where X = `List A

  nilBranch : {A : Set} → ConcatConvoy A nilT
  nilBranch u = `nil

  consBranch : {A : Set} → ConcatConvoy A consT
  consBranch xs-xss-rec-u =
    let u  = proj₂ (proj₂ xs-xss-rec-u)
        xs = proj₁ xs-xss-rec-u
        xss = proj₁ (proj₁ (proj₂ xs-xss-rec-u))
        rec = proj₂ (proj₁ (proj₂ xs-xss-rec-u))
    in  append xs rec

  concatα : (A : Set) → let X = `List A
    in Recs (ListD X) (`List X) X → X
  concatα A xss = case (ConcatConvoy A)
    (nilBranch , consBranch , tt)
    (proj₁ xss)
    (proj₂ xss)

  `concat : {A : Set} → `List (`List A) → `List A
  `concat {A} = cata (ListD (`List A)) (`List A) (concatα A)

----------------------------------------------------------------------

module Generic where

  ℕR : Data
  ℕR = record
    { P = zero
    ; E = ℕE
    ; B = λ u →
        End
      , Rec End
      , tt
    }
  
  `ℕ : Set
  `ℕ = Form ℕR
  
  `zero : `ℕ
  `zero = inj ℕR zeroT
  
  `suc : `ℕ → `ℕ
  `suc = inj ℕR sucT
  
  ListR : Data
  ListR = record
    { P = one
    ; E = ListE
    ; B = λ A-u →
        End
      , Arg (proj₁ A-u) (Rec (End))
      , tt
    }
  
  `List : (A : Set) → Set
  `List = Form ListR
  
  `nil : {A : Set} → `List A
  `nil = inj ListR nilT
  
  `cons : {A : Set} (x : A) (xs : `List A) → `List A
  `cons = inj ListR consT
  
  TreeR : Data
  TreeR = record
    { P = 2
    ; E = TreeE
    ; B = λ A-B-u →
        Arg (proj₁ A-B-u) End
      , Arg (proj₁ (proj₂ A-B-u)) End
      , Rec (Rec End)
      , tt
    }
  
  `Tree : (A B : Set) → Set
  `Tree = Form TreeR
  
  `leaf₁ : {A B : Set} → A → `Tree A B
  `leaf₁ = inj TreeR leaf₁T
  
  `leaf₂ : {A B : Set} → B → `Tree A B
  `leaf₂ = inj TreeR leaf₂T
  
  `node : {A B : Set} → `Tree A B → `Tree A B → `Tree A B
  `node = inj TreeR nodeT
  
  ----------------------------------------------------------------------
  
  `add : `ℕ → `ℕ → `ℕ
  `add = fold ℕR
    (λ n → n)
    (λ m rec n → `suc (rec n))
  
  `mult : `ℕ → `ℕ → `ℕ
  `mult = fold ℕR
    (λ n → `zero)
    (λ m rec n → `add n (rec n))
  
  `append : {A : Set} (xs ys : `List A) → `List A
  `append = fold ListR
    (λ ys → ys)
    (λ x xs rec ys → `cons x (rec ys))
  
  `consBranch : {A : Set} (xs : `List A) (xss : `List (`List A)) → `List A → `List A
  `consBranch = λ xs xss rec → `append xs rec

  `concat : {A : Set} (xss : `List (`List A)) → `List A
  `concat = fold ListR
    `nil
    `consBranch

  `ConsBranch-naive : Set
  `ConsBranch-naive = (A-u : Set × ⊤)
    → let A = proj₁ A-u in
    (xs-xss-rec-u : `List A × (`List (`List A) × `List A) × ⊤) → `List A

  `mapTree : {A B X Y : Set} (f : A → X) (g : B → Y) → `Tree A B → `Tree X Y
  `mapTree f g = fold TreeR
    (λ a → `leaf₁ (f a))
    (λ b → `leaf₂ (g b))
    (λ t₁ rec₁ t₂ rec₂ → `node rec₁ rec₂)


----------------------------------------------------------------------
