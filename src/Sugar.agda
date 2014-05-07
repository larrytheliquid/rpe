{-# OPTIONS --type-in-type #-}
open import Data.Unit
open import Data.Product hiding ( curry ; uncurry )
open import Data.Nat hiding ( fold )
open import Data.List
open import Data.String
open import Relation.Binary.PropositionalEquality
open import Function
module Sugar where

----------------------------------------------------------------------

data Desc : Set where
  End : Desc
  Rec : (D : Desc) → Desc
  Arg : (A : Set) (D : Desc) → Desc
  Sum : (T : Set) (B : T → Desc) → Desc

----------------------------------------------------------------------

El : (D : Desc) → Set → Set
El End X = ⊤
El (Rec D) X = X × El D X
El (Arg A D) X = A × El D X
El (Sum T B) X = Σ T (λ t → El (B t) X)

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

data ℕT : Set where
  zeroT sucT : ℕT

data ListT : Set where
  nilT consT : ListT

data TreeT : Set where
  leaf₁T leaf₂T nodeT : TreeT

----------------------------------------------------------------------

ℕC : ℕT → Desc
ℕC zeroT = End
ℕC sucT = Rec End

ℕD : Desc
ℕD = Sum ℕT ℕC

`ℕ : Set
`ℕ = μ ℕD

`zero : `ℕ
`zero = init (zeroT , tt)

`suc : `ℕ → `ℕ
`suc n = init (sucT , n , tt)

addα : Recs ℕD `ℕ (`ℕ → `ℕ) → `ℕ → `ℕ
addα (zeroT , tt) n = n
addα (sucT , (m , rec) , tt) n = `suc (rec n)

`add : `ℕ → `ℕ → `ℕ
`add = cata ℕD (`ℕ → `ℕ) addα

----------------------------------------------------------------------

ListC : Set → ListT → Desc
ListC A nilT = End
ListC A consT = Arg A (Rec End)

ListD : Set → Desc
ListD A = Sum ListT (ListC A)

`List : Set → Set
`List A = μ (ListD A)

`nil : {A : Set} → `List A
`nil = init (nilT , tt)

`cons : {A : Set} → A → `List A → `List A
`cons x xs = init (consT , x , xs , tt)

postulate `append : {A : Set} (xs ys : `List A) → `List A

concatα : (A : Set) → let X = `List A
  in Recs (ListD X) (`List X) X → X
concatα A (nilT , tt) = `nil
concatα A (consT , xs , (xss , rec) , tt) = `append xs rec

`concat : {A : Set} → `List (`List A) → `List A
`concat {A} = cata (ListD (`List A)) (`List A) (concatα A)

----------------------------------------------------------------------

TreeC : Set → Set → TreeT → Desc
TreeC A B leaf₁T = Arg A End
TreeC A B leaf₂T = Arg B End
TreeC A B nodeT  = Rec (Rec End)

TreeD : Set → Set → Desc
TreeD A B = Sum TreeT (TreeC A B)

`Tree : Set → Set → Set
`Tree A B = μ (TreeD A B)

`leaf₁ : {A B : Set} → A → `Tree A B
`leaf₁ a = init (leaf₁T , a , tt)

`leaf₂ : {A B : Set} → B → `Tree A B
`leaf₂ b = init (leaf₂T , b , tt)

`node : {A B : Set} → `Tree A B → `Tree A B → `Tree A B
`node t₁ t₂ = init (nodeT , t₁ , t₂ , tt)

mapTreeα : (A B X Y : Set)
  (f : A → X) (g : B → Y)
  → Recs (TreeD A B) (`Tree A B) (`Tree X Y) → `Tree X Y
mapTreeα A B X Y f g (leaf₁T , a , tt) = `leaf₁ (f a)
mapTreeα A B X Y f g (leaf₂T , b , tt) = `leaf₂ (g b)
mapTreeα A B X Y f g (nodeT , (t₁ , rec₁) , (t₂ , rec₂) , tt) =
  `node rec₁ rec₂

`mapTree : {A B X Y : Set}
  (f : A → X) (g : B → Y) → `Tree A B → `Tree X Y
`mapTree {A} {B} {X} {Y} f g =
  cata (TreeD A B) (`Tree X Y) (mapTreeα A B X Y f g)

----------------------------------------------------------------------
