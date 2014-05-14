module RPE.Background where

data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

data List (A : Set) : Set where
  nil : List A
  cons : A → List A → List A

data Tree (A B : Set) : Set where
  leaf₁ : A → Tree A B
  leaf₂ : B → Tree A B
  node : Tree A B → Tree A B → Tree A B

foldℕ : {X : Set}
  (czero : X)
  (csuc : ℕ → X → X)
  → ℕ → X
foldℕ czero csuc zero = czero
foldℕ czero csuc (suc n) = csuc n (foldℕ czero csuc n)

foldList : {X A : Set}
  (cnil : X)
  (ccons : A → List A → X → X)
  → List A → X
foldList cnil ccons nil = cnil
foldList cnil ccons (cons x xs) = ccons x xs (foldList cnil ccons xs)

foldTree : {X A B : Set}
  (cleaf₁ : A → X)
  (cleaf₂ : B → X)
  (cnode : Tree A B → X → Tree A B → X → X)
  → Tree A B → X
foldTree cleaf₁ cleaf₂ cnode (leaf₁ a) = cleaf₁ a
foldTree cleaf₁ cleaf₂ cnode (leaf₂ b) = cleaf₂ b
foldTree cleaf₁ cleaf₂ cnode (node t₁ t₂) =
  cnode t₁ (foldTree cleaf₁ cleaf₂ cnode t₁)
        t₂ (foldTree cleaf₁ cleaf₂ cnode t₂)

----------------------------------------------------------------------

Listℕ : Set
Listℕ = List ℕ

one   : ℕ ; one   = suc zero
two   : ℕ ; two   = suc (suc zero)
three : ℕ ; three = suc two

one-two-three : Listℕ
one-two-three =
  cons one (cons two (cons three nil))

add : ℕ → ℕ → ℕ
add = foldℕ
  (λ n → n)
  (λ m rec → λ n → (suc (rec n)))

append : {A : Set} → List A → List A → List A
append = foldList
  (λ ys → ys)
  (λ x xs rec → (λ ys → cons x (rec ys)))

concat : {A : Set} → List (List A) → List A
concat = foldList
  nil
  (λ xs xss rec → append xs rec)

mapTree : {A B X Y : Set} (f : A → X) (g : B → Y) → Tree A B → Tree X Y
mapTree f g = foldTree
  (λ a → leaf₁ (f a))
  (λ b → leaf₂ (g b))
  (λ t₁ rec₁ t₂ rec₂ → node rec₁ rec₂)

Treeℕs : Set
Treeℕs = Tree ℕ (Tree ℕ ℕ)

some-tree : Treeℕs
some-tree = node
  (node (leaf₁ zero) (leaf₁ one))
  (leaf₂ (node (leaf₁ two) (leaf₁ three)))

