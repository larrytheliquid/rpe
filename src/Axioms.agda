open import Relation.Binary.PropositionalEquality
module Axioms where

postulate
  ℕ : Set
  List : Set → Set
  Tree : Set → Set → Set

Listℕ : Set
Listℕ = List ℕ

postulate
  zero : ℕ
  suc : ℕ → ℕ

  nil : {A : Set} → List A
  cons : {A : Set} → A → List A → List A

  leaf₁ : {A B : Set} → A → Tree A B
  leaf₂ : {A B : Set} → B → Tree A B
  branch : {A B : Set} → Tree A B → Tree A B → Tree A B

one : ℕ
one = suc zero

two : ℕ
two = suc one

three : ℕ
three = suc two

postulate
  foldℕ : {X : Set}
    (czero : X)
    (csuc : ℕ → X → X)
    → ℕ → X
  foldℕ-zero : {X : Set} {czero : X} {csuc : ℕ → X → X}
    → foldℕ czero csuc zero ≡ czero
  foldℕ-suc : {X : Set} {czero : X} {csuc : ℕ → X → X} {n : ℕ}
    → foldℕ czero csuc (suc n) ≡ csuc n (foldℕ czero csuc n)
