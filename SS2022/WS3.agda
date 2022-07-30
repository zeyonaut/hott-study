{-# OPTIONS --without-K --exact-split --safe #-}

module SS2022.WS3 where

open import SS2022.Prelude

private variable i j k : Level

-- Q1

dist : {A : Type i} {x y z : A} (p : x ≡ y) (q : y ≡ z) → ! (p ∙ q) ≡ (! q) ∙ (! p)
dist (ref _) (ref _) = ref _

-- Q3

prod-obs : {A : Type i} {B : Type j} {a a' : A} {b b' : B} → (a ≡ a') × (b ≡ b') → (a , b) ≡ (a' , b')
prod-obs (ref a , ref b) = ref _

-- Q4

loop-thing : {A : Type i} (a : A) (z : Σ \(x : A) → a ≡ x) → (a , ref a) ≡ z
loop-thing a (a , ref a) = ref _