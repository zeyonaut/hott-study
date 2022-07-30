{-# OPTIONS --without-K --exact-split --safe #-}

module SS2022.WS1 where

open import SS2022.Prelude

private variable i j k : Level

-- Q3

flip : {A : Type i} {B : Type j} → (A × B) → (B × A)
flip (b , e) = e , b

-- Q5

swap : {A : Type i} {B : Type j} {F : A → B → Type k}
     → ((a : A) → (b : B) → (F a b)) → ((b : B) → (a : A) → (F a b))
swap f b a = f a b