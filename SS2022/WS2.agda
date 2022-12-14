{-# OPTIONS --without-K --exact-split --safe #-}

module SS2022.WS2 where

open import SS2022.Prelude

private variable i j k : Level

-- Q3

lt : β β β β π
lt nil nil = π
lt nil (suc y) = π
lt (suc x) y = π

-- Q4

choice : {A : Type i} {B : Type j} {F : A β B β Type k}
       β (Ξ£ \(b : B) β (a : A) β F a b) β ((a : A) β Ξ£ \(b : B) β F a b)
choice (b , e) a = b , e a

-- Q5

tautβ : Β¬ (Β¬ π)
tautβ f = f β

tautβ : {P : Type i} β Β¬ (P Γ (Β¬ P))
tautβ (b , e) = e b

tautβ : {P : Type i} β Β¬ (P β (Β¬ P))
tautβ (b , e) = b (e (\ p β b p p)) (e (\ p β b p p))