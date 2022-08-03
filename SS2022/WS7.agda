{-# OPTIONS --without-K --exact-split --safe #-}

module SS2022.WS7 where

open import SS2022.Prelude

private variable i j k ℓ : Level


{- Q1 -}

-- A map is an embedding precisely if its action on paths is an equivalence.

is-embed : {D : Type i} {C : Type j} (f : D → C) → Type (lmax i j)
is-embed {D = D} f = (x y : D) → is-equiv (ap f {x = x} {y = y})

-- Any embedding is injective.

embed→inj : {A : Type i} {B : Type j} {f : A → B} → is-embed f → inj f
embed→inj {f = f} ef {x} {y} = (πb ▹ πb) (ef x y)

embed→rcancel : {A : Type i} {B : Type j} {f : A → B} → is-embed f → {C : Type k} {g h : C → A} → g ▹ f ∼ h ▹ f → g ∼ h
embed→rcancel {f = f} ef {g = g} {h = h} p x  = embed→inj ef (p x)

-- If a composition of embeddings is an equivalence, then each embedding is an equivalence.

q1 : {A : Type i} {B : Type j} {C : Type k} (f : A → B) (g : B → C) → is-embed f → is-embed g → is-equiv (f ▹ g) → (is-equiv f) × (is-equiv g)
πb (πb (q1 f g ef eg ((s , ps) , (r , pr)))) = g ▹ s , embed→rcancel eg (g ▹∼ ps)
πf (πb (q1 f g ef eg ((s , ps) , (r , pr)))) = g ▹ r , pr
πb (πf (q1 f g ef eg ((s , ps) , (r , pr)))) = s ▹ f , ps
πf (πf (q1 f g ef eg ((s , ps) , (r , pr)))) = r ▹ f , (\ x → ap f ((!∼ (ps ∼▹ r) ∙∼ (s ▹∼ pr)) (g x))) ∙∼ embed→rcancel eg (g ▹∼ ps)

{- Q2 -}

-- Any independent explosion is an embedding.

boom-is-embed : {A : Type i} → is-embed (𝟘-elim' A)
boom-is-embed x = 𝟘-elim' _  x

-- Coproduct inclusions are embeddings.

il-is-embed : {L : Type i} {R : Type j} → is-embed (il {L = L} {R = R})
πb (πb (il-is-embed x x)) (ref (il x)) = ref x
πf (πb (il-is-embed x x)) (ref (il x)) = ref (ref (il x))
πb (πf (il-is-embed x x)) (ref (il x)) = ref x
πf (πf (il-is-embed x x)) (ref x) = ref (ref x)

ir-is-embed : {L : Type i} {R : Type j} → is-embed (ir {L = L} {R = R})
πb (πb (ir-is-embed x x)) (ref (ir x)) = ref x
πf (πb (ir-is-embed x x)) (ref (ir x)) = ref (ref (ir x))
πb (πf (ir-is-embed x x)) (ref (ir x)) = ref x
πf (πf (ir-is-embed x x)) (ref x) = ref (ref x)

-- We define an observational equality for coproducts.

data Lift {ℓ} (T : Type i) : Type (lmax ℓ i) where
  lift : T → Lift T

lower : {T : Type i} → Lift {ℓ = ℓ} T → T
lower (lift t) = t

_≡₊_ : {L : Type i} {R : Type j} → L + R → L + R → Type (lmax i j)
_≡₊_ {i = i} {j = j} (il a) (il b) = Lift {ℓ = lmax i j} (a ≡ b)
il a ≡₊ ir b = Lift 𝟘
ir a ≡₊ il b = Lift 𝟘
_≡₊_ {i = i} {j = j} (ir a) (ir b) = Lift {ℓ = lmax i j} (a ≡ b)

≡₊→≡ : {L : Type i} {R : Type j} {x y : L + R} → x ≡₊ y → x ≡ y
≡₊→≡ {x = il x} {y = il x} (lift (ref x)) = ref (il x)
≡₊→≡ {x = il x} {y = ir y} (lift ⊥) = 𝟘-elim _ ⊥
≡₊→≡ {x = ir x} {y = il y} (lift ⊥) = 𝟘-elim _ ⊥
≡₊→≡ {x = ir x} {y = ir x} (lift (ref x)) = ref (ir x)

≡→≡₊ : {L : Type i} {R : Type j} {x y : L + R} → x ≡ y → x ≡₊ y
≡→≡₊ (ref (il x)) = lift (ref x)
≡→≡₊ (ref (ir x)) = lift (ref x)

-- Case splitting.

+-elim' : {L : Type i} {R : Type j} {T : Type k} → (L → T) → (R → T) → (L + R) → T 
+-elim' fl fr (il l) = fl l
+-elim' fl fr (ir r) = fr r

-- il {R = R} is an equivalence precisely iff R ≃ 𝟘.

il-stmt : {L : Type i} {R : Type j} → (is-equiv (il {L = L} {R = R})) ↔ (R ≃ 𝟘) 
πb il-stmt eq with equiv→qinv eq
... | sr , ps , pr = (\ b → (≡→≡₊ ▹ lower) (ps (ir b))) ,
                     (𝟘-elim' _ , 𝟘-elim _) ,
                     (𝟘-elim' _ , (\ x → 𝟘-elim' _ ((≡→≡₊ ▹ lower) (ps (ir x)))))
πf il-stmt (R→𝟘 , eq) with equiv→qinv eq
... | sr , ps , pr = (+-elim' id (R→𝟘 ▹ (𝟘-elim' _)) , \{(il x) → ref (il x) ; (ir x) → 𝟘-elim' _ (R→𝟘 x)}) ,
                     (+-elim' id (R→𝟘 ▹ (𝟘-elim' _)) , ref)

-- If L and R are contractible, then L + R is not contractible.

q2-3 : {L : Type i} {R : Type j} → is-contr L → is-contr R → ¬ (is-contr (L + R))
q2-3 cl cr cc with cl | cr | cc
... | _ | center-r , _ | il _ , contr-c
  = lower (≡→≡₊ (contr-c (ir center-r)))
... | center-l , _ | _ | ir _ , contr-c
  = lower (≡→≡₊ (contr-c (il center-l)))

{- Q3 -}

-- Homotopies induce equivalences of path spaces.

∼→[≡≃≡] : {S : Type i} {T : Type j} {f g : S → T} (H : f ∼ g) (x y : S) → (f x ≡ f y) ≃ (g x ≡ g y)
∼→[≡≃≡] {f = f} {g = g} H x y =
  (\ p → ! (H x) ∙ p ∙ H y) ,
  qinv→equiv ((\ p → (H x) ∙ p ∙ ! (H y)) , (ps , pr)) where
    -- Warning: boring path algebra ahead.
    ps : (q : g x ≡ g y) → ! (H x) ∙ (H x ∙ q ∙ ! (H y)) ∙ H y ≡ q
    ps q = ap (\z → ! (H x) ∙ z ∙ H y) ((∙-assoc (H x) q (! (H y)))) ∙
           ap (\z → ! (H x) ∙ z) (! (∙-assoc (H x ∙ q) (! (H y)) (H y))) ∙
           ap (\z → ! (H x) ∙ (H x ∙ q) ∙ z) (!-linv (H y)) ∙
           ap (\z → ! (H x) ∙ z) (∙-runit (H x ∙ q)) ∙
           ∙-assoc (! (H x)) (H x) q ∙
           ap (\z → z ∙ q) (!-linv (H x)) ∙
           ∙-lunit q
    pr : (q : f x ≡ f y) → H x ∙ (! (H x) ∙ q ∙ H y) ∙ ! (H y) ≡ q
    pr q = ap (\z → H x ∙ z ∙ ! (H y)) ((∙-assoc (! (H x)) q (H y))) ∙
           ap (\z → H x ∙ z) (! (∙-assoc (! (H x) ∙ q) (H y) (! (H y)))) ∙
           ap (\z → H x ∙ (! (H x) ∙ q) ∙ z) (!-rinv (H y)) ∙
           ap (\z → H x ∙ z) (∙-runit (! (H x) ∙ q)) ∙
           ∙-assoc (H x) (! (H x)) q ∙
           ap (\z → z ∙ q) (!-rinv (H x)) ∙
           ∙-lunit q

-- Homotopy path type equivalences form a certain commutative triangle.

∼-equiv-com : {S : Type i} {T : Type j} {f g : S → T} (H : f ∼ g) {x y : S} → ((ap f) ▹ (πb (∼→[≡≃≡] H x y))) ∼ (ap g)
∼-equiv-com {f = f} {g = g} H (ref x) = ap (! (H x)  ∙_) (∙-lunit (H x)) ∙ !-linv (H x)

-- Homotopies transport equivalence.

∼-tr-equiv : {S : Type i} {T : Type j} {f g : S → T} → f ∼ g → is-equiv f → is-equiv g
∼-tr-equiv {f = f} {g = g} H ef with equiv→qinv ef
... | (!f , psf , prf) = qinv→equiv (!f , (!f ▹∼ !∼ H) ∙∼ psf , (!∼ H ∼▹ !f) ∙∼ prf)

-- Equivalences satisfy 2/3.

equiv-2/3-l : {A : Type i} {B : Type j} {C : Type k} {f : A → B} {g : B → C} → is-equiv g → is-equiv (f ▹ g) → is-equiv f
equiv-2/3-l {f = f} {g = g} eg efg with equiv→qinv eg | equiv→qinv efg
... | C→B , scb , rcb | C→A , sca , rca =
  qinv→equiv (
    g ▹ C→A ,
    (g ▹∼ (((C→A ▹ f) ▹∼ !∼ rcb) ∙∼ (sca ∼▹ C→B))) ∙∼ rcb ,
    rca
  )

equiv-2/3-c : {A : Type i} {B : Type j} {C : Type k} {f : A → B} {g : B → C}
            → is-equiv f → is-equiv g → is-equiv (f ▹ g)
equiv-2/3-c {f = f} {g = g} ef eg with equiv→qinv ef | equiv→qinv eg
... | !f , sf , rf | !g , sg , rg
  = qinv→equiv (!g ▹ !f , (!g ▹∼ sf ∼▹ g) ∙∼ sg , (f ▹∼ rg ∼▹ !f) ∙∼ rf)

equiv-2/3-r : {A : Type i} {B : Type j} {C : Type k} {f : A → B} {g : B → C}
  → is-equiv f → is-equiv (f ▹ g) → is-equiv g
equiv-2/3-r {f = f} {g = g} ef efg with equiv→qinv ef | equiv→qinv efg
... | !f , sf , rf | !fg , sfg , rfg
  = qinv→equiv (!fg ▹ f , sfg , (!∼ sf ∼▹ (g ▹ !fg ▹ f)) ∙∼ (!f ▹∼ rfg ∼▹ f) ∙∼ sf)

-- Naturality squares of homotopies.

ap-∼ : {S : Type i} {T : Type j} {f g : S → T} → (H : f ∼ g) → {x y : S} (p : x ≡ y) → ap f p ≡ H x ∙ ap g p ∙ ! (H y)
ap-∼ {f = f} {g = g} H (ref x) = ! (!-rinv (H x)) ∙ ! (ap ((H x) ∙_) (∙-lunit (! (H x))))

-- Equivalences are embeddings.

equiv→embed : {A : Type i} {B : Type j} {f : A → B} → is-equiv f → is-embed f
equiv→embed {A = A} {B = B} {f = f} ef with equiv→qinv ef
... | !f , sf , rf = \ x → \ y → qinv→equiv ((\ p → ! (rf x) ∙ ap !f p ∙ (rf y)) , apf-s , apf-r) where
  -- It didn't have to be this way...
  apf-s : ∀ {x y} (p : f x ≡ f y) → ap f (! (rf x) ∙ ap !f p ∙ rf y) ≡ p
  apf-s {x = x} {y = y} p =
    ! (∙-runit (ap f (! (rf x) ∙ ap !f p ∙ rf y))) ∙
    ap (\z → ap f (! (rf x) ∙ ap !f p ∙ rf y) ∙ z) (! (!-linv (sf (f y)))) ∙
    ∙-assoc (ap f (! (rf x) ∙ ap !f p ∙ rf y)) (! (sf (f y))) (sf (f y)) ∙
    ! (∙-lunit _) ∙
    ap (\z → z ∙ (ap f (! (rf x) ∙ ap !f p ∙ rf y) ∙ ! (sf (f y))) ∙ sf (f y)) (! (!-linv (sf (f x)))) ∙
    ! (∙-assoc (! (sf (f x))) (sf (f x)) ((ap f (! (rf x) ∙ ap !f p ∙ rf y) ∙ ! (sf (f y))) ∙ sf (f y))) ∙
    ap (\z → ! (sf (f x)) ∙ z) (∙-assoc (sf (f x)) (ap f (! (rf x) ∙ ap !f p ∙ rf y) ∙ ! (sf (f y))) (sf (f y))) ∙
    ap (\z → ! (sf (f x)) ∙ z ∙ (sf (f y))) (! (ap-∼ (f ▹∼ sf) (! (rf x) ∙ ap !f p ∙ rf y))) ∙
    ap (\z → ! (sf (f x)) ∙ z ∙ (sf (f y))) (ap-▹ (f ▹ !f) f (! (rf x) ∙ ap !f p ∙ rf y)) ∙
    ap (\z → ! (sf (f x)) ∙ ap f z ∙ (sf (f y))) (ap-∼ rf (! (rf x) ∙ ap !f p ∙ rf y)) ∙
    ap (\z → ! (sf (f x)) ∙ ap f (rf x ∙ z  ∙ ! (rf y)) ∙ sf (f y)) (ap-id {S = A} {T = B} (! (rf x) ∙ ap !f p ∙ rf y)) ∙
    ap (\z → ! (sf (f x)) ∙ ap f (rf x ∙ z) ∙ sf (f y)) (! (∙-assoc (! (rf x)) (ap !f p ∙ rf y) (! (rf y)))) ∙
    ap (\z → ! (sf (f x)) ∙ ap f (rf x ∙ ! (rf x) ∙ z) ∙ sf (f y)) (! (∙-assoc (ap !f p) (rf y) (! (rf y)))) ∙
    ap (\z →  ! (sf (f x)) ∙  ap f (rf x ∙ ! (rf x) ∙ ap !f p ∙ z) ∙ sf (f y)) (!-rinv (rf y)) ∙
    ap (\z → ! (sf (f x)) ∙  ap f (rf x ∙ ! (rf x) ∙ z) ∙ sf (f y)) (∙-runit (ap !f p)) ∙
    ap (\z → ! (sf (f x)) ∙ ap f z ∙ sf (f y)) (∙-assoc (rf x) (! (rf x)) (ap !f p)) ∙
    ap (\z → ! (sf (f x)) ∙ ap f (z ∙ ap !f p) ∙ sf (f y)) (!-rinv (rf x)) ∙
    ap (\z → ! (sf (f x)) ∙ ap f z ∙ sf (f y)) (∙-lunit (ap !f p)) ∙
    ap (\z → ! (sf (f x)) ∙ z ∙ sf (f y)) (! (ap-▹ !f f p)) ∙
    ap (\z → ! (sf (f x)) ∙ ap (!f ▹ f) p ∙ z) (! (!-invo (sf (f y)))) ∙
    ! (ap-∼ (!∼ sf) p) ∙
    ap-id {S = B} {T = A} p
  -- Yes. It did.
  apf-r : ∀ {x y} (p : x ≡ y) → ! (rf x) ∙ ap !f (ap f p) ∙ rf y ≡ p
  apf-r (ref x) =
    ap (\z → ! (rf x) ∙ ref (!f (f x)) ∙ z) (! (!-invo (rf x))) ∙
    ! (ap-∼ (!∼ rf) (ref (x)))

-- Suppose we have the following commutative triangle:

module com₀ {A : Type i} {B : Type j} {X : Type k} (f : A → X) (g : B → X) (h : A → B) (H : f ∼ h ▹ g) where

  -- If g is an embedding, then f is an embedding when h is an embedding.

  q3-1 : is-embed g → (is-embed f) ↔ (is-embed h)
  πb (q3-1 eg) ef x y = aph-is-equiv where
    apf-is-equiv = ef x y
    H-is-equiv = πf (∼→[≡≃≡] H x y)
    [apf▹H]-is-equiv = equiv-2/3-c apf-is-equiv H-is-equiv
    [apf▹H]∼[aph▹apg] = (∼-equiv-com H {x = x} {y = y}) ∙∼ (ap-▹ h g {x = x} {y = y})
    [aph▹apg]-is-equiv = ∼-tr-equiv [apf▹H]∼[aph▹apg] [apf▹H]-is-equiv
    apg-is-equiv = eg (h x) (h y)
    aph-is-equiv = equiv-2/3-l apg-is-equiv [aph▹apg]-is-equiv
  πf (q3-1 eg) eh x y = apf-is-equiv where
    aph-is-equiv = eh x y
    apg-is-equiv = eg (h x) (h y)
    [aph▹apg]-is-equiv = equiv-2/3-c aph-is-equiv apg-is-equiv
    [aph▹apg]∼[apf▹H] = !∼ (ap-▹ h g {x = x} {y = y}) ∙∼ !∼ (∼-equiv-com H {x = x} {y = y}) 
    [apf▹H]-is-equiv = ∼-tr-equiv [aph▹apg]∼[apf▹H] [aph▹apg]-is-equiv
    H-is-equiv = πf (∼→[≡≃≡] H x y)
    apf-is-equiv = equiv-2/3-l H-is-equiv [apf▹H]-is-equiv

-- We reuse the same commutative triangle.

module com₁ {A : Type i} {B : Type j} {X : Type k} (f : A → X) (g : B → X) (h : A → B) (H : f ∼ h ▹ g) where

  -- If h is an equivalence, then f is an embedding when g is an embedding.

  q3-2 : is-equiv h → (is-embed f) ↔ (is-embed g)
  πb (q3-2 vh) ef = g-is-embed where
    !h = πb (!≃ (h , vh))
    !h-is-equiv = πf (!≃ (h , vh))
    !h-is-embed = equiv→embed !h-is-equiv
    [g]∼[!h▹h▹g] = !∼ (πf (πf !h-is-equiv)) ∼▹ g
    [h▹g]-is-embed : is-embed (h ▹ g)
    [h▹g]-is-embed x y = ap[h▹g]-is-equiv where
       apf-is-equiv = ef x y
       H-is-equiv = πf (∼→[≡≃≡] H x y)
       [apf▹H]-is-equiv = equiv-2/3-c apf-is-equiv H-is-equiv
       [apf▹H]∼ap[h▹g] = (∼-equiv-com H {x = x} {y = y})
       ap[h▹g]-is-equiv = ∼-tr-equiv [apf▹H]∼ap[h▹g] [apf▹H]-is-equiv
    g-is-embed = πf (com₀.q3-1 g (h ▹ g) !h [g]∼[!h▹h▹g] [h▹g]-is-embed) !h-is-embed
  πf (q3-2 vh) eg x y = apf-is-equiv where
    h-is-embed = equiv→embed vh
    aph-is-equiv = h-is-embed x y
    apg-is-equiv = eg (h x) (h y)
    [aph▹apg]-is-equiv = equiv-2/3-c aph-is-equiv apg-is-equiv
    [aph▹apg]∼[apf▹H] = !∼ (ap-▹ h g {x = x} {y = y}) ∙∼ !∼ (∼-equiv-com H {x = x} {y = y})
    [apf▹H]-is-equiv = ∼-tr-equiv [aph▹apg]∼[apf▹H] [aph▹apg]-is-equiv
    H-is-equiv = πf (∼→[≡≃≡] H x y)
    apf-is-equiv = equiv-2/3-l H-is-equiv [apf▹H]-is-equiv

{- Q4 TODO -}

q4 : {A : Type i} {B : Type j} {C : Type k} (f : A → C) (g : B → C)
   → (is-embed (+-elim' f g)) ↔ (((is-embed f) × (is-embed g)) × ((a : A) (b : B) → ¬ (f a ≡ g b)))
q4 = {!!}

{- Q5 TODO -}

-- For any family of maps, we have its totalization:

tot : {A : Type i} {B : A → Type j} {C : A → Type k}
     → ((a : A) → B a → C a)
     → Σ B → Σ C
tot f (a , b) = a , f a b

q5-1 : {A : Type i} {B : A → Type j} {C : A → Type k}
     → (f g : (a : A) → B a → C a)
     → ((a : A) → (f a) ∼ (g a)) → tot f ∼ tot g
q5-1 = {!!}

q5-2 : {A : Type i} {B : A → Type j} {C : A → Type k} {D : A → Type ℓ}
     → (f : (a : A) → B a → C a) (g : (a : A) → C a → D a)
     → tot (\a → f a ▹ g a) ∼ tot f ▹ tot g
q5-2 = {!!}

q5-3 : {A : Type i} {B : A → Type j}
     → tot (\a → id {T = B a}) ∼ id {T = Σ B}
q5-3 = {!!}

-- q5-4 : TODO

-- q5-5 : TODO

{- Q6 TODO -}

-- A map is path-split precisely if it has a section and its path action (for all choices of endpoints) has a section.

is-path-split : {A : Type i} {B : Type j} (f : A → B) → Type (lmax i j)
is-path-split {A = A} f = (sect f) × (∀ x y → sect (ap f {x = x} {y = y}))

q6 : {A : Type i} {B : Type j} (f : A → B) → (is-equiv f) ↔ (is-path-split f)
q6 = {!!}              
