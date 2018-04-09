{-# OPTIONS --allow-unsolved-metas #-}

open import CS410-Prelude


------------------------------------------------------------------------------
-- Vectors
------------------------------------------------------------------------------

data Vec (X : Set) : Nat -> Set where
  []   :                              Vec X zero
  _,-_ : {n : Nat} -> X -> Vec X n -> Vec X (suc n)

infixr 4 _,-_


------------------------------------------------------------------------------
-- Heads and Tails
------------------------------------------------------------------------------

vHead : {X : Set}{n : Nat} -> Vec X (suc n) -> X
vHead (x ,- xs) = x

vTail : {X : Set}{n : Nat} -> Vec X (suc n) -> Vec X n
vTail (x ,- xs) = xs

vHeadTailFact : {X : Set}{n : Nat}(xs : Vec X (suc n)) -> (vHead xs ,- vTail xs) == xs
vHeadTailFact (x ,- xs) = refl (x ,- xs)


------------------------------------------------------------------------------
-- Concatenation and its Inverse
------------------------------------------------------------------------------

_+V_ : {X : Set}{m n : Nat} -> Vec X m -> Vec X n -> Vec X (m +N n)
[] +V ys        = ys
(x ,- xs) +V ys = x ,- xs +V ys

infixr 4 _+V_

vChop : {X : Set}(m : Nat){n : Nat} -> Vec X (m +N n) -> Vec X m * Vec X n
vChop zero xs = [] , xs
vChop (suc m) (x ,- xs) with vChop m xs
vChop (suc m) (x ,- xs) | xf , xb = (x ,- xf) , xb

vChopAppendFact : {X : Set}{m n : Nat}(xs : Vec X m)(ys : Vec X n) -> vChop m (xs +V ys) == (xs , ys)
vChopAppendFact [] ys = refl ([] , ys)
vChopAppendFact (x ,- xs) ys rewrite vChopAppendFact xs ys = refl ((x ,- xs) , ys)


------------------------------------------------------------------------------
-- Map, take I
------------------------------------------------------------------------------

-- Implement the higher-order function that takes an operation on
-- elements and does it to each element of a vector. Use recursion
-- on the vector.
-- Note that the type tells you the size remains the same.

-- Show that if the elementwise function "does nothing", neither does
-- its vMap. "map of identity is identity"

-- Show that two vMaps in a row can be collapsed to just one, or
-- "composition of maps is map of compositions"

vMap : {X Y : Set} -> (X -> Y) -> {n : Nat} -> Vec X n -> Vec Y n
vMap f []        = []
vMap f (x ,- xs) = f x ,- vMap f xs

vMapIdFact : {X : Set}{f : X -> X}(feq : (x : X) -> f x == x) ->
             {n : Nat}(xs : Vec X n) ->
             vMap f xs == xs
vMapIdFact feq [] = refl []
vMapIdFact feq (x ,- xs) rewrite vMapIdFact feq xs | feq x
  = refl (x ,- xs)

vMapCpFact : {X Y Z : Set}{f : Y -> Z}{g : X -> Y}{h : X -> Z}(heq : (x : X) -> f (g x) == h x) ->
             {n : Nat}(xs : Vec X n) ->
             vMap f (vMap g xs) == vMap h xs
vMapCpFact heq [] = refl []
vMapCpFact {f = f}{g = g}{h = h} heq (x ,- xs) rewrite vMapCpFact {f = f}{g = g}{h = h} heq xs | heq x
  = refl (h x ,- vMap h xs)


------------------------------------------------------------------------------
-- vMap and +V
------------------------------------------------------------------------------

-- Show that if you've got two vectors of Xs and a function from X to Y,
-- and you want to concatenate and map, it doesn't matter which you do
-- first.

vMap+VFact : {X Y : Set}(f : X -> Y) ->
             {m n : Nat}(xs : Vec X m)(xs' : Vec X n) ->
             vMap f (xs +V xs') == (vMap f xs +V vMap f xs')
vMap+VFact f [] xs' = refl (vMap f xs')
vMap+VFact f (x ,- xs) xs' rewrite vMap+VFact f xs xs' = refl (f x ,- vMap f xs +V vMap f xs')


------------------------------------------------------------------------------
-- Applicative Structure (giving mapping and zipping cheaply)
------------------------------------------------------------------------------

-- HINT: you will need to override the default invisibility of n to do this.
vPure : {X : Set} -> X -> {n : Nat} -> Vec X n
vPure x {zero}  = []
vPure x {suc n} =  x ,- vPure x

_$V_ : {X Y : Set}{n : Nat} -> Vec (X -> Y) n -> Vec X n -> Vec Y n
[] $V []           = []
f ,- fs $V x ,- xs =  f x ,- (fs $V xs)

infixl 3 _$V_

-- Pattern matching and recursion are forbidden for the next two tasks.

-- implement vMap again, but as a one-liner
vec : {X Y : Set} -> (X -> Y) -> {n : Nat} -> Vec X n -> Vec Y n
vec f xs = vPure f $V xs

-- implement the operation which pairs up corresponding elements
vZip : {X Y : Set}{n : Nat} -> Vec X n -> Vec Y n -> Vec (X * Y) n
vZip xs ys = vPure _,_ $V xs $V ys


------------------------------------------------------------------------------
-- Applicative Laws
------------------------------------------------------------------------------

-- According to "Applicative programming with effects" by
--   Conor McBride and Ross Paterson
-- some laws should hold for applicative functors.
-- Check that this is the case.

vIdentity : {X : Set}{f : X -> X}(feq : (x : X) -> f x == x) ->
            {n : Nat}(xs : Vec X n) -> (vPure f $V xs) == xs
vIdentity feq [] = refl []
vIdentity feq (x ,- xs) rewrite vIdentity feq xs | feq x = refl (x ,- xs)

vHomomorphism : {X Y : Set}(f : X -> Y)(x : X) -> {n : Nat} ->
                   (vPure f $V vPure x) == vPure (f x) {n}
vHomomorphism f x {zero} = refl []
vHomomorphism f x {suc n} rewrite vHomomorphism f x {n} = refl (f x ,- vPure (f x))

vInterchange : {X Y : Set}{n : Nat}(fs : Vec (X -> Y) n)(x : X) ->
                 (fs $V vPure x) == (vPure (_$ x) $V fs)
vInterchange [] x = refl []
vInterchange (f ,- fs) x rewrite vInterchange fs x = refl (f x ,- (vPure (\ f → f x) $V fs))

vComposition : {X Y Z : Set}{n : Nat}(fs : Vec (Y -> Z) n)(gs : Vec (X -> Y) n)(xs : Vec X n) ->
                  (vPure _<<_ $V fs $V gs $V xs) == (fs $V (gs $V xs))
vComposition [] [] [] = refl []
vComposition (f ,- fs) (g ,- gs) (x ,- xs) rewrite vComposition fs gs xs = refl (f (g x) ,- (fs $V (gs $V xs)))


------------------------------------------------------------------------------
-- Order-Preserving Embeddings (also known in the business as "thinnings")
------------------------------------------------------------------------------

-- What have these to do with Pascal's Triangle?

data _<=_ : Nat -> Nat -> Set where
  oz :                          zero  <= zero
  os : {n m : Nat} -> n <= m -> suc n <= suc m
  o' : {n m : Nat} -> n <= m ->     n <= suc m

-- Find all the values in each of the following <= types.
-- This is a good opportunity to learn to use C-c C-a with the -l option
--   (a.k.a. "google the type" without "I feel lucky")
-- The -s n option also helps.

all0<=4 : Vec (0 <= 4) 1
all0<=4 = o' (o' (o' (o' oz))) ,- []

all1<=4 : Vec (1 <= 4) 4
all1<=4 = o' (o' (o' (os oz))) ,-
          o' (o' (os (o' oz))) ,-
          o' (os (o' (o' oz))) ,-
          os (o' (o' (o' oz))) ,-
          []

all2<=4 : Vec (2 <= 4) 6
all2<=4 =  os (os (o' (o' oz))) ,-
           os (o' (os (o' oz))) ,-
           os (o' (o' (os oz))) ,-
           o' (os (os (o' oz))) ,-
           o' (os (o' (os oz))) ,-
           o' (o' (os (os oz))) ,-
           []

all3<=4 : Vec (3 <= 4) 4
all3<=4 = os (os (os (o' oz))) ,-
          os (os (o' (os oz))) ,-
          os (o' (os (os oz))) ,-
          o' (os (os (os oz))) ,-
          []

all4<=4 : Vec (4 <= 4) 1
all4<=4 = os (os (os (os oz))) ,- []

-- Prove the following. A massive case analysis "rant" is fine.

no5<=4 : 5 <= 4 -> Zero
no5<=4 (os (os (os (os ()))))
no5<=4 (os (os (os (o' ()))))
no5<=4 (os (os (o' (os ()))))
no5<=4 (os (os (o' (o' ()))))
no5<=4 (os (o' (os (os ()))))
no5<=4 (os (o' (os (o' ()))))
no5<=4 (os (o' (o' (os ()))))
no5<=4 (os (o' (o' (o' ()))))
no5<=4 (o' (os (os (os ()))))
no5<=4 (o' (os (os (o' ()))))
no5<=4 (o' (os (o' (os ()))))
no5<=4 (o' (os (o' (o' ()))))
no5<=4 (o' (o' (os (os ()))))
no5<=4 (o' (o' (os (o' ()))))
no5<=4 (o' (o' (o' (os ()))))
no5<=4 (o' (o' (o' (o' ()))))


------------------------------------------------------------------------------
-- Order-Preserving Embeddings Select From Vectors
------------------------------------------------------------------------------

-- Use n <= m to encode the choice of n elements from an m-Vector.
-- The os constructor tells you to take the next element of the vector;
-- the o' constructor tells you to omit the next element of the vector.

_<?=_ : {X : Set}{n m : Nat} -> n <= m -> Vec X m -> Vec X n
oz    <?= [] = []
os th <?= (x ,- xs) =  x ,- th <?= xs
o' th <?= (x ,- xs) =  th <?= xs

-- it shouldn't matter whether you map then select or select then map

vMap<?=Fact : {X Y : Set}(f : X -> Y)
              {n m : Nat}(th : n <= m)(xs : Vec X m) ->
              vMap f (th <?= xs) == (th <?= vMap f xs)
vMap<?=Fact f oz [] = refl []
vMap<?=Fact f (os th) (x ,- xs) rewrite vMap<?=Fact f th xs = refl (f x ,- (th <?= vMap f xs))
vMap<?=Fact f (o' th) (x ,- xs) rewrite vMap<?=Fact f th xs = refl (th <?= vMap f xs)


------------------------------------------------------------------------------
-- Our Favourite Thinnings
------------------------------------------------------------------------------

-- Construct the identity thinning and the empty thinning.

oi : {n : Nat} -> n <= n
oi {zero}  = oz
oi {suc n} = os oi

oe : {n : Nat} -> 0 <= n
oe {zero}  = oz
oe {suc n} = o' oe

-- Show that all empty thinnings are equal to yours.

oeUnique : {n : Nat}(th : 0 <= n) -> th == oe
oeUnique oz     = refl oz
oeUnique (o' i) with oeUnique i
oeUnique (o' .oe) | refl .oe = refl (o' oe)


-- Show that there are no thinnings of form big <= small  (TRICKY)
-- Then show that all the identity thinnings are equal to yours.
-- Note that you can try the second even if you haven't finished the first.
-- HINT: you WILL need to expose the invisible numbers.
-- HINT: check CS410-Prelude for a reminder of >=

oTooBig : {n m : Nat} -> n >= m -> suc n <= m -> Zero
oTooBig {_} {zero} n>=m ()
oTooBig {zero} {suc m} n>=m (th) = n>=m
oTooBig {suc n} {suc m} n>=m (os th) with oTooBig {n} {m} n>=m th
oTooBig {suc n} {suc m} n>=m (os th) | ()
oTooBig {suc n} {suc m} n>=m (o' th) with oTooBig {suc n} {m} (trans->= (suc n) n m (suc->= n) n>=m) th
oTooBig {suc n} {suc m} n>=m (o' th) | ()

oiUnique : {n : Nat}(th : n <= n) -> th == oi
oiUnique oz = refl oz
oiUnique (os th) with oiUnique th
oiUnique (os .oi) | refl .oi = refl (os oi)
oiUnique {n}(o' th) with oTooBig (refl->= n) th
oiUnique {.(suc _)} (o' th) | ()


-- Show that the identity thinning selects the whole vector

id-<?= : {X : Set}{n : Nat}(xs : Vec X n) -> (oi <?= xs) == xs
id-<?= [] = refl []
id-<?= (x ,- xs) rewrite id-<?= xs = refl (x ,- xs)


------------------------------------------------------------------------------
-- Composition of Thinnings
------------------------------------------------------------------------------

-- Define the composition of thinnings and show that selecting by a
-- composite thinning is like selecting then selecting again.
-- A small bonus applies to minimizing the length of the proof.
-- To collect the bonus, you will need to think carefully about
-- how to make the composition as *lazy* as possible.

_o>>_ : {p n m : Nat} -> p <= n -> n <= m -> p <= m
oz o>> th' = th'
os th o>> os th' with th o>> th'
os th o>> os th' | p = os p
os th o>> o' th' with (os th) o>> th'
os th o>> o' th' | p = o' p
o' th o>> os th' with th o>> th'
o' th o>> os th' | p = o' p
o' th o>> o' th' with (o' th) o>> th'
o' th o>> o' th' | p = o' p

cp-<?= : {p n m : Nat}(th : p <= n)(th' : n <= m) ->
         {X : Set}(xs : Vec X m) ->
         ((th o>> th') <?= xs) == (th <?= (th' <?= xs))
cp-<?= oz oz [] = refl []
cp-<?= oz (o' th') xs with o' th' <?= xs
cp-<?= oz (o' th') xs | [] = refl []
cp-<?= (os th) (os th') (x ,- xs) rewrite cp-<?= th th' xs      = refl (x ,- (th <?= (th' <?= xs)))
cp-<?= (os th) (o' th') (x ,- xs) rewrite cp-<?= (os th) th' xs = refl (os th <?= (th' <?= xs))
cp-<?= (o' th) (os th') (x ,- xs) rewrite cp-<?= th th' xs      = refl (th <?= (th' <?= xs))
cp-<?= (o' th) (o' th') (x ,- xs) rewrite cp-<?= (o' th) th' xs = refl (o' th <?= (th' <?= xs))

-- TODO: shorter solution for bonus


------------------------------------------------------------------------------
-- Thinning Dominoes
------------------------------------------------------------------------------

idThen-o>> : {n m : Nat}(th : n <= m) -> (oi o>> th) == th
idThen-o>> oz = refl oz
idThen-o>> (os th) rewrite idThen-o>> th = refl (os th)
idThen-o>> {zero}(o' th) rewrite idThen-o>> th = refl (o' th)
idThen-o>> {suc n}(o' th) rewrite idThen-o>> th = refl (o' th)

idAfter-o>> : {n m : Nat}(th : n <= m) -> (th o>> oi) == th
idAfter-o>> oz = refl oz
idAfter-o>> (os th) rewrite idAfter-o>> th = refl (os th)
idAfter-o>> (o' th) rewrite idAfter-o>> th = refl (o' th)

assoc-o>> : {q p n m : Nat}(th0 : q <= p)(th1 : p <= n)(th2 : n <= m) ->
            ((th0 o>> th1) o>> th2) == (th0 o>> (th1 o>> th2))
assoc-o>> oz th1 th2 = refl (th1 o>> th2)
assoc-o>> (os th0) (os th1) (os th2) rewrite assoc-o>> th0 th1 th2           = refl (os (th0 o>> (th1 o>> th2)))
assoc-o>> (os th0) (os th1) (o' th2) rewrite assoc-o>> (os th0) (os th1) th2 = refl (o' (os th0 o>> (os th1 o>> th2)))
assoc-o>> (os th0) (o' th1) (os th2) rewrite assoc-o>> (os th0) th1 th2      = refl (o' (os th0 o>> (th1 o>> th2)))
assoc-o>> (os th0) (o' th1) (o' th2) rewrite assoc-o>> (os th0) (o' th1) th2 = refl (o' (os th0 o>> (o' th1 o>> th2)))
assoc-o>> (o' th0) (os th1) (os th2) rewrite assoc-o>> th0 th1 th2           = refl (o' (th0 o>> (th1 o>> th2)))
assoc-o>> (o' th0) (os th1) (o' th2) rewrite assoc-o>> (o' th0) (os th1) th2 = refl (o' (o' th0 o>> (os th1 o>> th2)))
assoc-o>> (o' th0) (o' th1) (os th2) rewrite assoc-o>> (o' th0) th1 th2      = refl (o' (o' th0 o>> (th1 o>> th2)))
assoc-o>> (o' th0) (o' th1) (o' th2) rewrite assoc-o>> (o' th0) (o' th1) th2 = refl (o' (o' th0 o>> (o' th1 o>> th2)))


------------------------------------------------------------------------------
-- Vectors as Arrays
------------------------------------------------------------------------------

-- We can use 1 <= n as the type of bounded indices into a vector and do
-- a kind of "array projection". First we select a 1-element vector from
-- the n-element vector, then we take its head to get the element out.

vProject : {n : Nat}{X : Set} -> Vec X n -> 1 <= n -> X
vProject xs i = vHead (i <?= xs)

-- Your (TRICKY) mission is to reverse the process, tabulating a function
-- from indices as a vector. Then show that these operations are inverses.

--??--1.15--------------------------------------------------------------------

-- HINT: composition of functions
vTabulate : {n : Nat}{X : Set} -> (1 <= n -> X) -> Vec X n
vTabulate {n} f = {!!}

-- This should be easy if vTabulate is correct.
vTabulateProjections : {n : Nat}{X : Set}(xs : Vec X n) ->
                       vTabulate (vProject xs) == xs
vTabulateProjections xs = {!!}

-- HINT: oeUnique
vProjectFromTable : {n : Nat}{X : Set}(f : 1 <= n -> X)(i : 1 <= n) ->
                    vProject (vTabulate f) i == f i
vProjectFromTable f i = {!!}

--??--------------------------------------------------------------------------
