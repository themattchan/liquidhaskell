{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--eliminate"       @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts      #-}

module MonadList where

import Proves
import Helper
import Prelude hiding (return)


import Append
import ListDef

-- | Monad Laws :
-- | Left identity:	  return a >>= f  ≡ f a
-- | Right identity:	m >>= return    ≡ m
-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

-- | Left Identity

{-@ left_identity :: x:a -> f:(a -> L b) -> {v:Proof | bind (return x) f == f x } @-}
left_identity :: a -> (a -> L b) -> Proof
left_identity x f
  = toProof $
      bind (return x) f
        ==! bind (C x N) f
        ==! append (f x) (bind N f)
        ==! append (f x) N
        ==! f x                      ? prop_append_neutral (f x)


-- | Right Identity

{-@ right_identity :: x:L a -> {v:Proof | bind x return == x } @-}
right_identity :: L a -> Proof
right_identity N
  = toProof $
      bind N return
        ==! N

right_identity (C x xs)
  = toProof $
      bind (C x xs) return
        ==! append (return x) (bind xs return)
        ==! append (C x N)    (bind xs return)
        ==! C x (append N (bind xs return))
        ==! C x (bind xs return)
        ==! C x xs                              ? right_identity xs


-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)
{-@ associativity :: m:L a -> f: (a -> L b) -> g:(b -> L c)
  -> {v:Proof | bind (bind m f) g == bind m (\x:a -> (bind (f x) g))} @-}
associativity :: L a -> (a -> L b) -> (b -> L c) -> Proof
associativity N f g
  = toProof $
      bind (bind N f) g
        ==! bind N g
        ==! N
        ==! bind N (\x -> (bind (f x) g))
associativity (C x xs) f g
  = toProof $
      bind (bind (C x xs) f) g
          ==! bind (append (f x) (bind xs f)) g
          ==! bind (append (f x) (bind xs f)) g                    ? bind_append (f x) (bind xs f) g
          ==! append (bind (f x) g) (bind (bind xs f) g)
          ==! append (bind (f x) g) (bind xs (\y -> bind (f y) g)) ? associativity xs f g
          ==! append ((\y -> bind (f y) g) x) (bind xs (\y -> bind (f y) g))
          ==! bind (C x xs) (\y -> bind (f y) g)

bind_append :: L a -> L a -> (a -> L b) -> Proof
{-@ bind_append :: xs:L a -> ys:L a -> f:(a -> L b)
     -> {v:Proof | bind (append xs ys) f == append (bind xs f) (bind ys f) }
  @-}

bind_append N ys f
  = toProof $
      bind (append N ys) f
         ==! bind ys f
         ==! append N (bind ys f)
         ==! append (bind N f) (bind ys f)
bind_append (C x xs) ys f
  = toProof $
      bind (append (C x xs) ys) f
        ==! bind (C x (append xs ys)) f
        ==! append (f x) (bind (append xs ys) f)
        ==! append (f x) (append (bind xs f) (bind ys f)) ? bind_append xs ys f
        ==! append (append (f x) (bind xs f)) (bind ys f) ? prop_assoc (f x) (bind xs f) (bind ys f)
        ==! append (bind (C x xs) f) (bind ys f)
