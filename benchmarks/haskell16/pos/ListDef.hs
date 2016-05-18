{-@ LIQUID "--higherorder"     @-}
{-@ LIQUID "--totality"        @-}
{-@ LIQUID "--exact-data-cons" @-}
{-@ LIQUID "--eliminate"       @-}


{-# LANGUAGE IncoherentInstances   #-}
{-# LANGUAGE FlexibleContexts      #-}

module ListDef where

import Prelude hiding (return, map, concatMap)

import Proves
import Helper


-- | Monad Laws :
-- | Left identity:	  return a >>= f  ≡ f a
-- | Right identity:	m >>= return    ≡ m
-- | Associativity:	  (m >>= f) >>= g ≡	m >>= (\x -> f x >>= g)

{-@ axiomatize return @-}
return :: a -> L a
return x = C x N

{-@ axiomatize bind @-}
bind :: L a -> (a -> L b) -> L b
bind m f
  | llen m > 0 = append (f (hd m)) (bind (tl m) f)
  | otherwise  = N

{-@ axiomatize append @-}
append :: L a -> L a -> L a
append xs ys
  | llen xs == 0 = ys
  | otherwise    = C (hd xs) (append (tl xs) ys)

{-@ axiomatize map @-}
map :: (a -> b) -> L a -> L b
map f xs
  | llen xs == 0 = N
  | otherwise    = C (f (hd xs)) (map f (tl xs))

{-@ axiomatize concatMap @-}
concatMap :: (a -> L b) -> L a -> L b
concatMap f xs
  | llen xs == 0 = N
  | otherwise    = append (f (hd xs)) (concatMap f (tl xs))


{-@ axiomatize concatt @-}
concatt :: L (L a) -> L a
concatt xs
  | llen xs == 0 = N
  | otherwise    = append (hd xs) (concatt (tl xs))

data L a = N | C a (L a)
{-@ data L [llen] @-}

{-@ measure llen @-}
llen :: L a -> Int
{-@ llen :: L a -> Nat @-}
llen N        = 0
llen (C _ xs) = 1 + llen xs

{-@ measure hd @-}
{-@ hd :: {v:L a | llen v > 0 } -> a @-}
hd :: L a -> a
hd (C x _) = x

{-@ measure tl @-}
{-@ tl :: xs:{L a | llen xs > 0 } -> {v:L a | llen v == llen xs - 1 } @-}
tl :: L a -> L a
tl (C _ xs) = xs
