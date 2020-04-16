# Implementation of AEATSD on simple λ-terms

This module implements the tree diffing algorithm presented in [1] on simple λ-terms.

```haskell
module Main where

import Control.Monad -- for main only
import Data.List
```

The following example should give you an idea of what we're trying to do.

```haskell
main :: IO ()
main = do
  print t1
  print t2
  putStrLn "ChangeTerm:"
  print $ changeTerm t1 t2
  -- putStrLn "Diff:"
  -- print $ (diff t1 t2 :: ChangeTerm MetaVar)

t1 = Lam "x" (Var "x")
t2 = Lam "x" (App (Var "x") (Var "x"))
```

Within the "spine" of `λx`, the diff should replace the hole `0` by `0 0`.
There are some more examples at the end of this file in the function `main2`.

First of all, we will define a type for λ-terms and a corresponding context type along the lines of section 2.

```haskell
data Term
  = Var String
  | Lam String Term
  | App Term Term
  deriving (Show, Eq)

type MetaVar = Int

data TermC a
  = Hole a
  | VarC String
  | LamC String (TermC a)
  | AppC (TermC a) (TermC a)
  deriving (Show)

type ChangeTerm a = (TermC a, TermC a)
```

With those basic definitions out of the way, let us write the functions from section 2.2 in their order of appearance.

`changeTerm` computes an insertion context and a deletion context for two terms.
`wcs'` refers to the naive oracle function presented in section 2.4.
`postprocess` simply fills holes that don't appear in the other context.

```haskell
changeTerm :: Term -> Term -> ChangeTerm MetaVar
changeTerm a b = postprocess a b (extract (wcs' a b) a) (extract (wcs' a b) b)

-- If tree isn't a common subtree of a and b, convert it to a context.
-- Otherwise, return the corresponding hole.
extract oracle tree = maybe (peel tree) Hole (oracle tree)
    where
        peel (Var x) = VarC x
        peel (Lam p b) = LamC p $ extract oracle b
        peel (App f x) = AppC (extract oracle f) (extract oracle x)

postprocess a b insCtx delCtx = (fillHoles a insCtx, fillHoles b delCtx)
    where
        fillHoles t (Hole h)
            | not $ h `elem` commonHoles = toCtx t
            | otherwise                  = Hole h
        fillHoles (Lam _ b') (LamC p b)  = LamC p $ fillHoles b' b
        fillHoles (App f' x') (AppC f x) = AppC (fillHoles f' f) (fillHoles x' x)
        -- (big) assumption: the trees actually possess the same structure
        fillHoles _ c                    = c
    
        commonHoles = intersect (holes insCtx) (holes delCtx)

-- Should use sets.
holes :: TermC mv -> [mv]
holes (Hole h)   = [h]
holes (LamC _ b) = holes b
holes (AppC f x) = holes f ++ holes x
holes _          = []

wcs' l r x = elemIndex x $ intersect (subtrees l) (subtrees r)

subtrees (Var x) = [Var x]
subtrees (Lam p b) = Lam p b : subtrees b
subtrees (App f x) = App f x : (subtrees f ++ subtrees x)

toCtx (Var x) = VarC x
toCtx (Lam p b) = LamC p $ toCtx b
toCtx (App f x) = AppC (toCtx f) (toCtx x)
```

## Computing Patches

```haskell
type PatchTerm = TermC (ChangeTerm MetaVar)
```

Identify the spine of two contexts (greatest common prefix):

```haskell
gcp :: TermC mv -> TermC mv -> TermC (ChangeTerm mv)
gcp (VarC v)   (VarC v')    | v == v' = VarC v
gcp (LamC p b) (LamC p' b') | p == p' = LamC p $ gcp b b'
gcp (AppC f x) (AppC f' x')           = AppC (gcp f f') (gcp x x')
gcp a          b                      = Hole (a, b)
```

Get some closure:
This code is literally straight from the 3rd circle of hell.
This is kind of a horrible hack I used to fill in the blanks left in the introduction of [1].

```haskell
closure :: PatchTerm -> PatchTerm
closure (VarC v) = VarC v
closure (LamC p b) = LamC p $ closure b
closure (AppC f x)
  | open f' || open x' = Hole
    ( AppC f'l x'l
    , AppC f'r x'r
    )
  | otherwise = AppC f' x'
  where
    f' = closure f
    x' = closure x
    (f'l, f'r) = openUp f'
    (x'l, x'r) = openUp x'
closure (Hole h) = Hole h

openUp :: PatchTerm -> ChangeTerm MetaVar
openUp (Hole (l, r)) = (l, r)
openUp (VarC v) = (VarC v, VarC v)
openUp (LamC p b) = (LamC p bl, LamC p br)
  where (bl, br) = openUp b
openUp (AppC f x) = (AppC fl xl, AppC fr xr)
  where (fl, fr) = openUp f
        (xl, xr) = openUp x

open (Hole (lh, rh)) = not $ null (holes rh \\ holes lh)
open (LamC _ b) = open b
open (AppC f x) = open f || open x
open _          = False
```

## More examples

```haskell
examples =
  [ (t1, t2)
  , (App (Var "a") (Var "b"), App (Var "b") (Var "a"))
  , (App (App (Var "t") (Var "k")) (Var "u"), App (App (Var "t") (Var "k")) (Var "t"))
  , (App (Var "a") (App (Var "b") (Var "c")), App (Var "a") (App (Var "b") (Var "b")))
  ]

main2 = mapM_ go examples
  where
    go (l, r) = do
      putStrLn $ show l ++ " vs. " ++ show r
      putStrLn $ "ChangeTerm: " ++ show (changeTerm l r)
      putStrLn $ "Spine:      " ++ show (uncurry gcp $ changeTerm l r)
```

## References

[1]: AEATSD / TODO
