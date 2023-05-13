

module Cubical.Substitution where

import Data.Foldable
import qualified Data.Array.LI as ALI

import Common
import Cubical.Interval

----------------------------------------------------------------------------------------------------

data IList = ILNil | ILDef IList I
  deriving Show

data Sub = Sub# Word32 Word32 IList

instance Show Sub where
  show (Sub d c is) = show (d, c, subToList (Sub d c is))

pattern Sub :: IVar -> IVar -> IList -> Sub
pattern Sub d c is <- Sub# (fromIntegral -> d) (fromIntegral -> c) is where
  Sub d c is = Sub# (fromIntegral d) (fromIntegral c) is
{-# complete Sub #-}

instance HasDom Sub where
  dom f (Sub d c s) = (\d -> Sub d c s) <$> f d
  {-# inline dom #-}

instance HasCod Sub where
  cod f (Sub d c s) = (\c -> Sub d c s) <$> f c
  {-# inline cod #-}

type SubArg = (?sub :: Sub)

mkIdSub :: IVar -> Sub
mkIdSub i = Sub i i (go 0 ILNil) where
  go j acc | i == j = acc
  go j acc = go (j + 1) (ILDef acc (IVar j))

idSubs :: ALI.Array Sub
idSubs = ALI.fromList $ map mkIdSub [0..maxIVar]
{-# noinline idSubs #-}

idSub :: IVar -> Sub
idSub i = idSubs ALI.! fromIntegral i
{-# inline idSub #-}

lookupIList :: IVar -> IList -> I
lookupIList i is = case (i, is) of
  (0, ILDef _ i)  -> i
  (i, ILDef is _) -> lookupIList (i - 1) is
  _               -> impossible

lookupSub :: IVar -> Sub -> I
lookupSub i (Sub d c s) = lookupIList (c - i - 1) s
{-# inline lookupSub #-}

emptySub :: IVar -> Sub
emptySub d = Sub d 0 ILNil
{-# inline emptySub #-}

subToList :: Sub -> [I]
subToList (Sub _ _ is) = go is [] where
  go ILNil        acc = acc
  go (ILDef is i) acc = go is (i:acc)

extError :: I -> IVar -> a
extError i d = error $ "ext: " ++ show i ++ " " ++ show d
{-# noinline extError #-}

-- | Extend a sub with an expression. Domain doesn't change.
ext :: Sub -> I -> Sub
ext (Sub d c is) i =
  let i' = matchIVar i (\case i | i < d -> IVar i; i -> extError (IVar i) d) i
  in Sub d (c + 1) (ILDef is i')
{-# inline ext #-}

instance Lift Sub where
  lift (Sub d c is) = Sub (d + 1) (c + 1) (ILDef is (IVar d))
  {-# inline lift #-}

subFromList :: [I] -> Sub
subFromList is =
  let dom = case [x | IVar x <- is] of [] -> 0; is -> maximum is + 1
  in foldl' ext (emptySub dom) is

dropIList :: IVar -> IList -> IList
dropIList i is = case i // is of
  (0, is)         -> is
  (i, ILDef is _) -> dropIList (i - 1) is
  _               -> impossible

setCod :: IVar -> Sub -> Sub
setCod i (Sub d c is) = Sub d i (dropIList (c - i) is)

setDom :: IVar -> Sub -> Sub
setDom d (Sub _ c is) = Sub d c is

class SubAction a where
  sub :: SubArg => a -> a

appSub :: SubAction a => Sub -> a -> a
appSub s a = let ?sub = s in sub a
{-# inline appSub #-}

instance SubAction I where
  sub i = matchIVar i (\i -> lookupSub i ?sub) i
  {-# inline sub #-}

-- | Substitution composition.
instance SubAction Sub where
  sub s@(Sub d c is)
    | d > ?sub^.cod = error ("SUB " ++ show s ++ " " ++ show ?sub)
    | True = Sub (?sub^.dom) c (go is ?sub) where
        go :: IList -> Sub -> IList
        go is s = case is of
          ILNil      -> ILNil
          ILDef is i -> ILDef (go is s) (appSub s i)

pushSub :: Sub -> Sub -> Sub
pushSub (Sub d c is) (Sub _ c' is') = Sub d (c + c') (go is is') where
  go is ILNil         = is
  go is (ILDef is' i) = ILDef (go is is') i
