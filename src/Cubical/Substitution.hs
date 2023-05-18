

module Cubical.Substitution where

import Data.Foldable
import qualified Data.Array.LI as ALI

import Common
import Cubical.Interval

----------------------------------------------------------------------------------------------------

data IList = ILNil | ILDef IList I
  deriving (Eq, Show)

data Sub = Sub# Word32 Word32 IList
  deriving Eq

instance Show Sub where
  show (Sub d c is) = show (d, c, subToList (Sub d c is))

pattern Sub :: IVar -> IVar -> IList -> Sub
pattern Sub d c is <- Sub# (fromIntegral -> d) (fromIntegral -> c) is where
  Sub d c is = Sub# (fromIntegral d) (fromIntegral c) is
{-# complete Sub #-}

instance HasDom Sub where
  dom (Sub d c s) = d; {-# inline dom #-}
  setDom i (Sub _ c s) = Sub i c s; {-# inline setDom #-}

instance HasCod Sub where
  cod (Sub d c s) = c;   {-# inline cod #-}
  setCod i (Sub d c is) = Sub d i (dropIList (c - i) is); {-# inline setCod #-}

type SubArg = (?sub :: Sub)

mkIdSub :: IVar -> Sub
mkIdSub i = Sub i i (go 0 ILNil) where
  go j acc | i == j = acc
  go j acc = go (j + 1) (ILDef acc (IVar j))

mkIdSubs :: IVar -> [Sub]
mkIdSubs i = go i (case mkIdSub i of Sub _ _ is -> is) [] where
  go i is acc = case is of
    ILNil      -> acc
    ILDef is j -> go (i - 1) is (Sub (i-1) (i-1) is:acc)

idCacheSize :: IVar
idCacheSize = 1000

idSubs :: ALI.Array Sub
idSubs = ALI.fromList $ mkIdSubs idCacheSize
{-# noinline idSubs #-}

idSub :: IVar -> Sub
idSub i | i <  idCacheSize = idSubs ALI.! fromIntegral i
        | True             = mkIdSub i
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
    | d > cod ?sub = error ("SUB " ++ show s ++ " " ++ show ?sub)
    | True = Sub (dom ?sub) c (go is ?sub) where
        go :: IList -> Sub -> IList
        go is s = case is of
          ILNil      -> ILNil
          ILDef is i -> ILDef (go is s) (appSub s i)

pushSub :: Sub -> Sub -> Sub
pushSub (Sub d c is) (Sub _ c' is') = Sub d (c + c') (go is is') where
  go is ILNil         = is
  go is (ILDef is' i) = ILDef (go is is') i
