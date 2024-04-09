
module Cubical.Cofibration where

import Common
import Cubical.Interval
import Cubical.Substitution
import Statistics (bumpMaxIVar)

import qualified Data.IVarSet as IS

----------------------------------------------------------------------------------------------------

data Cof = CEq I I deriving Show
data NeCof = NCEq I I deriving Show

-- | Substitution which maps each ivar to its smallest
--   representative ivar in the equivalence class.
data NCof = NCof IVar IList

type NCofArg = (?cof :: NCof)

data NeCof' = NeCof' {
    neCof'Extended :: NCof
  , neCof'Extra    :: {-# unpack #-} NeCof}

-- TODO: unbox
data VCof
  = VCTrue
  | VCFalse
  | VCNe {-# unpack #-} NeCof'

makeFields ''NeCof'

instance HasDom NCof where
  dom (NCof d is) = d; {-# inline dom #-}
  setDom i (NCof d is) = NCof i (dropIList (d - i) is); {-# inline setDom #-}

instance Show NCof where
  show nc = "[" ++ go nc "" ++ "]" where
    sep = \case ILNil -> id
                _     -> (" | "++)
    go (NCof d is) = case is of
      ILNil         -> id
      ILDef is i    -> go (NCof (d - 1) is).sep is.((show (d - 1)++" = "++show i)++)

instance Show NeCof' where
  show (NeCof' c c') = show (c, c')

deriving instance Show VCof

instance Lift NCof where
  lift (NCof d is) = runIO (bumpMaxIVar d >> (pure $! (NCof (d + 1) (ILDef is (IVar d)))))
  -- lift (NCof d is) = NCof (d + 1) (ILDef is (IVar d))
  {-# inline lift #-}

lookupNCof :: IVar -> NCof -> I
lookupNCof i (NCof d is) = lookupIList (d - i - 1) is
{-# inline lookupNCof #-}

appNCof :: NCof -> I -> I
appNCof ncof i = matchIVar i (\i -> lookupNCof i ncof) i
{-# inline appNCof #-}

orient :: (IVar, IVar) -> (IVar, IVar)
orient (i, j) | i < j = (i, j)
              | True  = (j, i)

solve :: NCof -> IVar -> I -> NCof
solve (NCof d is) i j = NCof d (go d is i j) where
  go d is i j = case is of
    ILNil -> impossible
    ILDef is i' | d - 1 == i   -> ILDef is j
                | i' == IVar i -> ILDef (go (d - 1) is i j) j
                | True         -> ILDef (go (d - 1) is i j) i'

-- | Equate forced I-s.
eq# :: NCofArg => I -> I -> VCof
eq# i j = case (i, j) of
  (i, j) | i == j  -> VCTrue
  (IVar i, IVar j) -> case orient (i, j) of
                        (i', j') -> VCNe (NeCof' (solve ?cof j' (IVar i')) (NCEq (IVar i) (IVar j)))
  (IVar i, j     ) -> VCNe (NeCof' (solve ?cof i j) (NCEq (IVar i) j))
  (i     , IVar j) -> VCNe (NeCof' (solve ?cof j i) (NCEq (IVar j) i))
  _                -> VCFalse

eq :: NCofArg => I -> I -> VCof
eq i j = eq# (appNCof ?cof i) (appNCof ?cof j)
{-# inline eq #-}

evalI :: NCofArg => SubArg => I -> I
evalI i = appNCof ?cof (sub i)
{-# inline evalI #-}

eqS :: SubArg => NCofArg => I -> I -> VCof
eqS i j = eq# (evalI i) (evalI j)
{-# inline eqS #-}

-- | Extend with a forced neutral NeCof. Error if non-neutral.
conjNeCof :: NCofArg => NeCof -> NCof
conjNeCof = \case
  NCEq i j    -> case (i, j) of
    (i     , j     ) | i == j -> impossible
    (IVar i, IVar j)          -> case orient (i, j) of (i, j) -> solve ?cof j (IVar i)
    (IVar i, j     )          -> solve ?cof i j
    (i     , IVar j)          -> solve ?cof j i
    (i, j)                    -> impossible

assumeNeCof :: NeCof -> (NCofArg => a) -> (NCofArg => a)
assumeNeCof nc act = let ?cof = conjNeCof nc in act
{-# inline assumeNeCof #-}

idNCof :: IVar -> NCof
idNCof i = NCof i (go 0 ILNil) where
  go j acc | i == j = acc
  go j acc = go (j + 1) (ILDef acc (IVar j))

emptyNCof :: NCof
emptyNCof = NCof 0 ILNil

----------------------------------------------------------------------------------------------------

appNCofToSub :: NCof -> Sub -> Sub
appNCofToSub nc (Sub d c is) = Sub d c (go nc is) where
  go nc ILNil        = ILNil
  go nc (ILDef is i) = ILDef (go nc is) (appNCof nc i)

wkSub :: NCofArg => Sub -> Sub
wkSub s = setDom (dom ?cof) s
{-# inline wkSub #-}

----------------------------------------------------------------------------------------------------

evalCof :: NCofArg => SubArg => Cof -> VCof
evalCof (CEq i j) = eqS i j
{-# inline evalCof #-}

----------------------------------------------------------------------------------------------------

isUnblocked :: NCofArg => IS.Set -> Bool
isUnblocked is =
  IS.foldrAccum
    (\x hyp (!varset, !cof) ->
       matchIVar (lookupNCof x cof)
         (\x -> IS.member x varset || hyp (IS.insert x varset // cof))
         True)
    (mempty, ?cof)
    False
    is

isUnblockedS :: SubArg => NCofArg => IS.Set -> Bool
isUnblockedS is = IS.foldrAccum
  (\x hyp (!varset, !sub, !cof) ->
     matchIVar (lookupSub x sub)
       (\x -> matchIVar (lookupNCof x cof)
         (\x -> IS.member x varset || hyp ((,,) $$! IS.insert x varset $$! sub $$! cof))
         True)
       True)
  (mempty, ?sub, ?cof)
  False
  is

insertI :: NCofArg => I -> IS.Set -> IS.Set
insertI i s = IS.insertI (appNCof ?cof i) s
{-# inline insertI #-}

neCofVars :: NeCof -> IS.Set
neCofVars (NCEq i j) = IS.insertI i $ IS.insertI j mempty
{-# inline neCofVars #-}
