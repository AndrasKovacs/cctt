
module Cubical.Cofibration where

import Common
import Cubical.Interval
import Cubical.Substitution

import qualified Data.ISet as IS

----------------------------------------------------------------------------------------------------

-- | Conjunction of equalities and inequalities.
data Cof = CTrue | CEq I I Cof | CNEq I I Cof
  deriving Show

data NeCof
  = NCEq I I
  | NCNEq I I
  | NCAnd NeCof NeCof
  deriving Show

data NCof = NCof IVar NCof# deriving Eq
type NCofArg = (?cof :: NCof)

data NeCof' = NeCof' {
    neCof'Extended :: NCof
  , neCof'Extra    :: NeCof}

-- TODO: unbox
data VCof
  = VCTrue
  | VCFalse
  | VCNe NeCof' IS.Set

data NCof# =
    NCNil
  | NCLink NCof# I
  | NCRep NCof# IS.Set
  deriving Eq

makeFields ''NeCof'

instance HasDom NCof where
  dom (NCof d is) = d; {-# inline dom #-}
  setDom i (NCof d is) = NCof i (dropNCof# (d - i) is); {-# inline setDom #-}

dropNCof# :: IVar -> NCof# -> NCof#
dropNCof# i is = case i // is of
  (0, is         ) -> is
  (i, NCRep is _ ) -> dropNCof# (i - 1) is
  (i, NCLink is _) -> dropNCof# (i - 1) is
  _                -> impossible

instance Show NCof where
  show nc = "[" ++ go nc "" ++ "]" where
    sep = \case NCNil -> id
                _     -> (" | "++)
    go (NCof d is) = case is of
      NCNil         -> id
      NCLink is i   -> go (NCof (d - 1) is).sep is.((show (d - 1)++" = "++show i)++)
      NCRep is neqs -> go (NCof (d - 1) is).sep is.((show (d - 1)++" ≠ "++show neqs)++)

instance Show NeCof' where
  show (NeCof' c c') = show (c, c')

deriving instance Show VCof

instance Lift NCof where
  lift (NCof d is) = NCof (d + 1) (NCRep is mempty)
  {-# inline lift #-}

lookupNCof# :: NCof -> IVar -> (I, IS.Set)
lookupNCof# (NCof d is) i = go (NCof d is) (d - i - 1) where
  go (NCof d is) i = case (is, i) of
    (NCLink is i , 0) -> appNCof# (NCof (d - 1) is) i
    (NCRep _ neqs, 0) -> IVar (d - 1) // neqs
    (NCLink is _ , i) -> go (NCof (d - 1) is) (i - 1)
    (NCRep is _  , i) -> go (NCof (d - 1) is) (i - 1)
    _                 -> impossible

lookupNCof :: NCof -> IVar -> I
lookupNCof ncof i = fst (lookupNCof# ncof i)
{-# inline lookupNCof #-}

-- | Note: the IS.Set is only meaningful when the result is IVar.
appNCof# :: NCof -> I -> (I, IS.Set)
appNCof# ncof i = matchIVar i (lookupNCof# ncof) (i // mempty)
{-# inline appNCof# #-}

appNCof :: NCof -> I -> I
appNCof ncof i = fst (appNCof# ncof i)
{-# inline appNCof #-}

orient :: (IVar, IS.Set) -> (IVar, IS.Set) -> ((IVar, IS.Set), (IVar, IS.Set))
orient (!i, !ineq) (!j, !jneq)
  | i < j = ((i, ineq), (j, jneq))
  | True  = ((j, jneq), (i, ineq))
{-# inline orient #-}

-- | Extend with an IVar-constant equation.
conjFlexRigidEq# :: NCof -> (IVar, IS.Set) -> I -> NCof
conjFlexRigidEq# (NCof d is) (!i, !ineq) j = let

  -- Update:
  --   - neq links from i to x --> neq links from x to j
  belowI :: NCof -> IS.Set -> I -> NCof#
  belowI (NCof d is) ineq j = case is of
    NCNil ->
      NCNil
    NCLink is l ->
      NCLink (belowI (NCof (d - 1) is) ineq j) l
    NCRep is neqs ->
      let neqs' | IS.memberIVar (d - 1) ineq = IS.insert j neqs
                | otherwise                  = neqs
      in NCRep (belowI (NCof (d - 1) is) ineq j) neqs'

  -- Update:
  --  - all links to i to j
  --  - all neq links to i to j
  downToI :: NCof -> IVar -> IVar -> IS.Set -> I -> NCof#
  downToI (NCof d is) i topi ineq j = case (is, i) of
    (NCRep is _, 0) ->
      NCLink (belowI (NCof (d - 1) is) ineq j) j
    (NCRep is neqs, i) ->
      let neqs' | IS.memberIVar topi neqs = IS.insert j $ IS.deleteIVar topi neqs
                | otherwise               = neqs
      in NCRep (downToI (NCof (d - 1) is) (i - 1) topi ineq j) neqs'
    (NCLink is l, i) ->
      let l' | l == IVar topi = j
             | otherwise      = l
      in NCLink (downToI (NCof (d - 1) is) (i - 1) topi ineq j) l'
    _ ->
      impossible

  in NCof d (downToI (NCof d is) (d - i - 1) i ineq j)

-- | Extend a cof with an IVar-IVar equation.
conjFlexFlexEq# :: NCof -> (IVar, IS.Set) -> (IVar, IS.Set) -> NCof
conjFlexFlexEq# (NCof d is) (!i, !ineqs) (!j, !jneqs) = let

  -- Update
  --   - The neqset of i is merged with the weakening of the neqset of j
  --   - every neq link from j to x --> new link from x to i
  downToI :: NCof -> IVar -> IVar -> IS.Set -> NCof#
  downToI (NCof d is) i topi jneqs = case (is, i) of
    (NCRep is neqs, 0) ->
      NCRep is (neqs <> jneqs)
    (NCRep is neqs, i) ->
      let neqs' | IS.memberIVar (d - 1) jneqs = IS.insertIVar topi neqs
                | otherwise                   = neqs
      in NCRep (downToI (NCof (d - 1) is) (i - 1) topi (IS.deleteIVar (d - 1) jneqs)) neqs'
    (NCLink is l, i) ->
      NCLink (downToI (NCof (d - 1) is) (i - 1) topi (IS.deleteIVar (d - 1) jneqs)) l
    _ ->
      impossible

  -- Update
  --   - j to a link to i
  --   - every link to j to i
  --   - every neq link to j to a neq link to i
  downToJ :: NCof -> IVar -> IVar -> IVar -> IVar -> IS.Set -> NCof#
  downToJ (NCof d is) i topi j topj jneqs = case (is, j) of
    (NCRep is _, 0) ->
      NCLink (downToI (NCof (d - 1) is) (i - 1) topi jneqs) (IVar topi)
    (NCRep is neqs, j) ->
      let neqs' | IS.memberIVar topj neqs = IS.insertIVar topi $ IS.deleteIVar topj neqs
                | otherwise               = neqs
      in NCRep (downToJ (NCof (d - 1) is) (i - 1) topi (j - 1) topj jneqs) neqs'
    (NCLink is l, j) ->
      let l' | l == IVar topj = IVar topi
             | otherwise      = l
      in NCLink (downToJ (NCof (d - 1) is) (i - 1) topi (j - 1) topj jneqs) l'
    _ ->
      impossible

  in NCof d (downToJ (NCof d is) (d - i - 1) i (d - j - 1) j jneqs)


-- | Evaluate an equality of forced I-s.
eq# :: NCofArg => (I, IS.Set) -> (I, IS.Set) -> VCof
eq# (!i, !ineq) (!j, !jneq)
  | i == j =
    VCTrue

  | otherwise = case (i, j) of

    (IVar i, IVar j) ->
      case orient (i,ineq) (j,jneq) of
        ((i,ineq), (j,jneq))
          | IS.member (IVar i) jneq ->
            VCFalse
          | otherwise ->
            VCNe (NeCof' (conjFlexFlexEq# ?cof (i,ineq) (j,jneq))
                         (NCEq (IVar i) (IVar j)))
                 (IS.insertIVar i $ IS.insertIVar j mempty)

    (IVar i, j)
      | IS.member j ineq ->
        VCFalse
      | otherwise ->
        VCNe (NeCof' (conjFlexRigidEq# ?cof (i,ineq) j)
                     (NCEq (IVar i) j))
             (IS.insertIVar i mempty)

    (i, IVar j)
      | IS.member i jneq ->
        VCFalse
      | otherwise ->
        VCNe (NeCof' (conjFlexRigidEq# ?cof (j,jneq) i)
                     (NCEq i (IVar j)))
             (IS.insertIVar j mempty)

    _ -> VCFalse

-- | Extend with an I-IVar inequality.
conjFlexNEq# :: NCof -> I -> IVar -> NCof
conjFlexNEq# (NCof d is) i j = NCof d (go is i (d - j - 1)) where
  go is i j = case (is, j) of
    (NCRep is neqs, 0) -> NCRep is (IS.insert i neqs)
    (NCRep is neqs, j) -> NCRep (go is i (j - 1)) neqs
    (NCLink is l  , j) -> NCLink (go is i (j - 1)) l
    _                  -> impossible

-- | Evaluate an inequality of forced I-s.
neq# :: NCofArg => (I, IS.Set) -> (I, IS.Set) -> VCof
neq# (!i, !ineq) (!j, !jneq)
  | i == j =
    VCFalse

  | otherwise = case (i, j) of

    (IVar i, IVar j) ->
      case orient (i,ineq)(j,jneq) of
        ((i,ineq), (j,jneq))
          | IS.member (IVar i) jneq ->
            VCTrue
          | otherwise ->
            VCNe (NeCof' (conjFlexNEq# ?cof (IVar i) j) (NCNEq (IVar i) (IVar j)))
                 (IS.insertIVar i $ IS.insertIVar j mempty)

    (IVar i, j)
      | IS.member j ineq ->
        VCTrue
      | otherwise ->
        VCNe (NeCof' (conjFlexNEq# ?cof j i) (NCNEq (IVar i) j))
             (IS.insertIVar i mempty)

    (i, IVar j)
      | IS.member i jneq ->
        VCTrue
      | otherwise ->
        VCNe (NeCof' (conjFlexNEq# ?cof i j) (NCNEq i (IVar j)))
             (IS.insertIVar j mempty)

    _ -> VCTrue

-- | Extend with a forced neutral NeCof. Error if non-neutral.
conjNeCof :: NCofArg => NeCof -> NCof
conjNeCof = \case
  NCEq i j    -> case eq  i j of VCNe (NeCof' nc  _) _ -> nc; _ -> impossible
  NCNEq i j   -> case neq i j of VCNe (NeCof' nc  _) _ -> nc; _ -> impossible
  NCAnd c1 c2 -> let ?cof = conjNeCof c1 in conjNeCof c2

assumeNeCof :: NeCof -> (NCofArg => a) -> (NCofArg => a)
assumeNeCof nc act = let ?cof = conjNeCof nc in act
{-# inline assumeNeCof #-}

idNCof :: IVar -> NCof
idNCof i = NCof i (go i NCNil) where
  go 0 acc = acc
  go i acc = go (i - 1) (NCRep acc mempty)

emptyNCof :: NCof
emptyNCof = NCof 0 NCNil

quoteNCof :: NCof -> Cof
quoteNCof = go CTrue where
  go :: Cof -> NCof -> Cof
  go acc (NCof d is) = case is of
    NCNil -> acc
    NCRep is neqs -> go (IS.foldl (\c i -> CNEq (IVar (d - 1)) i c) acc neqs)
                        (NCof (d - 1) is)
    NCLink is j   -> go (CEq (IVar (d - 1)) j acc) (NCof (d - 1) is)

reverseCof :: Cof -> Cof
reverseCof = go CTrue where
  go acc CTrue        = acc
  go acc (CEq i j c)  = go (CEq i j acc) c
  go acc (CNEq i j c) = go (CNEq i j acc) c

-- | Validity:
--    - Every eq/neq link goes downwards.
validNCof :: NCof -> Bool
validNCof = go where

  validI :: IVar -> I -> Bool
  validI i (IVar j) = j < i
  validI _ _        = True

  go :: NCof -> Bool
  go (NCof d is) = case is of
    NCNil         -> True
    NCLink is j   -> validI (d - 1) j && go (NCof (d - 1) is)
    NCRep is neqs -> IS.foldr (\i b -> validI (d - 1) i && b)
                              (go (NCof (d - 1) is)) neqs

-- TODO: additional validation: tripping through quote and evalCof

----------------------------------------------------------------------------------------------------

appNCofToSub :: NCof -> Sub -> Sub
appNCofToSub nc (Sub d c is) = Sub d c (go nc is) where
  go nc ILNil        = ILNil
  go nc (ILDef is i) = ILDef (go nc is) (appNCof nc i)

wkSub :: NCofArg => Sub -> Sub
wkSub s = setDom (dom ?cof) s
{-# inline wkSub #-}

----------------------------------------------------------------------------------------------------

eq :: NCofArg => I -> I -> VCof
eq i j = eq# (appNCof# ?cof i) (appNCof# ?cof j)

neq :: NCofArg => I -> I -> VCof
neq i j = neq# (appNCof# ?cof i) (appNCof# ?cof j)

eqS :: SubArg => NCofArg => I -> I -> VCof
eqS i j = eq# (appNCof# ?cof (sub i)) (appNCof# ?cof (sub j))

neqS :: SubArg => NCofArg => I -> I -> VCof
neqS i j = neq# (appNCof# ?cof (sub i)) (appNCof# ?cof (sub j))

evalI :: NCofArg => SubArg => I -> I
evalI i = appNCof ?cof (sub i)

evalCof :: NCofArg => SubArg => Cof -> VCof
evalCof = \case
  CTrue        -> VCTrue
  CEq i j cof  -> case eqS i j of
    VCTrue    -> evalCof cof
    VCFalse   -> VCFalse
    VCNe c is -> let ?cof = c^.extended in case evalCof cof of
                   VCTrue      -> VCNe c is
                   VCFalse     -> VCFalse
                   VCNe c' is' -> VCNe (NeCof' (c'^.extended) (NCAnd (c^.extra) (c'^.extra)))
                                       (is <> is')
  CNEq i j cof -> case neqS i j of
    VCTrue    -> evalCof cof
    VCFalse   -> VCFalse
    VCNe c is -> let ?cof = c^.extended in case evalCof cof of
                   VCTrue      -> VCNe c is
                   VCFalse     -> VCFalse
                   VCNe c' is' -> VCNe (NeCof' (c'^.extended) (NCAnd (c^.extra) (c'^.extra)))
                                       (is <> is')

----------------------------------------------------------------------------------------------------

isUnblocked :: NCofArg => IS.Set -> Bool
isUnblocked is =
  IS.foldrAccum
    (\x hyp (!varset, !cof) ->
       matchIVar (appNCof cof x)
         (\x -> IS.memberIVar x varset || hyp (IS.insertIVar x varset // cof))
         True)
    (mempty, ?cof)
    False
    (IS.delete01 is)

isUnblockedS :: SubArg => NCofArg => IS.Set -> Bool
isUnblockedS is = IS.foldrAccum
  (\x hyp (!varset, !sub, !cof) ->
     matchIVar (appSub sub x)
       (\x -> matchIVar (lookupNCof cof x)
         (\x -> IS.memberIVar x varset || hyp ((,,) $$! IS.insertIVar x varset $$! sub $$! cof))
         True)
       True)
  (mempty, ?sub, ?cof)
  False
  (IS.delete01 is)

-- | Insert an *unforced* I to an `IS.Set`.
insertI :: NCofArg => I -> IS.Set -> IS.Set
insertI i s = IS.insert (appNCof ?cof i) s
{-# inline insertI #-}

neCofVars :: NeCof -> IS.Set
neCofVars = \case
  NCEq i j    -> IS.insert i $ IS.insert j mempty
  NCNEq i j   -> IS.insert i $ IS.insert j mempty
  NCAnd c1 c2 -> neCofVars c1 <> neCofVars c2

----------------------------------------------------------------------------------------------------
