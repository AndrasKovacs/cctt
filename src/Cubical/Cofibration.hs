
module Cubical.Cofibration where

import Common
import Cubical.Interval
import Cubical.Substitution

import qualified Data.IVarSet as IS

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


-- instance HasDom NCof where
--   dom (NCof d is) = d; {-# inline dom #-}
--   setDom i (NCof d is) = NCof i (dropNCof# (d - i) is); {-# inline setDom #-}

-- dropNCof# :: IVar -> NCof# -> NCof#
-- dropNCof# i is = case i // is of
--   (0, is         ) -> is
--   (i, NCRep is _ ) -> dropNCof# (i - 1) is
--   (i, NCLink is _) -> dropNCof# (i - 1) is
--   _                -> impossible

-- instance Show NCof where
--   show nc = "[" ++ go nc "" ++ "]" where
--     sep = \case NCNil -> id
--                 _     -> (" | "++)
--     go (NCof d is) = case is of
--       NCNil         -> id
--       NCLink is i   -> go (NCof (d - 1) is).sep is.((show (d - 1)++" = "++show i)++)
--       NCRep is neqs -> go (NCof (d - 1) is).sep is.((show (d - 1)++" ≠ "++show neqs)++)

-- instance Show NeCof' where
--   show (NeCof' c c') = show (c, c')

-- deriving instance Show VCof

-- instance Lift NCof where
--   lift (NCof d is) = NCof (d + 1) (NCRep is mempty)
--   {-# inline lift #-}

-- lookupNCof :: IVar -> NCof -> I
-- lookupNCof i (NCof d is) = case is of
--   NCLink is j | d - 1 == i -> j
--               | True       -> lookupNCof i (NCof (d - 1) is)
--   NCRep is _  | d - 1 == i -> IVar i
--               | True       -> lookupNCof i (NCof (d - 1) is)
--   _                        -> impossible

-- lookupNCof# :: IVar -> NCof -> (I, IS.Set)
-- lookupNCof# i (NCof d is) = case is of
--   NCLink is j  | d - 1 == i -> appNCof# (NCof (d - 1) is) j
--                | True       -> lookupNCof# i (NCof (d - 1) is)
--   NCRep is neq | d - 1 == i -> (IVar i, neq)
--                | True       -> lookupNCof# i (NCof (d - 1) is)
--   _                         -> impossible

-- appNCof :: NCof -> I -> I
-- appNCof ncof i = matchIVar i (\i -> lookupNCof i ncof) i
-- {-# inline appNCof #-}

-- appNCof# :: NCof -> I -> (I, IS.Set)
-- appNCof# ncof i = matchIVar i (\i -> lookupNCof# i ncof) (i, mempty)
-- {-# inline appNCof# #-}

-- orient :: (IVar, IS.Set) -> (IVar, IS.Set) -> ((IVar, IS.Set), (IVar, IS.Set))
-- orient (!i, !ineq) (!j, !jneq)
--   | i < j = ((i, ineq), (j, jneq))
--   | True  = ((j, jneq), (i, ineq))
-- {-# inline orient #-}

-- -- | Extend with an IVar-constant equation.
-- conjFlexRigidEq# :: NCof -> IVar -> I -> NCof
-- conjFlexRigidEq# (NCof d is) i j = let

--   newLink :: IVar -> I -> (NCof#, IS.Set, IS.Set) -> (NCof#, IS.Set, IS.Set)
--   newLink x j (is, s0, s1) = case j of
--     I0 -> (,,) $$! NCLink is I0 $$! IS.insert x s0 $$! s1
--     I1 -> (,,) $$! NCLink is I1 $$! s0 $$! IS.insert x s1
--     _  -> impossible
--   {-# inline newLink #-}

--   belowI :: NCof -> IS.Set -> IS.Set -> (NCof#, IS.Set, IS.Set)
--   belowI (NCof d is) s0 s1 = case is of
--     NCNil ->
--       (NCNil, s0, s1)

--     NCLink is l ->
--       case belowI (NCof (d - 1) is) s0 s1 of
--         (is, s0, s1) ->
--           let l' = matchIVar l (\case x | IS.member x s0 -> I0
--                                         | IS.member x s1 -> I1
--                                         | True           -> l) l
--           in (,,) $$! NCLink is l' $$! s0 $$! s1

--     NCRep is neqs ->
--       let curr = d - 1
--           (!s0', !s1') | IS.member curr s0 = (s0 // (neqs <> s1))
--                        | IS.member curr s1 = ((neqs <> s0) // s1)
--                        | True              = (s0, s1)
--       in case belowI (NCof curr is) s0' s1' of
--         res@(is, s0, s1)
--           | IS.member curr s0 || not (IS.null (IS.intersect neqs s1)) -> newLink curr I0 res
--           | IS.member curr s1 || not (IS.null (IS.intersect neqs s0)) -> newLink curr I1 res
--           | True                                                      -> (NCRep is neqs, s0, s1)

--   toI :: NCof -> IVar -> I -> (NCof#, IS.Set, IS.Set)
--   toI (NCof d is) i j = case is of
--     NCNil ->
--       impossible

--     NCLink is l ->
--       case toI (NCof (d - 1) is) i j of
--         (is, s0, s1) ->
--           let l' = matchIVar l (\case x | IS.member x s0 -> I0
--                                         | IS.member x s1 -> I1
--                                         | True           -> l) l
--           in (,,) $$! NCLink is l' $$! s0 $$! s1

--     NCRep is neqs
--       | d - 1 == i ->
--         let (!s0, !s1) | j == I0 = (IS.insert i mempty // neqs)
--                        | j == I1 = (neqs // IS.insert i mempty)
--                        | True    = impossible
--         in case belowI (NCof (d - 1) is) s0 s1 of
--           (is, s0, s1) -> (NCLink is j, s0, s1)

--       | True ->
--         let curr = d - 1
--         in case toI (NCof curr is) i j of
--           res@(is, s0, s1)
--             | not $ IS.null $ IS.intersect neqs s0 -> newLink curr I1 res
--             | not $ IS.null $ IS.intersect neqs s1 -> newLink curr I0 res
--             | True                                 -> (NCRep is neqs, s0, s1)

--   in case toI (NCof d is) i j of
--     (is, _, _) -> NCof d is


-- -- | Extend with an IVar-IVar equation
-- conjFlexFlexEq# :: NCof -> IVar -> (IVar, IS.Set) -> NCof
-- conjFlexFlexEq# (NCof d is) i (!j, !jneq) = let

--   toI :: NCof -> IVar -> IS.Set -> NCof#
--   toI (NCof d is) i jneq = case is of
--     NCNil ->
--       impossible
--     NCLink is l ->
--       NCLink (toI (NCof (d - 1) is) i jneq) l
--     NCRep is neqs
--       | d - 1 == i ->
--         NCRep is (neqs <> jneq)
--       | True ->
--         let neqs' | IS.member (d - 1) jneq = IS.insert i neqs
--                   | True                   = neqs
--         in NCRep (toI (NCof (d - 1) is) i (IS.delete (d - 1) jneq)) neqs'

--   toJ :: NCof -> IVar -> IVar -> IS.Set -> NCof#
--   toJ (NCof d is) i j jneq = case is of
--     NCNil ->
--       impossible
--     NCLink is l ->
--       let l' | l == IVar j = IVar i
--              | True        = l
--       in NCLink (toJ (NCof (d - 1) is) i j jneq) l'
--     NCRep is neqs
--       | d - 1 == j ->
--         NCLink (toI (NCof (d - 1) is) i jneq) (IVar i)
--       | True ->
--         let neqs' | IS.member j neqs = IS.insert i $ IS.delete j neqs
--                   | True             = neqs
--         in NCRep (toJ (NCof (d - 1) is) i j jneq) neqs'

--   in NCof d (toJ (NCof d is) i j jneq)


-- -- | Extend with an IVar-IVar inequality
-- conjFlexFlexNEq# :: NCof -> IVar -> IVar -> NCof
-- conjFlexFlexNEq# (NCof d is) i j = NCof d (go (NCof d is) i j) where
--   go :: NCof -> IVar -> IVar -> NCof#
--   go (NCof d is) i j = case is of
--     NCNil         -> impossible
--     NCLink is l   -> NCLink (go (NCof (d - 1) is) i j) l
--     NCRep is neqs -> if d - 1 == j then NCRep is (IS.insert i neqs)
--                                    else NCRep (go (NCof (d - 1) is) i j) neqs

-- -- | Evaluate an equality of forced I-s.
-- eq# :: NCofArg => (I, IS.Set) -> (I, IS.Set) -> VCof
-- eq# (!i, !ineq) (!j, !jneq)
--   | i == j =
--     VCTrue

--   | otherwise = case (i, j) of

--     (IVar i, IVar j) ->
--       case orient (i,ineq) (j,jneq) of
--         ((i,ineq), (j,jneq))
--           | IS.member i jneq ->
--             VCFalse
--           | otherwise ->
--             VCNe (NeCof' (conjFlexFlexEq# ?cof i (j,jneq))
--                          (NCEq (IVar i) (IVar j)))
--                  (IS.insert i $ IS.insert j mempty)

--     (IVar i, j) ->
--       VCNe (NeCof' (conjFlexRigidEq# ?cof i j)
--                    (NCEq (IVar i) j))
--            (IS.insert i mempty)

--     (i, IVar j) ->
--       VCNe (NeCof' (conjFlexRigidEq# ?cof j i)
--                    (NCEq i (IVar j)))
--            (IS.insert j mempty)

--     _ ->
--       VCFalse

-- -- | Evaluate an inequality of forced I-s.
-- neq# :: NCofArg => (I, IS.Set) -> (I, IS.Set) -> VCof
-- neq# (!i, !ineq) (!j, !jneq)
--   | i == j =
--     VCFalse

--   | otherwise = case (i, j) of

--     (IVar i, IVar j) ->
--       case orient (i,ineq)(j,jneq) of
--         ((i,ineq), (j,jneq))
--           | IS.member i jneq ->
--             VCTrue
--           | otherwise ->
--             VCNe (NeCof' (conjFlexFlexNEq# ?cof i j) (NCNEq (IVar i) (IVar j)))
--                  (IS.insert i $ IS.insert j mempty)

--     (IVar i, j) ->
--       VCNe (NeCof' (conjFlexRigidEq# ?cof i j) (NCEq (IVar i) (flip# j)))
--            (IS.insert i mempty)

--     (i, IVar j) ->
--       VCNe (NeCof' (conjFlexRigidEq# ?cof j i) (NCEq (flip# i) (IVar j)))
--            (IS.insert j mempty)

--     _ -> VCTrue

-- eq :: NCofArg => I -> I -> VCof
-- eq i j = eq# (appNCof# ?cof i) (appNCof# ?cof j)

-- neq :: NCofArg => I -> I -> VCof
-- neq i j = neq# (appNCof# ?cof i) (appNCof# ?cof j)

-- eqS :: SubArg => NCofArg => I -> I -> VCof
-- eqS i j = eq# (appNCof# ?cof (sub i)) (appNCof# ?cof (sub j))

-- neqS :: SubArg => NCofArg => I -> I -> VCof
-- neqS i j = neq# (appNCof# ?cof (sub i)) (appNCof# ?cof (sub j))

-- evalI :: NCofArg => SubArg => I -> I
-- evalI i = appNCof ?cof (sub i)

-- -- | Extend with a forced neutral NeCof. Error if non-neutral.
-- conjNeCof :: NCofArg => NeCof -> NCof
-- conjNeCof = \case
--   NCEq i j    -> case eq  i j of VCNe (NeCof' nc  _) _ -> nc; _ -> impossible
--   NCNEq i j   -> case neq i j of VCNe (NeCof' nc  _) _ -> nc; _ -> impossible
--   NCAnd c1 c2 -> let ?cof = conjNeCof c1 in conjNeCof c2

-- assumeNeCof :: NeCof -> (NCofArg => a) -> (NCofArg => a)
-- assumeNeCof nc act = let ?cof = conjNeCof nc in act
-- {-# inline assumeNeCof #-}

-- idNCof :: IVar -> NCof
-- idNCof i = NCof i (go i NCNil) where
--   go 0 acc = acc
--   go i acc = go (i - 1) (NCRep acc mempty)

-- emptyNCof :: NCof
-- emptyNCof = NCof 0 NCNil

-- quoteNCof :: NCof -> Cof
-- quoteNCof = go CTrue where
--   go :: Cof -> NCof -> Cof
--   go acc (NCof d is) = case is of
--     NCNil -> acc
--     NCRep is neqs -> go (IS.foldl (\c i -> CNEq (IVar (d - 1)) (IVar i) c) acc neqs)
--                         (NCof (d - 1) is)
--     NCLink is j   -> go (CEq (IVar (d - 1)) j acc) (NCof (d - 1) is)

-- reverseCof :: Cof -> Cof
-- reverseCof = go CTrue where
--   go acc CTrue        = acc
--   go acc (CEq i j c)  = go (CEq i j acc) c
--   go acc (CNEq i j c) = go (CNEq i j acc) c

-- -- | Validity:
-- --    - Every eq/neq link goes downwards.
-- validNCof :: NCof -> Bool
-- validNCof = go where

--   validI :: IVar -> I -> Bool
--   validI i (IVar j) = j < i
--   validI _ _        = True

--   go :: NCof -> Bool
--   go (NCof d is) = case is of
--     NCNil         -> True
--     NCLink is j   -> validI (d - 1) j && go (NCof (d - 1) is)
--     NCRep is neqs -> IS.foldr (\i b -> validI (d - 1) (IVar i) && b)
--                               (go (NCof (d - 1) is)) neqs

-- -- TODO: additional validation: tripping through quote and evalCof

-- ----------------------------------------------------------------------------------------------------

-- appNCofToSub :: NCof -> Sub -> Sub
-- appNCofToSub nc (Sub d c is) = Sub d c (go nc is) where
--   go nc ILNil        = ILNil
--   go nc (ILDef is i) = ILDef (go nc is) (appNCof nc i)

-- wkSub :: NCofArg => Sub -> Sub
-- wkSub s = setDom (dom ?cof) s
-- {-# inline wkSub #-}

-- ----------------------------------------------------------------------------------------------------

-- evalCof :: NCofArg => SubArg => Cof -> VCof
-- evalCof = \case
--   CTrue        -> VCTrue
--   CEq i j cof  -> case eqS i j of
--     VCTrue    -> evalCof cof
--     VCFalse   -> VCFalse
--     VCNe c is -> let ?cof = c^.extended in case evalCof cof of
--                    VCTrue      -> VCNe c is
--                    VCFalse     -> VCFalse
--                    VCNe c' is' -> VCNe (NeCof' (c'^.extended) (NCAnd (c^.extra) (c'^.extra)))
--                                        (is <> is')
--   CNEq i j cof -> case neqS i j of
--     VCTrue    -> evalCof cof
--     VCFalse   -> VCFalse
--     VCNe c is -> let ?cof = c^.extended in case evalCof cof of
--                    VCTrue      -> VCNe c is
--                    VCFalse     -> VCFalse
--                    VCNe c' is' -> VCNe (NeCof' (c'^.extended) (NCAnd (c^.extra) (c'^.extra)))
--                                        (is <> is')

-- ----------------------------------------------------------------------------------------------------

-- isUnblocked :: NCofArg => IS.Set -> Bool
-- isUnblocked is =
--   IS.foldrAccum
--     (\x hyp (!varset, !cof) ->
--        matchIVar (lookupNCof x cof)
--          (\x -> IS.member x varset || hyp (IS.insert x varset // cof))
--          True)
--     (mempty, ?cof)
--     False
--     (IS.delete01 is)

-- isUnblockedS :: SubArg => NCofArg => IS.Set -> Bool
-- isUnblockedS is = IS.foldrAccum
--   (\x hyp (!varset, !sub, !cof) ->
--      matchIVar (lookupSub x sub)
--        (\x -> matchIVar (lookupNCof x cof)
--          (\x -> IS.member x varset || hyp ((,,) $$! IS.insert x varset $$! sub $$! cof))
--          True)
--        True)
--   (mempty, ?sub, ?cof)
--   False
--   (IS.delete01 is)

-- insertI :: NCofArg => I -> IS.Set -> IS.Set
-- insertI i s = IS.insertI (appNCof ?cof i) s
-- {-# inline insertI #-}

-- neCofVars :: NeCof -> IS.Set
-- neCofVars = \case
--   NCEq i j    -> IS.insertI i $ IS.insertI j mempty
--   NCNEq i j   -> IS.insertI i $ IS.insertI j mempty
--   NCAnd c1 c2 -> neCofVars c1 <> neCofVars c2

-- ----------------------------------------------------------------------------------------------------
