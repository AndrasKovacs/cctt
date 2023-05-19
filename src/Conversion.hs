
module Conversion where

import Common
import Core
import CoreTypes
import Cubical

-- Note: neutral inputs (NeSys, Ne, NeSysHCom) are assumed to be forced
--       other things are not!
-- Also: neutral inputs may have different types!
----------------------------------------------------------------------------------------------------

class Conv a where
  conv :: NCofArg => DomArg => a -> a -> Bool

instance Conv Val where
  conv t t' = case frc t // frc t' of

    -- rigid match
    (VNe n _          , VNe n' _            ) -> conv n n'
    (VGlueTy a sys    , VGlueTy a' sys'     ) -> conv a a' && conv sys sys'
    (VPi a b          , VPi a' b'           ) -> conv a a' && conv b b'
    (VLam t           , VLam t'             ) -> conv t t'
    (VPath a t u      , VPath a' t' u'      ) -> conv a a' && conv t t' && conv u u'
    (VPLam _ _ t      , VPLam _ _ t'        ) -> conv t t'
    -- (VSg a b          , VSg a' b'           ) -> b^.name == b'^.name && conv a a' && conv b b'
    (VSg a b          , VSg a' b'           ) -> conv a a' && conv b b'
    -- (VWrap x a        , VWrap x' a'         ) -> x == x' && conv a a'
    (VWrap x a        , VWrap x' a'         ) -> conv a a'
    (VPair _ t u      , VPair _ t' u'       ) -> conv t t' && conv u u'
    (VU               , VU                  ) -> True
    (VLine a          , VLine a'            ) -> conv a a'
    (VLLam t          , VLLam t'            ) -> conv t t'
    (VTyCon inf ts    , VTyCon inf' ts'     ) -> inf^.tyId == inf'^.tyId && conv ts ts'
    (VHTyCon inf ts   , VHTyCon inf' ts'    ) -> inf^.tyId == inf'^.tyId && conv ts ts'
    (VDCon inf sp     , VDCon inf' sp'      ) -> inf^.conId == inf'^.conId && conv sp sp'
    (VGlue t eqs sys _, VGlue t' eqs' sys' _) -> conv t t' && conv eqs eqs' && conv sys sys'

    (VHDCon i _ fs s _, VHDCon i' _ fs' s' _) ->
      i^.conId == i'^.conId && conv fs fs' && conv s s'

    (VHCom r1 r2 a t b _, VHCom r1' r2' a' t' b' _) ->
      conv r1 r1' && conv r2 r2'  && conv a a' && conv t t' && conv b b'

    (VHole{}, _) -> True
    (_, VHole{}) -> True

    -- -- We keep track of evaluation contexts for holes.
    -- -- This prevents spurious conversions between holes.
    -- (VHole _ p s e  , VHole _ p' s' e'  ) -> p == p' && conv s s' && conv e e'

    -- -- Glue eta
    -- -- A bit ugly that we put "mempty"-s there, and potentially dodgy, but the only
    -- -- way conversion checking can succeed here is when the VNe-s are immediately consumed.
    -- (NGlue b sys fib  , t'                   ) -> conv b (VNe (NUnglue t' sys) mempty)
    -- (t                , NGlue b' sys' fib'   ) -> conv (VNe (NUnglue t sys') mempty) b'

    -- eta
    (VLam t           , t'                  ) -> fresh \x -> conv (t ∙ x) (t' ∙ x)
    (t                , VLam t'             ) -> fresh \x -> conv (t ∙ x) (t' ∙ x)
    (VPair x t u      , t'                  ) -> conv t (proj1 x t') && conv u (proj2 x t')
    (t                , VPair x t' u'       ) -> conv (proj1 x t) t' && conv (proj2 x t) u'
    (VPLam l r t      , t'                  ) -> freshI \i -> conv (t ∙ i) (papp l r t' i)
    (t                , VPLam l r t'        ) -> freshI \i -> conv (papp l r t i) (t' ∙ i)
    (VLLam t          , t'                  ) -> freshI \i -> conv (t ∙ i) (lapp t' i)
    (t                , VLLam t'            ) -> freshI \i -> conv (lapp t i) (t' ∙ i)
    (VPack x t        , t'                  ) -> conv t (unpack x t')
    (t                , VPack x t'          ) -> conv (unpack x t) t'
    (VGlue b sys fib _, t'                  ) -> conv b (ungluen t' sys)
    (t                , VGlue b' sys' fib' _) -> conv (ungluen t sys') b'

    (VSub{}, _     ) -> impossible
    (_     , VSub{}) -> impossible
    _                -> False

instance Conv a => Conv (WithIS a) where
  conv (WIS a _) (WIS a' _) = conv a a'
  {-# inline conv #-}

instance Conv Ne where

  conv t t' = case unSubNe t // unSubNe t' of
    (NLocalVar x     , NLocalVar x'      ) -> x == x'
    (NDontRecurse inf, NDontRecurse inf' ) -> inf^.recId == inf'^.recId
    (NApp t u        , NApp t' u'        ) -> conv t t' && conv u u'
    (NPApp l r t i   , NPApp l' r' t' i' ) -> conv t t' && conv i i'
    (NProj1 n _      , NProj1 n' _       ) -> conv n n'
    (NProj2 n _      , NProj2 n' _       ) -> conv n n'
    (NLApp t i       , NLApp t' i'       ) -> conv t t' && conv i i'

    (NCoe r1 r2 a t, NCoe r1' r2' a' t') ->
      conv r1 r1' && conv r2 r2' && conv a a' && conv t t'

    -- the types of the "a"-s can be different Glue-s a priori, that's
    -- why we first convert sys-es. Neutrals of different types can
    -- be converted, and then the type equality is part of the output,
    -- but the "a" here aren't neutrals!
    (NUnglue a sys    , NUnglue a' sys'      ) -> conv sys sys' && conv a a'

    (NCase t b tag cs , NCase t' b' tag' cs' ) -> conv t t' && conv b b' && convCases tag cs tag' cs'
    (NHCase t b tag cs, NHCase t' b' tag' cs') -> conv t t' && conv b b' && convHCases tag cs tag' cs'

    (NUnpack n _      , NUnpack n' _         ) -> conv n n'

    (NSub{} , _      ) -> impossible
    (t      , NSub{} ) -> impossible
    _                  -> False

convCases' :: NCofArg => DomArg => RecurseArg => Sub -> Env -> Cases -> Sub -> Env -> Cases -> Bool
convCases' sub env cs sub' env' cs' = case (cs, cs') of
  (CSNil            , CSNil             ) -> True
  (CSCons x xs t cs , CSCons _ _  t' cs') ->
    (case pushVars env xs of
      (!env, !dom) -> case pushVars env' xs of
        (!env', !_) ->
          let ?dom = dom in
          let v  = (let ?env = env ; ?sub = sub  in eval t ) in
          let v' = (let ?env = env'; ?sub = sub' in eval t') in
          conv v v')
    &&
    convCases' sub env cs sub' env' cs'
  _ ->
    impossible

convHCases' :: NCofArg => DomArg => RecurseArg => Sub -> Env -> HCases -> Sub -> Env -> HCases -> Bool
convHCases' sub env cs sub' env' cs' = case (cs, cs') of
  (HCSNil               , HCSNil               ) -> True
  (HCSCons x xs is t cs , HCSCons _ _ _  t' cs') ->
    (case pushVars env xs of
      (!env, !dom) -> case pushVars env' xs of
        (!env', !_) -> case pushIVars sub is of
          (!sub, !cof) -> case pushIVars sub' is of
            (!sub', _) ->
              let ?dom = dom in
              let ?cof = cof in
              let v  = (let ?env = env ; ?sub = sub  in eval t ) in
              let v' = (let ?env = env'; ?sub = sub' in eval t') in
              conv v v')
    &&
    convHCases' sub env cs sub' env' cs'
  _ ->
    impossible

convCases :: NCofArg => DomArg => CaseTag -> EvalClosure Cases -> CaseTag -> EvalClosure Cases -> Bool
convCases tag (EC sub env _ cs) tag' (EC sub' env' _ cs') = case (wkSub sub, wkSub sub') of
  (!sub, !sub') ->
    (tag == tag' && conv sub sub' && conv env env')
    ||
    (let ?recurse = DontRecurse
     in convCases' sub env cs sub' env' cs')

convHCases :: NCofArg => DomArg => CaseTag -> EvalClosure HCases -> CaseTag -> EvalClosure HCases -> Bool
convHCases tag (EC sub env _ cs) tag' (EC sub' env' _ cs') = case (wkSub sub, wkSub sub') of
  (!sub, !sub') ->
    (tag == tag' && conv sub sub' && conv env env')
    ||
    (let ?recurse = DontRecurse
     in convHCases' sub env cs sub' env' cs')

instance Conv NeCof where
  conv (NCEq i j) (NCEq i' j') = conv i i' && conv j j'

instance Conv VDSpine where
  conv sp sp' = case (sp, sp') of
    (VDNil         , VDNil           ) -> True
    (VDCons t sp   , VDCons t' sp'   ) -> conv t t' && conv sp sp'
    _                                  -> impossible

instance Conv a => Conv [a] where
  conv as as' = case (as, as') of
    ([], [])       -> True
    (a:as, a':as') -> conv a a' && conv as as'
    _              -> False
  {-# inline conv #-}

instance Conv (BindI Val) where
  conv t t' = freshI \i -> conv (t ∙ i) (t' ∙ i); {-# inline conv #-}

instance Conv (BindILazy Val) where
  conv t t' = freshI \i -> conv (t ∙ i) (t' ∙ i); {-# inline conv #-}

instance Conv a => Conv (BindCofLazy a) where
  conv t t' = conv (t^.binds) (t'^.binds)
           && assumeCof (t^.binds) (conv (t^.body) (t'^.body))
  {-# inline conv #-}

instance Conv a => Conv (BindCof a) where
  conv t t' = conv (t^.binds) (t'^.binds)
           && assumeCof (t^.binds) (conv (t^.body) (t'^.body))
  {-# inline conv #-}

instance Conv I where
  conv r r' = frc r == frc r'; {-# inline conv #-}

instance Conv Sub where
  conv (Sub _ _ s) (Sub _ _ s') = go s s' where
    go :: NCofArg => IList -> IList -> Bool
    go s s' = case (s, s') of
      (ILNil     , ILNil       ) -> True
      (ILDef is i, ILDef is' i') -> go is is' && conv i i'
      _                          -> False

instance Conv NeSys where
  conv t t' = case (t, t') of
    (NSEmpty      , NSEmpty        ) -> True
    (NSCons t sys , NSCons t' sys' ) -> conv t t' && conv sys sys'
    _                                -> False

instance Conv NeSysHCom where
  conv t t' = case (t, t') of
    (NSHEmpty      , NSHEmpty        ) -> True
    (NSHCons t sys , NSHCons t' sys' ) -> conv t t' && conv sys sys'
    _                                  -> False

instance Conv NamedClosure where
  conv t t' = fresh \x -> conv (t ∙ x) (t' ∙ x); {-# inline conv #-}

instance Conv NamedIClosure where
  conv t t' = freshI \i -> conv (t ∙ i) (t' ∙ i); {-# inline conv #-}

instance Conv NeCof' where
  conv (NeCof' _ c) (NeCof' _ c') = conv c c'
  {-# inline conv #-}

instance Conv Env where
  conv e e' = case (e, e') of
    (ENil     , ENil       ) -> True
    (EDef e t , EDef e' t' ) -> conv e e' && conv t t'
    _                        -> False
