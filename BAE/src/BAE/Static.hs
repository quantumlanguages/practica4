module BAE.Static where

  import qualified Data.List as List
  import BAE.Type.Type as Type
  import qualified BAE.Unifier as Unifier
  import qualified BAE.Sintax as Sintax

  type Ctxt = [(Sintax.Identifier, Type)]

  subst :: Ctxt -> Type.Substitution -> Ctxt
  subst [] _ = []
  subst ((x, t): cs) s = (x, Type.subst t s) : substCtxt cs s

  find :: Sintax.Identifier -> Ctxt -> Maybe Type
  find _ [] = Nothing
  find x ((y, t) : cs) if x == y then
                          Just t
                       else
                          find x cs

  type Constraint = [[Type, Type]]

  fresh' :: Type -> [Type] -> Type
  fresh' (T n) v = if List.elem (T n) vars v then
                        fresh' (T (succ n)) v
                      else
                        (T n)

  fresh :: [Type] -> Type
  fresh v = fresh' (T 0) v

  infer' :: ([Type], LC.Expr) -> ([Type], Ctxt, Type, Constraint)
  infer' (nv (Sintax.V x)) = let t = fresh nv
                               nv' = nv `union` [t]
                        in (nv' ,[(x, t)] ,t , [])
  infer' (nv, (Sintax.L x e)) = let (nv', g, t, r) = infer' (nv, e)
                            in case find x g of
                              Just t' -> (nv', g \\ [(x, t')], t' :-> t, r)
                              Nothing -> let t' = fresh nv'
                                          nv'' = nv' `List.union` [t']
                                         in
                                          (nv'', g, t' :-> t, r)
  infer' (nv, (Sintax.App e1 e2)) = let (nv1, g1, t1, r1) = infer' (nv, e1)
                                    (nv2, g2, t2, r2) = infer' (nv1, e2)
                                    s = [(s1, s2) | (x, s1) <- g1, (y, s2) <- g2, x == y]
                                    z = fresh nv2 --item para operadores
                                    nv' = nv2 `List.union` [z]
                                in
                                    (nv', g1 `List.union` g2, z, r1 `List.union` r2 `Lista.union` s `Lista.union` [(t1, t2 :-> z)]) --items

  infer :: (LC.Expr) -> (Ctxt, Type)
  infer e = let (_, g, t, r) = infer' ([], e)
                umg = Unifier.µ r
            in
                (substCtxt g umg, subst t umg)
