module Type (
  Type, Identifier,
  vars, subst, comp, simpl
) where

  import qualified Data.List as List

  type Identifier = Int
  infix :->

  data Type = T Identifier
       | Integer | Boolean
       | Type :-> Type deriving (Show, Eq)

  vars :: Type -> [Identifier]
  vars (T t) = [t]
  vars (t1 :-> t2) = List.union (vars t1) (vars t2)

  type Substitution = [(Identifier, Type)]

  subst :: Type -> Substitution -> Type
  subst (T t) s = case s of
                    []           -> T t
                    ((x, t'): ss) -> if x == t then
                                      t'
                                     else
                                      subst (T t) ss
  subst (t1 :-> t2) s = (subst t1 s) :-> (subst t2 s)

  comp :: Substitution -> Substitution -> Substitution
  comp s1 s2 = [(x, subst t s2) | (x, t) <- s1] `List.union` [(x, t) | (x, t) <- s2, List.notElem x [y | (y, t) <- s1]]

  simpl:: Substitution -> Substitution
  simpl s = filter filterS s

  filterS :: (Identifier, Type) -> Bool
  filterS (i, T t) = i /= t
  filterS _ = True
