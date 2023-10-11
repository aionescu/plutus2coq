module Lambda where

type Name = Int

data Expr
  = Var Name
  | Let Name Expr Expr
  | Lam Name Expr
  | App Expr Expr

-- Data.Foldable.maximum is a partial function (fails when the list is empty)
-- So we use a total version that requires a nonempty list.
maxName :: Name -> [Name] -> Name
maxName n ns = foldr max n ns

maxVar :: Expr -> Int
maxVar (Var n)       = n
maxVar (Let n e1 e2) = maxName n [maxVar e1, maxVar e2]
maxVar (Lam n e)     = maxName  n [maxVar e]
maxVar (App e1 e2)   = maxName (maxVar e1) [maxVar e2]

fresh :: Expr -> Int
fresh e = 1 + maxVar e

anf :: Expr -> Expr
anf (Var n)          = Var n
anf (Let n rhs body) = Let n (anf rhs) (anf body)
anf (Lam n body)     = Lam n (anf body)
anf (App f (Var n))  = App (anf f) (Var n)
anf (App f e)        = Let v (anf e) (App (anf f) (Var v))
  where v = fresh f
