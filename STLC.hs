data Ty =
    Boolean
  | Func Ty Ty
  deriving (Eq, Show)


-- note: nameless  (using de Brujin indices)
data Term =
    Var Int
  | Abs Ty Term   -- lam x: T. t
  | App Term Term
  | Tr
  | Fl
  | If Term Term Term
  deriving (Eq, Show)

type Ctx = [Ty]

readVar :: Ctx -> Int -> Ty
readVar = (!!)

-- addCtx :: Ctx -> Ty -> Ctx
-- addCtx ctx ty = ctx ++ [ty]

typeOf :: Ctx -> Term -> Maybe Ty
typeOf ctx (Var k) = return $ readVar ctx k
typeOf ctx (Abs ty t) = do
  ty' <- typeOf (ty : ctx) t
  return $ Func ty ty'

typeOf ctx (App t1 t2) = do
  Func ty1 ty2 <- typeOf ctx t1
  ty1' <- typeOf ctx t2
  if ty1 == ty1' then return ty2
  else Nothing

typeOf ctx Tr = return Boolean
typeOf ctx Fl = return Boolean

typeOf ctx (If c t1 t2) = do
  cty <- typeOf ctx c
  if cty == Boolean then do
    ty1 <- typeOf ctx t1
    ty2 <- typeOf ctx t2
    if ty1 == ty2 then return ty1
    else Nothing 
  else Nothing

infixl <**>
(<**>) :: Term -> Term -> Term
(<**>) = App

infixr 8 ==>
(==>) :: Ty -> Term -> Term
(==>) = Abs

double = Func Boolean Boolean ==> Boolean ==> Var 1 <**> (Var 1 <**> Var 0)


test1 () = do
  print double
  print $ typeOf [] double


