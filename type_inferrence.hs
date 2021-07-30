data Ty =
    BoolTy
  | FuncTy Ty Ty
  | TVar Int       -- 型変数 整数ID
  deriving (Eq)

instance Show Ty where
  show (FuncTy ty1 ty2) = "(" ++ show ty1 ++ " -> " ++ show ty2 ++ ")"
  show (TVar k) = "T" ++ show k
  show BoolTy = "Bool"

-- note: nameless  (using de Brujin indices)
data Term =
    Var Int
  | Abs Ty Term   -- lam x: T. t
  | AbsInf Term   -- lam x. t
  | App Term Term
  | Tr
  | Fl
  | If Term Term Term
  deriving (Eq, Show)

-- 制約 (型方程式)
data Constraint = Constraint Ty Ty
  deriving (Eq)

instance Show Constraint where
  show (Constraint ty1 ty2) = show ty1 ++ " = " ++ show ty2

(===) = Constraint


type Ctx = [Ty]
type TVarEnv = Int -- 変数の数をカウントする

readVar :: Ctx -> Int -> Ty
readVar = (!!)

-- フレッシュ型変数を生成する
genTVar :: TVarEnv -> (Ty , TVarEnv)
genTVar tvenv =
  (TVar tvenv , tvenv+1)

-- 制約付き型付け
cTyping :: TVarEnv -> Ctx -> Term -> (Ty , TVarEnv , [Constraint])
cTyping tvenv ctx (Var k) = (readVar ctx k , tvenv , [])

cTyping tvenv ctx (Abs ty t) =
  let (ty1 , tvenv1 , c1) = cTyping tvenv (ty : ctx) t in
  (FuncTy ty ty1 , tvenv1 , c1)

cTyping tvenv ctx (AbsInf t) =
  let (newTVar , newEnv) = genTVar tvenv in
  let (ty1 , tvenv1 , c1) = cTyping newEnv (newTVar : ctx) t in
  (FuncTy newTVar ty1 , tvenv1 , c1)

cTyping tvenv ctx (App t1 t2) =
  let (ty1 , tvenv1 , c1) = cTyping tvenv ctx t1 in
  let (ty2 , tvenv2 , c2) = cTyping tvenv1 ctx t2 in
  let (newTVar , newEnv) = genTVar tvenv2 in
  let c' = Constraint ty1 $ FuncTy ty2 newTVar in
  (newTVar , newEnv , c' : c1 ++ c2)

cTyping tvenv ctx Tr = (BoolTy , tvenv , [])
cTyping tvenv ctx Fl = (BoolTy , tvenv , [])

cTyping tvenv ctx (If t1 t2 t3) =
  let (ty1 , tvenv1 , c1) = cTyping tvenv ctx t1 in
  let (ty2 , tvenv2 , c2) = cTyping tvenv1 ctx t2 in
  let (ty3 , tvenv3 , c3) = cTyping tvenv2 ctx t3 in
  let c'1 = Constraint ty2 ty3 in
  let c'2 = Constraint ty1 BoolTy in
  (ty2 , tvenv3 , c'1 : c'2 : c1 ++ c2 ++ c3 )

-- 代入  [X |-> T] :: Ty -> Ty
type Subst = Ty -> Ty

-- [X |-> T]
(|->) :: Int -> Ty -> Subst
(k |-> ty) BoolTy = BoolTy

(k |-> ty) (FuncTy ty1 ty2) =
  let t'1 = (k |-> ty) ty1 in
  let t'2 = (k |-> ty) ty2 in
  FuncTy t'1 t'2

(k |-> ty) (TVar x) =
  if k == x then ty
  else TVar x

-- X in Fv(T) ?
contain :: Int -> Ty -> Bool
contain x (TVar k) = k == x
contain x BoolTy = False
contain x (FuncTy ty1 ty2) =
  contain x ty1 || contain x ty2

-- apply subst to all constraint of C
substC :: Subst -> [Constraint] -> [Constraint]
substC f = map (\(Constraint tl tr) -> Constraint (f tl) (f tr))

-- 主要解計算アルゴリズム
unify :: [Constraint] -> Maybe Subst
unify [] = return id
unify ((Constraint tl tr) : c') =
  case (tl , tr) of
    (TVar x , t)
      | contain x t -> Nothing
      | otherwise ->
          let sig = (x |-> t) in
          unify (substC sig c') >>= \f -> return $ f . sig

    (t , TVar x)
      | contain x t -> Nothing
      | otherwise ->
          let sig = (x |-> t) in
          unify (substC sig c') >>= \f -> return $ f . sig

    (FuncTy s1 s2, FuncTy t1 t2) ->
      unify (s1 === t1 : s2 === t2 : c')

    _  
      | tl == tr  -> unify c'
      | otherwise -> Nothing


-- 型推論器 主要型を出力 FV(t) = empty を仮定
typeInfer :: Term -> Maybe Ty

typeInfer term =
  let (ty , _ , cs) = cTyping 0 [] term in
  unify cs >>= \f -> return $ f ty


-- 型コンテキストへの代入
substCtx :: Subst -> Ctx -> Ctx
substCtx = map

substTerm :: Subst -> Term -> Term
substTerm f (Abs ty t) = Abs (f ty) (substTerm f t)
substTerm f (App t1 t2) = substTerm f t1 <**> substTerm f t2
substTerm f (AbsInf t) = AbsInf $ substTerm f t
substTerm f (If t1 t2 t3) = If (substTerm f t1) (substTerm f t2) (substTerm f t3)
substTerm _ t = t

-- 型推論器の段階的アルゴリズム
typeInfer2 :: TVarEnv -> Ctx -> Term -> Maybe (Ty , Subst , TVarEnv)

typeInfer2 tvenv ctx t = case t of

  Tr -> return (BoolTy , id , tvenv)
  Fl -> return (BoolTy , id , tvenv)

  Var k -> return (readVar ctx k , id , tvenv)

  Abs ty t -> do
    (ty1 , f , tvenv1) <- typeInfer2 tvenv (ty : ctx) t
    return (f (FuncTy ty ty1), f , tvenv1)

  AbsInf t -> do
    (newTVar , newEnv) <- return $ genTVar tvenv
    (ty1 , f , tvenv1) <- typeInfer2 newEnv (newTVar : ctx) t
    return (f (FuncTy newTVar ty1), f , tvenv1)

  App t1 t2 -> do
    (ty1 , f1 , tvenv1) <- typeInfer2 tvenv ctx t1
    let ctx1 = substCtx f1 ctx
    (ty2 , f2 , tvenv2) <- typeInfer2 tvenv1 ctx1 t2
    let f' = f1 . f2
    [ty1 , ty2] <- return $ map f' [ty1 , ty2]
    (newTVar , newEnv) <- return $ genTVar tvenv2
    let c = Constraint ty1 $ FuncTy ty2 newTVar
    sig <- unify [c]
    f'' <- return $ sig . f'
    return (f'' newTVar , f'' , newEnv)


  If t1 t2 t3 -> do
    (ty1 , f1 , tvenv1) <- typeInfer2 tvenv ctx t1
    let ctx1 = substCtx f1 ctx
    (ty2 , f2 , tvenv2) <- typeInfer2 tvenv1 ctx1 t2
    let ctx2 = substCtx f2 ctx1
    (ty3 , f3 , tvenv3) <- typeInfer2 tvenv2 ctx2 t3
    let f' = f3 . f2 . f1
    [ty1 , ty2 , ty3] <- return $ map f' [ty1 , ty2 , ty3]
    let c1 = Constraint ty2 ty3
    let c2 = Constraint ty1 BoolTy
    sig <- unify [c1 , c2]
    return (sig . f' $ ty2 , sig . f' , tvenv3)


infixl <**>
(<**>) = App

infixr 8 ==>
(==>) = Abs

lam = AbsInf

-- \f -> \x -> f (f x)
double = FuncTy (TVar 0) (TVar 0) ==> TVar 0 ==> Var 1 <**> (Var 1 <**> Var 0)

doubleInf = lam $ lam $ Var 1 <**> (Var 1 <**> Var 0)

-- \x: X -> \y: Y -> \z: Z -> x z $ y z
t1 = TVar 0 ==> TVar 1 ==> TVar 2 ==> (Var 2 <**> Var 0) <**> (Var 1 <**> Var 0)

-- \x -> \y -> \z -> x z $ y z
t1Inf = lam $ lam $ lam (Var 2 <**> Var 0) <**> (Var 1 <**> Var 0)

-- id
t2 = lam $ Var 0

t3 = lam $ TVar 0 ==> Var 1 <**> (Var 0 <**> Tr)

t4 = lam $ If Tr Fl (Var 0 <**> Fl)

-- \x: X -> \y: X -> \z: Y -> (if z (\_ -> y) (id)) z
-- Bool -> Bool -> Bool -> Bool
-- t5 = Abs (TVar 0) (Abs (TVar 0)) 
t5 = TVar 0 ==> TVar 0 ==> TVar 1 ==> Var 0 <**> If (Var 0) (lam $ Var 2) (lam $ Var 0)


test1 () = do
  -- print double
  -- (ty , env , cons) <- return (cTyping 1 [] double)
  -- putStrLn $ show ty ++ "\n" ++ unlines (map show cons)

  -- print "--------------------------"
  -- print $ cTyping 3 [] t1

  print "--------------------------"
  (ty , env , cons) <- return (cTyping 0 [] double)
  putStrLn $ show ty ++ "\n" ++ unlines (map show cons)
  print $ "primary type : " ++ show (typeInfer doubleInf)

  print "--------------------------"
  Just (ty, _, _) <- return $ typeInfer2 0 [] doubleInf
  print $ "primary type : " ++ show ty

  -- print "--------------------------"
  -- (ty , env , cons) <- return (cTyping 0 [] t1Inf)
  -- putStrLn $ show ty ++ "\n" ++ unlines (map show cons)
  -- print $ "primary type : " ++ show (typeInfer t1Inf)

  -- print "--------------------------"
  -- let Just (ty, _, _) = typeInfer2 0 [] t1Inf
  -- print $ "primary type : " ++ show ty

  -- print "--------------------------"
  -- let Just (ty, _, _) = typeInfer2 0 [] t2
  -- print $ "primary type : " ++ show ty

  -- print "--------------------------"
  -- let Just (ty, _, _) = typeInfer2 0 [] t3
  -- print $ "primary type : " ++ show ty

  -- print "--------------------------"
  -- Just (ty, _, _) <- return $ typeInfer2 0 [] t4
  -- print $ "primary type : " ++ show ty

  -- print "--------------------------"
  -- Just (ty, _, _) <- return $ typeInfer2 1 [] t5
  -- print $ "primary type : " ++ show ty

