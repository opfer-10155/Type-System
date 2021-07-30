-- 項の情報 (何行目の何文字目か)
data Info = Info {
  line :: Int,
  chara :: Int
}

type VarName = String
type CtxLen = Int
type Error = (String , Info)
type Ctx = [VarName]

-- using de Brujin indices
data Term =
    Var Int
  | Abs Term
  | App Term Term

-- Terms with Infomation
data TermI =
    TVar Int CtxLen Info
  | TAbs Term Info VarName
  | TApp Term Term Info

-- read variable
index2Name :: Env -> Int -> VarName
index2Name = (!!)

-- c番目より外側の変数をdだけシフトする。
shift :: Int -> Int -> Term -> Term
shift d c (Var k) | k < c = k
shift d c (Var k) | k >= c = k + d
shift d c (Abs t) = Abs $ shift d (c+1) t
shift d c (App t1 t2) = App (shift d c t1) (shift d c t2)

-- 代入 [x -> s]t
subst :: Int -> Term -> Term
subst x s (Var k)
  | k == x = s
  | otherwise = k
subst x s (Abs t) = Abs $ subst (j+1) (shift 1 0 s) t
subst x s (App t1 t2) = App (subst j s t1) (subst j s t2)


isVal :: Term -> Bool
isVal (Abs _) = True
isVal _ = False

-- evalの補助関数、一段階評価する
eval' :: Ctx -> Term -> Term
eval' ctx (App t1 t2)
  | isVal t1 && isVal t2 = subst 0 t2 t1
  | isVal t1             = App t1 (eval ctx t2)
  | otherwise            = App (eval ctx t1) t2

eval' ctx t = t

evalSub = eval'

-- 一段階評価して、valなら終了、そうでなければ続行
eval :: Ctx -> Term -> Term
eval ctx t =
  let t' = evalSub ctx t in
  if isval t' then t' else eval ctx t'


termToStr :: TermI -> Ctx -> Either String String

termToStr (Var k info len) ctx
  | k < len = Right $ index2Name ctx k
  | otherwise = Left ("Bad Index of var " ++ show k ++ " in context length " ++ show len , Info)

termToStr (Abs t _ x) ctx =
  Right $ "l " ++ x ++ " -> " ++ termToStr t

termToStr (App t1 t2 info) ctx =
  Right $ termToStr t1 ++ " $ " ++ termToStr t2


