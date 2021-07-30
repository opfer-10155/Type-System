-- 項の情報 (何行目の何文字目か)
data Info = Info {
  line :: Int,
  chara :: Int
}

-- data Term =
--     Tru
--   | Fal
--   | Zero
--   | Succ  Term
--   | If    Term Term Term
--   | IsZero Term

-- Terms with infomation
data TermI =
    Tru   Info
  | Fal   Info
  | Zero  Info
  | Succ  TermI Info
  | If    TermI TermI TermI Info
  | IsZero TermI Info

data Val =
    TruV
  | FalV
  | ZeroV
  | SuccV Val


-- removeInfo :: TermI -> Term

isNum :: TermI -> Bool
isNum (Zero _) = True
isNum (Succ t _) = isNum t
isNum _ = False

isNumV :: Val -> Bool
isNumV ZeroV = True
isNumV (SuccV n) = isNumV n
isNumV _ = False


isVal :: TermI -> Bool
isVal (Tru _) = True
isVal (Fal _) = True
isVal (Zero _) = True
isVal (Succ t _) = isVal t
isVal _ = False

getInfo :: TermI -> Info
getInfo (Tru info) = info
getInfo (Fal info) = info
getInfo (Zero info) = info
getInfo (Succ _ info) = info
getInfo (If _ _ _ info) = info
getInfo (IsZero _ info) = info


-- 1ステップ評価
eval1 :: TermI -> Either (String , Info) TermI
eval1 (Succ t info) = do
  t' <- eval1 t
  return (Succ t' info)
eval1 (If (Tru _) t2 t3 info) = Right t2
eval1 (If (Fal _) t2 t3 info) = Right t3
eval1 (If t1 t2 t3 info) =
  eval1 t1 >>= \t1' -> Right (If t1' t2 t3 info)
eval1 (IsZero (Zero _) info) = Right (Tru info)
eval1 (IsZero (Succ _ _) info) = Right (Fal info)
eval1 (IsZero t info) =
  eval1 t >>= \t' -> Right (IsZero t' info)
eval1 t = Left ("No Rule" , getInfo t)


-- 大ステップ評価
eval :: TermI -> Either (String , Info) Val
eval (Tru _) = Right TruV
eval (Fal _) = Right FalV
eval (Zero _) = Right ZeroV
eval (Succ t info) =
  eval t >>= \v ->
    if isNumV v then
      Right (SuccV v)
    else
      Left ("Not Number" , info)
eval (If t1 t2 t3 info) =
  eval t1 >>= \v -> case v of
    TruV -> eval t2
    FalV -> eval t3
    _ -> Left ("Not Bool" , info)
eval (IsZero t info) =
  eval t >>= \v -> case v of
    ZeroV -> Right TruV
    (SuccV n) -> Right FalV
    _ -> Left ("Not Number" , info)


