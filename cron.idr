module Cron

import Data.Fin
import Lightyear
import Lightyear.Char
import Lightyear.Strings

data Restriction = MinutesR | HoursR | DayMonthR | MonthR | DayWeekR | YearR

total
restrictionToNat : Restriction -> Nat
restrictionToNat MinutesR = 60
restrictionToNat HoursR = 24
restrictionToNat DayMonthR = 32
restrictionToNat MonthR = 13
restrictionToNat DayWeekR = 7
restrictionToNat YearR = 2100

Minutes : Type
Minutes = Fin (restrictionToNat MinutesR)

Hours : Type
Hours = Fin (restrictionToNat HoursR)

DayMonth : Type
DayMonth = Fin (restrictionToNat DayMonthR)

Month : Type
Month = Fin (restrictionToNat MonthR)

DayWeek : Type
DayWeek = Fin (restrictionToNat DayWeekR)

Year : Type
Year = Fin (restrictionToNat YearR)

data CronExpression : Type -> Type where
  CronSingle : (restriction : ty) -> CronExpression ty
  CronRange : (range : (ty, ty)) -> CronExpression ty
  CronEnum : (enum : List ty) -> CronExpression ty
  CronAny : CronExpression ty

record Cron where
  constructor MkCron
  minutes : CronExpression Minutes
  hours : CronExpression Hours
  dayMonth : CronExpression DayMonth
  month : CronExpression Month
  dayWeek : CronExpression DayWeek
  year : CronExpression Year

parseNumber : Parser Nat
parseNumber = map (\t => the Nat (cast (pack t))) (some (satisfy isDigit))

parseNumberExpression : (n : Nat) -> Parser (CronExpression Nat)
parseNumberExpression n = (token "-" *> map (\c => CronRange (n, c) ) parseNumber) <|>
                          (token "," *> map (\list => CronEnum (n :: list)) (sepBy1 parseNumber (token ","))) <|>
                          pure (CronSingle n)

verifyCronExpression : (rest : Restriction) -> CronExpression Nat -> Parser (CronExpression (Fin (restrictionToNat rest)))
verifyCronExpression rest (CronSingle n) = case natToFin n (restrictionToNat rest) of
                                                Nothing => fail "Out of bounds"
                                                (Just x) => pure $ CronSingle x
verifyCronExpression rest (CronRange (a, b)) = (case natToFin a (restrictionToNat rest) of
                                                     Nothing => fail "Out of bounds"
                                                     (Just x) => (case natToFin b (restrictionToNat rest) of
                                                                       Nothing => fail "Out of bounds"
                                                                       (Just y) => pure $ CronRange (x, y)))
verifyCronExpression rest (CronEnum enum) = let listOfMaybe = map verifyItem enum in
                                            let maybeList = foldr (liftA2 (::)) (Just []) listOfMaybe in
                                                (case maybeList of
                                                      Nothing => fail "Out of bounds"
                                                      (Just x) => pure $ CronEnum x)
  where
    verifyItem : Nat -> Maybe (Fin (restrictionToNat rest))
    verifyItem k = natToFin k (restrictionToNat rest)

verifyCronExpression rest CronAny = pure CronAny

parseCronExpression : (rest : Restriction) -> Parser (CronExpression (Fin (restrictionToNat rest)))
parseCronExpression rest = token "*" >!= (\t => pure CronAny) <|>
                           parseNumber >>= parseNumberExpression >>= verifyCronExpression rest

parseCron : Parser Cron
parseCron = do minutes <- parseCronExpression MinutesR
               spaces
               hours <- parseCronExpression HoursR
               spaces
               dayMonth <- parseCronExpression DayMonthR
               spaces
               month <- parseCronExpression MonthR
               spaces
               dayWeek <- parseCronExpression DayWeekR
               spaces
               year <- parseCronExpression YearR
               pure $ MkCron minutes hours dayMonth month dayWeek year

strToCron : String -> Either String Cron
strToCron str = parse parseCron str
