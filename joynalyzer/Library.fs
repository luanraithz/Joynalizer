namespace joynalyzer

type public Result = | Tautology | Contradiction | Contingency

type Expression =
     | Symbol of string
     | Constant of bool
     | Negation of Expression
     | Or of Expression * Expression
     | And of Expression * Expression
     | Implication of Expression * Expression
     | Equivalence of Expression * Expression

type RequiredResult =
    | SymbolToHave of string * bool
    | Any of List<RequiredResult>
    | All of List<RequiredResult>
    | Every of List<RequiredResult>
    | Impossible
    | Nothing

module Joynalizer =
    let rec get_required_for_for_result (exp: Expression) (r: bool): RequiredResult =
        match exp with
        | And(left, right) -> match (left, right, r) with
            | (Constant(false), _, true) -> Impossible
            | (_, Constant(false), true) -> Impossible
            | (Constant(true), Constant(true), true) -> Nothing
            | (Constant(true), Symbol(s), true) -> SymbolToHave(s, true)
            | (Symbol(s), Constant(true), true) -> SymbolToHave(s, true)
            | (Constant(false), Symbol(s), false) -> Any [ SymbolToHave(s, true); SymbolToHave(s, false) ]
            | (Constant(true), And(left, right), true) -> get_required_for_for_result (And(left, right)) true
            | (And(left, right), Constant(true), true) -> get_required_for_for_result (And(left, right)) true
            | (_, Constant(false), false) -> Nothing
            | (Symbol(s1), Symbol(s2), true) -> All [ SymbolToHave(s1, true); SymbolToHave(s2, true) ]
            | (And(exp1, exp2), And(exp3, exp4), true) -> (
                                                                    get_required_for_for_result (And(exp1, exp2))) @
                                                                    get_required_for_for_result (And(exp3, exp4)) true
                                                                ) with
                | (_, Impossible) -> Impossible
                | (Impossible, _) -> Impossible
                | (All(list1), All(list2)) -> All (list1 @ list2)
                | (All(list1), Any(list2)) -> Every ([All list1] @ [Any list2])
                | (Any(list1), All(list2)) -> Every ([Any list1] @ [All list2])
                | (Any(list1), Any(list2)) -> Every ([Any list1] @ [Any list2])
                | _ -> Impossible
            | _ -> Impossible
        | _ -> Impossible;
    let evalutate (ex: Expression) =
         match ex with
         | Constant(v) -> v
         | _ -> false

    type Entry = | Exp of Expression | String
    let analyze (name: Entry) =
        Tautology
