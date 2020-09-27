namespace Joynalyzer

type public Result = Tautology | Contradiction | Contingency

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


module Eval =
    let HasAnyContradiction (r: RequiredResult): bool * Map<string, bool> =
        let rec innerHasAnyContradiction (state: Map<string, bool>) v = match v with
         | SymbolToHave(t, v) -> match Map.tryFind t state with
            | Some(x) -> (not x = v, state)
            | None -> (false, (Map.add t v state))
         | All(x) -> match (List.fold (fun (s: bool * Map<string, bool>) next -> match s with
                                | (true, _) -> (true, state)
                                | (false, s) -> innerHasAnyContradiction s next
                                ) (false, state) x) with
            | (true, _) -> (true, state)
            | s -> s
         | Any(x) -> match (List.fold (fun (s: bool * Map<string, bool>) next -> match s with
                                | (false, s) -> (false, s)
                                | (true, _) -> innerHasAnyContradiction state next
                                ) (true, state) x) with
            | (true, _) -> (true, state)
            | s -> s
         | _ -> (false, state)
        innerHasAnyContradiction Map.empty r
    let rec GetRequirementsForExpression (exp: Expression) (r: bool): RequiredResult =
        match exp with
        | And(left, right) -> match r with
            | false -> Any ([
                                              (All ([ (GetRequirementsForExpression left false); (GetRequirementsForExpression right false) ]))
                                              (All ([ (GetRequirementsForExpression left true); (GetRequirementsForExpression right false) ]))
                                              (All ([ (GetRequirementsForExpression left false); (GetRequirementsForExpression right true) ]))
                                              ])
            | true -> All [ (GetRequirementsForExpression left true); (GetRequirementsForExpression right true) ]
        | Symbol(t) -> SymbolToHave(t, r)
        | Constant(v) -> if v = r then Nothing else Impossible
        | Negation(t) -> GetRequirementsForExpression t (not r)
        | Or(left, right) -> match r with
            | true -> Any [ (GetRequirementsForExpression left true); (GetRequirementsForExpression right true) ]
            | false -> All [ (GetRequirementsForExpression left false); (GetRequirementsForExpression right false) ]
        | Implication(s, v) -> match r with
            | true -> Any ([
                (All ([ (GetRequirementsForExpression s true); (GetRequirementsForExpression v true) ]))
                (All ([ (GetRequirementsForExpression s false); (GetRequirementsForExpression v false) ]))
                (All ([ (GetRequirementsForExpression s false); (GetRequirementsForExpression v true) ]))
                ])
            | false -> All ([ (GetRequirementsForExpression s true); (GetRequirementsForExpression v false) ])
        | Equivalence(s, v) -> match r with
            | true -> Any ([
                (All ([ (GetRequirementsForExpression s true); (GetRequirementsForExpression v true) ]));
                (All ([ (GetRequirementsForExpression s false); (GetRequirementsForExpression v false) ]));
            ])
            | false -> Any ([
               (All ([ (GetRequirementsForExpression s false); (GetRequirementsForExpression v true) ]));
               (All ([ (GetRequirementsForExpression s true); (GetRequirementsForExpression v false) ]));
            ])
    let Analyze (expression: Expression) =
        let r1 = GetRequirementsForExpression expression true 
        let r2 = GetRequirementsForExpression expression false 
        match (r1 |> HasAnyContradiction, r2 |> HasAnyContradiction) with
            | (s1, s2) -> match (s1 |> fst, s2 |> fst) with
                | (false, false) -> Contingency
                | (true, false) -> Contradiction
                | _ -> Tautology
