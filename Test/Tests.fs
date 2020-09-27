
module Tests

open System
open Xunit
open Joynalyzer

type ValidResult = | List of List<RequiredResult> | Single of RequiredResult

let isNothing (r: RequiredResult) = match r with
    | Nothing -> true
    | _ -> false

let rec IgnoreNothings l: ValidResult = match (List.filter (fun x -> not (isNothing x)) l) with
    | l :: [] -> Single l
    | s -> List s


[<Fact>]
let Implications() =
   let example = (Implication(Symbol("P"), Symbol("Q")))
   let res = Eval.GetRequirementsForExpression example false;
   let expected = All ([ SymbolToHave("P", true); SymbolToHave("Q", false) ])
   Assert.Equal(expected, res)
   let example1 = (Negation example)
   let res = Eval.GetRequirementsForExpression example1 true;
   Assert.Equal(expected, res)

   let res1 = Eval.GetRequirementsForExpression example true;
   let expected1 = Any ([
       (All ([ SymbolToHave("P", true); SymbolToHave("Q", true) ]));
       (All ([ SymbolToHave("P", false); SymbolToHave("Q", false) ]));
       (All ([ SymbolToHave("P", false); SymbolToHave("Q", true) ]));
   ])
   Assert.Equal(expected1, res1)

   let example = (Implication(Symbol("P"), Or(Symbol("Q"), Symbol("P"))))
   let expected = All ([
       SymbolToHave("P", true);
       (All ([ SymbolToHave("Q", false); SymbolToHave("P", false) ]));
   ])
   let res = Eval.GetRequirementsForExpression example false;
   Assert.Equal(expected, res)

[<Fact>]
let HasAnyContradiciton() =
   let case = Eval.HasAnyContraction (RequiredResult.All ([
                                                                   RequiredResult.SymbolToHave("A", true);
                                                                   RequiredResult.SymbolToHave("A", false)
                                                               ]))
   Assert.Equal((true, Map.empty), case)

   let case = Eval.HasAnyContraction (RequiredResult.All ([
                                                                   RequiredResult.SymbolToHave("A", false);
                                                                   RequiredResult.SymbolToHave("A", false)
                                                               ]))
   Assert.Equal((false, Map.add "A" false Map.empty), case)
   let (hasContradictions, _) = Eval.GetRequirementsForExpression (And((Negation(Symbol "C")), (Symbol "C"))) true |> Eval.HasAnyContraction;
   Assert.True hasContradictions

   let example = (Negation(Implication(Symbol("P"), Or(Symbol("P"), Symbol("Q")))))
   let res = Eval.GetRequirementsForExpression example true;
   Assert.True (res |> Eval.HasAnyContraction |> fst)

   let res = Eval.GetRequirementsForExpression example false;

   let expected = Any ([ All
     [ SymbolToHave("P", true);
      Any [ SymbolToHave("P", true); SymbolToHave("Q", true) ] ];
   All
     [ SymbolToHave("P", false);
      All [ SymbolToHave("P", false); SymbolToHave("Q", false) ] ];
   All
     [ SymbolToHave("P", false);
      Any [ SymbolToHave("P", true); SymbolToHave("Q", true) ] ] ])
   Assert.Equal(expected, res)
   Assert.False (res |> Eval.HasAnyContraction |> fst)

[<Fact>]
let analyze_required_and() =
    let analyze s = Eval.GetRequirementsForExpression s;
    Assert.Equal (All ([ Nothing; SymbolToHave("A", true) ]),
                 analyze (And((Constant true), (Symbol "A"))) true)
    Assert.Equal (RequiredResult.All [ Nothing; All ([ SymbolToHave("A", true); SymbolToHave("B", true) ]) ],
                 analyze (And((Constant true), (And((Symbol "A"), (Symbol "B"))))) true)

    let result = analyze (And((And(Symbol("A"), Constant(true))), (And(Constant(true), (Constant true))))) true;
    let expected = RequiredResult.All([ RequiredResult.SymbolToHave("A", true) ] @ [ Nothing; Nothing ])
    Assert.Equal(expected, result)

    Assert.Equal (All [ All [ SymbolToHave("C", true); SymbolToHave("A", true) ]; All [ Nothing; Nothing ] ],
                 analyze (And((And((Constant true), (Symbol "C"))), (And((Symbol "A"), (Constant true))))) true)

    Assert.Equal (All [ SymbolToHave("C", false); SymbolToHave("C", true) ],
                 analyze (And((Negation(Symbol "C")), (Symbol "C"))) true)

    Assert.Equal (All [ SymbolToHave("C", true); SymbolToHave("C", true) ],
                 analyze (And((Symbol "C"), (Symbol "C"))) true)

    let result = analyze (And(
                                  (And(Symbol("A"), Symbol("B"))),
                                  (And(Symbol("A"), (Negation(Symbol("B")))))
                              )) true;
    let expected = RequiredResult.All([ RequiredResult.SymbolToHave("A", true) ] @ [ Nothing ])
    Assert.Equal(expected, result)


[<Fact>]
let analyze_required_or() =
    let analyze = Eval.GetRequirementsForExpression;
    Assert.Equal (Any ([ SymbolToHave("B", true); SymbolToHave("A", true) ]),
                 analyze (Or((Symbol "B"), (Symbol "A"))) true)

    let result = analyze (Or(
                                  (And(Symbol("A"), Symbol("B"))),
                                  (And(Symbol("A"), (Negation(Symbol("B")))))
                              )) true;
    let expected = RequiredResult.Any
                       ([
                           (All ([ RequiredResult.SymbolToHave("A", true); RequiredResult.SymbolToHave("B", true) ]));
                           (All ([ RequiredResult.SymbolToHave("A", true); RequiredResult.SymbolToHave("B", false) ]))
                           ])
    Assert.Equal(expected, result)

    let result = analyze (Or(
                                  (And(Symbol("A"), (Or(Symbol("B"), Symbol("C"))))),
                                  (And(Symbol("A"), (Negation(Symbol("B")))))
                              )) true;
    let expected = RequiredResult.Any
                       ([
                           (All ([ RequiredResult.SymbolToHave("A", true); Any ([ RequiredResult.SymbolToHave("B", true); SymbolToHave("C", true) ]) ]))
                           (All ([ RequiredResult.SymbolToHave("A", true); RequiredResult.SymbolToHave("B", false) ]))
                           ])
    Assert.Equal(expected, result)

[<Fact>]
let AnyContradiction() =
    Any [
        All [ SymbolToHave("T", true); SymbolToHave("T", false) ]
        All [ SymbolToHave("T", true); SymbolToHave("T", true) ]
        All [ SymbolToHave("T", false); SymbolToHave("T", true) ]
    ] |> Eval.HasAnyContraction
      |> fst
      |> Assert.False

    Any [
        All [ SymbolToHave("T", true); SymbolToHave("T", false) ]
        All [ SymbolToHave("T", false); SymbolToHave("T", true) ]
    ] |> Eval.HasAnyContraction
      |> fst
      |> Assert.True

    All [
        All [ SymbolToHave("T", true); SymbolToHave("F", false) ]
        All [ SymbolToHave("T", false); SymbolToHave("F", false) ]
    ] |> Eval.HasAnyContraction
      |> fst
      |> Assert.True


[<Fact>]
let Analyze() =
   Negation(Implication(Symbol("P"), Or(Symbol("P"), Symbol("Q"))))
    |> Eval.Analyze
    |> fun x -> Assert.Equal(Result.Contradiction, x)

   Negation(Implication(Or(Implication(Symbol "P", Symbol "Q"), Symbol("P")), Symbol "Q"))
    |> Eval.Analyze
    |> fun x -> Assert.Equal(Result.Contradiction, x)

   Negation(Implication(Or(Symbol "P", And(Symbol "P", Symbol "Q")), Symbol "P"))
    |> Eval.Analyze
    |> fun x -> Assert.Equal(Result.Contradiction, x)

   Negation(Implication(Or(Symbol "P", Symbol "Q"), Symbol "Q"))
    |> Eval.Analyze
    |> fun x -> Assert.Equal(Result.Contingency, x)

   Implication (
                    Implication(Symbol "P", Symbol "Q"),
                    Implication(
                                    Implication(Symbol "P", Negation(Symbol "Q")),
                                    Negation(Symbol "P")
                                ))
        |> Eval.Analyze
        |> fun x -> Assert.Equal(Result.Tautology, x)

   // 2) C  Lista 3
   Negation(And(
                      Implication(Symbol "P", (And(Symbol "Q", Negation(Symbol "Q")))),
                      Symbol "P"
                  ))
        |> Eval.Analyze
        |> fun x -> Assert.Equal(Result.Tautology, x)

   Implication (
                    Implication(Symbol "P", Symbol "Q"),
                    Implication(
                                    Implication(Symbol "P", Negation(Symbol "Q")),
                                    Negation(Symbol "P")
                                ))
        |> Eval.Analyze
        |> fun x -> Assert.Equal(Result.Tautology, x)
