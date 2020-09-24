module Tests

open System
open Xunit
open joynalyzer
open joynalyzer

[<Fact>]
let analyze_tautlogy() =
    let analyze s = Joynalizer.analyze (Joynalizer.Exp s);
    Assert.Equal(Tautology, analyze (Constant true))
    
[<Fact>]
let analyze_required() =
    let analyze s = Joynalizer.get_required_for_for_result s;
    Assert.Equal(RequiredResult.Nothing, analyze (Constant true) true)
    
[<Fact>]
let analyze_required_and() =
    let analyze s = Joynalizer.get_required_for_for_result s;
    Assert.Equal(SymbolToHave ("A", true),
                 analyze (And ((Constant true), (Symbol "A"))) true)
    Assert.Equal(RequiredResult.All [ SymbolToHave ("A", true); SymbolToHave("B", true) ],
                 analyze (And ((Constant true), (And ((Symbol "A"), (Symbol "B"))))) true)
    
    Assert.Equal(RequiredResult.All [ SymbolToHave ("C", true); SymbolToHave ("A", true) ],
                 analyze (And ((And ((Constant true), (Symbol "C"))), (And ((Symbol "A"), (Constant true))))) true)
