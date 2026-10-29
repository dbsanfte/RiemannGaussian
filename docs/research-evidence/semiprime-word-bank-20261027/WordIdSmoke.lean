import RiemannGaussian.SemiprimeSourceWordIdPredicate
open RiemannGaussian
open SemiprimeSourceWordIdEnvironment SemiprimeSourceWordIdPredicate
open SemiprimeMaterializedScoreEnvironment (ScoreProgram)

def bank := SemiprimeSourceWordBank.acquire 2 1
def id0 := bank.ids[0]?.getD []
def id1 := bank.ids[1]?.getD []
def base := (initial id0 [id1,id0]).value
def earlier := (extend base (acquireKey 1).value id1).value
def newest := (extend earlier (acquireKey 1).value id0).value
def env := (extend newest (acquireKey 3).value id1).value
#eval (equalID [true] [true,false,false]).value
#eval (decide ((SemiprimeSourceWordIdEnvironment.read base (acquireKey 0).value).value=id0),
  decide ((SemiprimeSourceWordIdEnvironment.read env (acquireKey 1).value).value=id0),
  decide ((SemiprimeSourceWordIdEnvironment.read env (acquireKey 7).value).value=id0))
def programs : List (ScoreProgram 1) :=
  [.incidence 1 0 0 0,.incidence 3 0 2 0,.head 0 0 2,.head 0 3 2,.head 0 7 2]
#eval programs.map (fun p => ((terminal bank env p).value,
  (SemiprimeSourceScoreCounts.hit p
    (decodeEnvironment (SemiprimeSourceWordBankSemantics.decode 2 1) env)).value))
#eval (terminal_acquired 2 1 env (.head 0 3 2)).work > bank.clock
-- Empty rows still have meaningful acquired IDs and original incidence truth.
def emptyBank := SemiprimeSourceWordBank.acquire 2 0
def emptyEnv := (initial [] []).value
#eval (terminal emptyBank emptyEnv (.incidence 5 7 9 2 : ScoreProgram 0)).value
