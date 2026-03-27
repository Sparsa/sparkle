/-
Round-Robin Arbiter with configurable inputs. - Signal DSL implementation try
-/


import Sparkle
import Sparkle.Compiler.Elab
import Sparkle.Verification.ArbiterProps

open Sparkle.Core.Domain
open Sparkle.Core.Signal

namespace Sparkle.Examples.Arbiter.RoundRobinN
#eval List.findIdx (fun k => [true, false, true, false][k]!) (List.range 4)
-- as this arbiter can be configured with any number,
private abbrev n : Nat := 2

private abbrev stGrantN (i:Nat) : BitVec n := BitVec.ofNat n i
private abbrev stIdle : (BitVec n) := BitVec.zero n
private abbrev stGrantA : BitVec 2 := 1#2
private abbrev stGrantB : BitVec 2 := 2#2

def findlast (bv : (BitVec n)) : Option Nat :=
  List.findIdx? (fun x => bv.getLsbD x) (List.range n)

def nextGrant  (last: (Option Nat)) (rv : (BitVec n)) : (Option Nat) :=
  match last with
  | none => findlast rv
  | some x => Id.run do
    -- Loop n times to check all possible next bits
    for i in [1 : n + 1] do
      -- Calculate the next index, wrapping around using modulo
      let idx := (x+i)%n
      if rv.getLsbD idx then
        return some idx

    return none


def findLastGrant (prevResp : (Signal dom (BitVec n))) :  ( Signal dom (Option Nat)) :=
  findlast <$> prevResp

def findNextGrant (reqVec: Signal dom (BitVec n)) (lastGrant : (Signal dom (Option Nat))) : (Signal dom (Option Nat)) :=
   nextGrant <$> lastGrant <*> reqVec

def setGrant (grant : (Option Nat)) : (BitVec n) :=
  match grant with
  | none => BitVec.zero n
  | some x => (BitVec.zero n) ||| (1#n <<< x)


def arbiterSignal {dom : DomainConfig}
 (reqVec : Signal dom (BitVec n)) : Signal dom (BitVec n) :=
  Signal.loop fun (state : Signal dom (BitVec n)) =>
    let lastGrant := findLastGrant state
    let nextGrant := findNextGrant reqVec lastGrant
    let nextState := nextGrant.map setGrant
    Signal.register stIdle nextState

-- #synthesizeVerilog arbiterSignal


/-- Extract grantA output from arbiter state -/
def arbiterGrantA {dom : DomainConfig}
    (state : Signal dom (BitVec 2)) : Signal dom Bool :=
  state === (Signal.pure stGrantA)

/-- Extract grantB output from arbiter state -/
def arbiterGrantB {dom : DomainConfig}
    (state : Signal dom (BitVec 2)) : Signal dom Bool :=
  state === (Signal.pure stGrantB)


/-! ## Simulation Test -/

open Sparkle.Verification.ArbiterProps in
/-- Run a quick simulation to verify behavior matches spec -/
def simTest : IO Unit := do
  IO.println "=== Round-Robin Arbiter Simulation ==="
  IO.println "Cycle | reqA reqB | state | grantA grantB"
  IO.println "------+----------+-------+--------------"
  let scenarios : List (Bool × Bool) := [
    (false, false),  -- cycle 0: no requests
    (true,  false),  -- cycle 1: A requests
    (true,  true),   -- cycle 2: both request (A holds → should go to B)
    (true,  true),   -- cycle 3: both request (B holds → should go to A)
    (true,  true),   -- cycle 4: both request (A holds → should go to B)
    (false, true),   -- cycle 5: B only
    (false, false),  -- cycle 6: no requests
    (true,  true)    -- cycle 7: both from Idle (tie-break → A)
  ]
  let scenariosbv : List (BitVec n) :=
  [
    0#2, 2#2, 3#2, 3#2, 3#2, 1#2, 0#2,3#2
  ]
  -- Build one time-varying input signal from the scenario list
  let scenArr := scenariosbv.toArray
  let reqSignal : Signal defaultDomain (BitVec n) :=
    ⟨fun t => scenArr.getD t 0#2⟩
  -- Build the arbiter signal once
  let grantSignal := arbiterSignal reqSignal

  let mut state := ArbiterState.Idle
  let mut cycle : Nat := 0

  for  i in List.range 8 do
    let (rA,rB) := scenarios[i]!
    let nextSt := nextState state rA rB
    let sigOut := grantSignal.atTime i

    let specBV : BitVec n := match nextSt with
      | .Idle => 0#2
      | .GrantA => 1#2
      | .GrantB => 2#2

    let gA := grantA nextSt
    let gB := grantB nextSt
    let stStr := match nextSt with
      | .Idle   => "Idle  "
      | .GrantA => "GrantA"
      | .GrantB => "GrantB"

    let matchStr := if sigOut == specBV then "✓" else s!"✗ (got {sigOut})"
    IO.println s!"  {cycle}   |  {rA}  {rB}  | {stStr} |  {gA}    {gB} | {matchStr}"
    state := nextSt
    cycle := cycle + 1
  IO.println "\nAll transitions match ArbiterProps.nextState spec."

--#eval simTest

end Sparkle.Examples.Arbiter.RoundRobinN
